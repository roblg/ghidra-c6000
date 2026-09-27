/* ###
 * Copyright 2026 ghidra-c6000 contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package c6000;

import java.math.BigInteger;
import java.util.*;

import ghidra.app.util.importer.MessageLog;
import ghidra.program.database.function.OverlappingFunctionException;
import ghidra.program.disassemble.Disassembler;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressRange;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.lang.InstructionPrototype;
import ghidra.program.model.lang.ProcessorContextImpl;
import ghidra.program.model.lang.Register;
import ghidra.program.model.lang.RegisterValue;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.MemBuffer;
import ghidra.program.model.mem.MemoryAccessException;
import ghidra.program.model.mem.MemoryBufferImpl;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.FlowType;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceManager;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Makes lifted p-code respect C6000 execute-packet and delay-slot timing.
 *
 * <p>Ghidra lifts one instruction at a time, in address order. On C6000 all
 * members of an execute packet read the registers as they were before the
 * packet, and multi-cycle instructions (loads, multiplies, floating point)
 * write their destination only after their delay slots. Compiled code relies
 * on both, e.g. {@code SHR B16,31,B5 || MPY B5,B24,B24} multiplies the old B5,
 * and {@code LDW *A3,A3} followed by {@code AND 1,A3,A0} tests the old pointer.
 *
 * <p>The SLEIGH wrapper in {@code c6000_packet.sinc} can park a write in a
 * shadow register and commit it later. This class finds the hazards and sets
 * the context bits that switch the wrapper on, only where a hazard exists:
 * <ul>
 * <li>{@code eps<R>}: this member's write to R is parked until the end of its
 *     packet, because a later member of the same packet reads R;</li>
 * <li>{@code epd<R>}: this member's delayed write to R is parked until the
 *     packet in which it lands, because something reads or writes R before
 *     then;</li>
 * <li>{@code epc<R>}/{@code epe<R>}: commit on the last member of the
 *     packet;</li>
 * <li>{@code ep_cpre}: commit before the last member, when it is a branch.</li>
 * </ul>
 *
 * <p>A branch takes effect after five delay cycles, and the packets issued in
 * them run on both paths. Where those cycles hold real work (or a delayed
 * write lands in them), the branch gets {@code ep_br} and {@code ep_ds}: the
 * variant generated in {@code c6000_branch.sinc} captures its condition and
 * register target, inlines the window as SLEIGH delay slots and then
 * branches. The branch and its window are redecoded together. The delay
 * slots of an unconditional jump, which Ghidra never decodes, are decoded
 * first so the window can be examined.
 *
 * <p>Hazards the model cannot express (branches inside a delay window, entry
 * points inside a window, two in-flight writes of one register, software
 * pipelined loop bodies) are left as they were and marked with a warning
 * bookmark in category {@value #BOOKMARK}.
 */
public final class C6000ParallelSemantics {

	public static final String BOOKMARK = "C6000 packet semantics";
	/** Set the DEBUG environment variable to log windows, skips and redecodes. */
	private static final boolean DEBUG = System.getenv("DEBUG") != null;

	private static final String[] BANKS = { "eps", "epd", "epc", "epe" };
	private static final int EPS = 0, EPD = 1, EPC = 2, EPE = 3;

	/** Totals from one run. */
	public static final class Result {
		public int packetHazards, delayHazards, branches, skipped, redecoded;

		@Override
		public String toString() {
			return String.format("packet=%d delay=%d branches=%d skipped=%d redecoded=%d",
				packetHazards, delayHazards, branches, skipped, redecoded);
		}
	}

	private final Program program;
	private final TaskMonitor monitor;
	private final Register contextReg;
	private final Register cpre;
	private final Register any;
	private final Register epBr;
	private final Register epDs;
	private final Register is16;
	private final Register[][] fields = new Register[4][64];
	private final Result result = new Result();

	private C6000ParallelSemantics(Program program, TaskMonitor monitor) {
		this.program = program;
		this.monitor = monitor;
		this.contextReg = program.getProgramContext().getBaseContextRegister();
		this.cpre = program.getRegister("ep_cpre");
		this.any = program.getRegister("ep_any");
		this.epBr = program.getRegister("ep_br");
		this.epDs = program.getRegister("ep_ds");
		this.is16 = program.getRegister("c_is16");
		for (int b = 0; b < 4; b++) {
			for (int r = 0; r < 64; r++) {
				fields[b][r] = program.getRegister(BANKS[b] + regName(r));
			}
		}
	}

	/** True if this program's language carries the packet-semantics fields. */
	public static boolean supported(Program program) {
		return C6000PacketContext.isC6000(program) && program.getRegister("ep_any") != null;
	}

	/** Analyze and fix every function that intersects {@code scope}. */
	public static Result apply(Program program, AddressSetView scope, TaskMonitor monitor,
			MessageLog log) throws CancelledException {
		C6000ParallelSemantics worker = new C6000ParallelSemantics(program, monitor);
		Set<Function> functions = new LinkedHashSet<>();
		FunctionManager fm = program.getFunctionManager();
		Iterator<Function> overlapping = fm.getFunctionsOverlapping(scope);
		while (overlapping.hasNext()) {
			functions.add(overlapping.next());
		}
		for (Function f : functions) {
			monitor.checkCancelled();
			worker.function(f, log);
		}
		return worker.result;
	}

	// ------------------------------------------------------------------
	// Register effects

	static String regName(int index) {
		return (index < 32 ? "A" : "B") + (index % 32);
	}

	private static int regIndex(String name) {
		if (name == null || name.length() < 2) return -1;
		char bank = name.charAt(0);
		if (bank != 'A' && bank != 'B') return -1;
		for (int i = 1; i < name.length(); i++) {
			if (!Character.isDigit(name.charAt(i))) return -1;
		}
		int n = Integer.parseInt(name.substring(1));
		if (n > 31) return -1;
		return (bank == 'A' ? 0 : 32) + n;
	}

	/** Delay slots before the destination write lands (SPRUFE8B, C674x). */
	public static int delaySlots(String mnemonic) {
		String m = baseMnemonic(mnemonic);
		if (m.startsWith("LD") && !m.equals("LDMVK")) return 4;
		switch (m) {
			case "MPYDP": case "MPYID": return 9;
			case "MPYI": return 8;
			case "ADDDP": case "SUBDP": case "MPYSPDP": return 6;
			case "MPYSP2DP": case "INTDP": case "INTDPU": return 4;
			case "SPDP": case "CMPEQDP": case "CMPGTDP": case "CMPLTDP": return 1;
			default:
		}
		if (m.startsWith("MPY32") || m.startsWith("DOTP") || m.startsWith("DDOTP") ||
			m.equals("MPY2") || m.equals("MPY2IR") || m.equals("SMPY2") ||
			m.startsWith("MPYHI") || m.startsWith("MPYLI") || m.startsWith("MPYIH") ||
			m.startsWith("MPYIL") || m.startsWith("MPYU4") || m.startsWith("MPYSU4") ||
			m.startsWith("MPYUS4") || m.startsWith("GMPY") || m.startsWith("CMPY") ||
			m.equals("XORMPY") || m.equals("SMPY32") || m.equals("MPYSP") ||
			m.equals("ADDSP") || m.equals("SUBSP") || m.equals("INTSP") ||
			m.equals("INTSPU") || m.equals("SPINT") || m.equals("SPTRUNC") ||
			m.equals("DPSP") || m.equals("DPINT") || m.equals("DPTRUNC") ||
			m.equals("ADDSUB") || m.equals("ADDSUB2") || m.equals("SADDSUB") ||
			m.equals("SADDSUB2") || m.equals("DPACK2")) {
			return 3;
		}
		if (m.startsWith("MPY") || m.startsWith("SMPY")) return 1;
		return 0;
	}

	/** {@code [!A0]LDW.D1} -> {@code LDW}; Ghidra marks delay slots with {@code _}. */
	public static String baseMnemonic(String mnemonic) {
		String m = mnemonic.toUpperCase(Locale.ROOT);
		if (m.startsWith("_")) m = m.substring(1);
		if (m.startsWith("[")) {
			int close = m.indexOf(']');
			if (close >= 0) m = m.substring(close + 1);
		}
		int dot = m.indexOf('.');
		return dot >= 0 ? m.substring(0, dot) : m;
	}

	private static boolean isShadow(Register r) {
		if (r == null) return false;
		String n = r.getName();
		return n.endsWith("_sv") || n.endsWith("_pk") || n.endsWith("_dl");
	}

	private final class Effects {
		final Instruction insn;
		final BitSet reads = new BitSet(64);
		final BitSet writes = new BitSet(64);
		final BitSet delayed = new BitSet(64);
		final int delay;
		final boolean flow;
		final boolean compactBranch;
		/** B, BNOP, BDEC or BPOS: its delay slots may be inlined. */
		final boolean branch;

		Effects(Instruction insn) {
			this.insn = insn;
			String base = baseMnemonic(insn.getMnemonicString());
			if (flag(insn, epBr)) {
				// Its p-code now carries the delay slots; read the operands instead.
				operandEffects(base);
			}
			else {
				BitSet written = new BitSet(64);
				for (PcodeOp op : insn.getPcode()) {
					if (touchesShadow(op)) continue; // wrapper copies from a previous run
					for (Varnode in : op.getInputs()) {
						units(in, bit -> { if (!written.get(bit)) reads.set(bit); });
					}
					units(op.getOutput(), bit -> { written.set(bit); writes.set(bit); });
				}
			}
			delay = delaySlots(insn.getMnemonicString());
			if (delay > 0 && insn.getNumOperands() > 0) {
				// Only the destination lands late; *A4++ base updates do not.
				for (Object o : insn.getOpObjects(insn.getNumOperands() - 1)) {
					if (o instanceof Register r) {
						for (int bit : gprUnits(r)) {
							if (writes.get(bit)) delayed.set(bit);
						}
					}
				}
			}
			FlowType ft = insn.getFlowType();
			flow = ft.isJump() || ft.isCall() || ft.isTerminal() || ft.isComputed();
			Register pf = program.getRegister("c_pfollow");
			RegisterValue v = pf == null ? null : insn.getRegisterValue(pf);
			compactBranch = insn.getLength() == 2 && flow && v != null &&
				v.hasValue() && v.getUnsignedValue().signum() != 0;
			branch = flow && epBr != null && (base.equals("B") || base.equals("BNOP") ||
				base.equals("BDEC") || base.equals("BPOS"));
		}

		/** Predicate and register operands are read; BDEC also writes its counter. */
		private void operandEffects(String base) {
			String m = insn.getMnemonicString().replaceFirst("^_", "");
			if (m.startsWith("[") && m.indexOf(']') > 0) {
				int p = regIndex(m.substring(1, m.indexOf(']')).replace("!", ""));
				if (p >= 0) reads.set(p);
			}
			for (int op = 0; op < insn.getNumOperands(); op++) {
				for (Object o : insn.getOpObjects(op)) {
					if (!(o instanceof Register r)) continue;
					for (int u : gprUnits(r)) {
						reads.set(u);
						if (op == 1 && base.equals("BDEC")) writes.set(u);
					}
				}
			}
		}

		BitSet immediateWrites() {
			BitSet b = (BitSet) writes.clone();
			b.andNot(delayed);
			return b;
		}
	}

	private static boolean flag(Instruction insn, Register field) {
		if (field == null) return false;
		RegisterValue v = insn.getRegisterValue(field);
		return v != null && v.hasValue() && v.getUnsignedValue().testBit(0);
	}

	private boolean touchesShadow(PcodeOp op) {
		if (op.getOutput() != null && isShadow(register(op.getOutput()))) return true;
		for (Varnode in : op.getInputs()) {
			if (isShadow(register(in))) return true;
		}
		return false;
	}

	private Register register(Varnode v) {
		if (v == null || !v.isRegister()) return null;
		return program.getRegister(v.getAddress(), v.getSize());
	}

	private void units(Varnode v, java.util.function.IntConsumer sink) {
		if (v == null || !v.isRegister()) return;
		for (int off = 0; off < v.getSize(); off += 4) {
			Register r = program.getRegister(v.getAddress().add(off), 4);
			int idx = r == null ? -1 : regIndex(r.getName());
			if (idx >= 0) sink.accept(idx);
		}
	}

	private List<Integer> gprUnits(Register r) {
		List<Integer> out = new ArrayList<>();
		int idx = regIndex(r.getName());
		if (idx >= 0) {
			out.add(idx);
			return out;
		}
		for (int off = 0; off < r.getMinimumByteSize(); off += 4) {
			Register c = program.getRegister(r.getAddress().add(off), 4);
			int i = c == null ? -1 : regIndex(c.getName());
			if (i >= 0) out.add(i);
		}
		return out;
	}

	// ------------------------------------------------------------------
	// Packets

	private static final class Packet {
		final List<Effects> members = new ArrayList<>();
		int cycle;       // first cycle
		int cycles = 1;  // cycles occupied (NOP n / BNOP n)
		boolean inLoop;  // SPLOOP body: timing belongs to the loop buffer

		Effects last() {
			return members.get(members.size() - 1);
		}

		boolean covers(int c) {
			return c >= cycle && c < cycle + cycles;
		}
	}

	private boolean parallelWithNext(Instruction insn) throws MemoryAccessException {
		Address a = insn.getMinAddress();
		if (insn.getLength() == 4) {
			return (program.getMemory().getInt(a) & 1) != 0;
		}
		long base = a.getOffset() & ~31L;
		int header = program.getMemory().getInt(a.getNewAddress(base + 28));
		if ((header >>> 28) != 0xE) throw new MemoryAccessException("no compact header at " + a);
		return ((header >>> ((a.getOffset() - base) / 2)) & 1) != 0;
	}

	private static boolean isHeader(Instruction insn) {
		return baseMnemonic(insn.getMnemonicString()).equals("CPKT");
	}

	/**
	 * Cycles an execute packet member makes the packet occupy: {@code NOP n}
	 * takes n cycles, {@code BNOP src,n} and {@code ADDKPC} add n after their
	 * own, {@code CALLP} adds five, and a load in a PROT=1 compact fetch
	 * packet adds four (SPRUFE8B 3.10.2).
	 */
	private int nopCycles(Instruction insn) {
		String m = baseMnemonic(insn.getMnemonicString());
		if (m.equals("CALLP")) return 6;
		if (m.startsWith("LD") && isProtected(insn)) return 5;
		int operand, self;
		if (m.equals("NOP")) { operand = 0; self = 0; }       // NOP n: n cycles
		else if (m.equals("BNOP")) { operand = 1; self = 1; } // B; NOP N == BNOP N
		else if (m.equals("ADDKPC")) { operand = 2; self = 1; }
		else return 1;
		if (insn.getNumOperands() <= operand) return 1;
		for (Object o : insn.getOpObjects(operand)) {
			if (o instanceof Scalar s) return (int) Math.max(1, s.getUnsignedValue() + self);
		}
		String text = insn.getDefaultOperandRepresentation(operand);
		if (text != null && text.matches("[0-9]")) {
			return Math.max(1, Integer.parseInt(text) + self);
		}
		return 1;
	}


	private boolean isProtected(Instruction insn) {
		Register prot = program.getRegister("c_prot");
		if (prot == null) return false;
		BigInteger v = program.getProgramContext().getValue(prot, insn.getMinAddress(), false);
		return v != null && v.testBit(0);
	}

	/** Contiguous runs of packets, in address order, within a function body. */
	private List<List<Packet>> runs(AddressSetView body) {
		List<List<Packet>> runs = new ArrayList<>();
		List<Packet> run = new ArrayList<>();
		Packet packet = null;
		Address expected = null;
		int cycle = 0;
		boolean inLoop = false;
		InstructionIterator it = program.getListing().getInstructions(body, true);
		while (it.hasNext()) {
			Instruction insn = it.next();
			if (isHeader(insn)) {
				expected = insn.getMaxAddress().add(1);
				continue;
			}
			if (expected != null && !insn.getMinAddress().equals(expected)) {
				if (packet != null) run.add(packet);
				if (!run.isEmpty()) runs.add(run);
				run = new ArrayList<>();
				packet = null;
				cycle = 0;
			}
			if (packet == null) {
				packet = new Packet();
				packet.cycle = cycle;
			}
			Effects e = new Effects(insn);
			packet.members.add(e);
			packet.cycles = Math.max(packet.cycles, nopCycles(insn));
			String m = baseMnemonic(insn.getMnemonicString());
			if (m.startsWith("SPLOOP")) inLoop = true;
			packet.inLoop |= inLoop;
			if (m.startsWith("SPKERNEL")) inLoop = false;
			expected = insn.getMaxAddress().add(1);
			boolean more;
			try {
				more = parallelWithNext(insn);
			}
			catch (MemoryAccessException ex) {
				more = false;
			}
			if (!more) {
				run.add(packet);
				cycle = packet.cycle + packet.cycles;
				packet = null;
			}
		}
		if (packet != null) run.add(packet);
		if (!run.isEmpty()) runs.add(run);
		return runs;
	}

	// ------------------------------------------------------------------
	// Hazard detection

	/** Wanted masks per instruction address: 4 banks + cpre. */
	private final class Want {
		final BitSet[] bank = { new BitSet(64), new BitSet(64), new BitSet(64), new BitSet(64) };
		boolean cpre;
		int ds; // ep_ds: delay-slot window in halfwords; nonzero sets ep_br

		boolean any() {
			return cpre || !bank[EPS].isEmpty() || !bank[EPD].isEmpty() ||
				!bank[EPC].isEmpty() || !bank[EPE].isEmpty();
		}
	}

	/** A branch whose delay slots are inlined into its p-code. */
	private static final class Window {
		final Effects branch;
		final int packet;  // index in the run of the branch's packet
		final int member;  // index of the branch in that packet
		int last;          // index of the last packet of the window
		Address end;       // last byte of the window

		Window(Effects branch, int packet, int member) {
			this.branch = branch;
			this.packet = packet;
			this.member = member;
		}

		/** Does the window contain member {@code m} of packet {@code k}? */
		boolean contains(int k, int m) {
			return (k > packet || (k == packet && m > member)) && k <= last;
		}
	}

	/** Branches whose delay slots are inlined, for the function being fixed. */
	private final Map<Effects, Window> slotted = new HashMap<>();

	private void function(Function f, MessageLog log) throws CancelledException {
		Map<Address, Want> wants = new HashMap<>();
		List<Instruction> all = new ArrayList<>();
		slotted.clear();
		if (DEBUG) ghidra.util.Msg.info(this, "C6000 packet semantics: function " + f.getEntryPoint());
		AddressSet body = new AddressSet(f.getBody());
		Map<Address, AddressSet> decoded = decodeJumpSlots(f, body);
		// Delay slots of branches slotted earlier need not be in the body.
		for (Instruction insn : program.getListing().getInstructions(f.getBody(), true)) {
			int ds = dsOf(program.getProgramContext().getRegisterValue(contextReg,
				insn.getMinAddress()));
			if (ds > 0) body.add(insn.getMaxAddress().next(), insn.getMaxAddress().add(2L * ds));
		}
		List<Window> windows = new ArrayList<>();
		for (List<Packet> run : runs(body)) {
			for (Packet p : run) {
				for (Effects e : p.members) {
					all.add(e.insn);
				}
			}
			List<Window> mine = windows(run);
			windows.addAll(mine);
			for (int i = 0; i < run.size(); i++) {
				monitor.checkCancelled();
				packetHazards(run.get(i), wants);
				delayHazards(run, i, wants, mine);
			}
		}
		for (Window w : windows) {
			want(wants, w.branch).ds =
				(int) (w.end.subtract(w.branch.insn.getMaxAddress()) / 2);
			result.branches++;
		}
		// Undo slot decoding the model did not use.
		for (Map.Entry<Address, AddressSet> e : decoded.entrySet()) {
			Instruction b = program.getListing().getInstructionAt(e.getKey());
			if (b == null || !slotted.containsKey(effectsOf(b, windows))) {
				for (AddressRange r : e.getValue().getAddressRanges()) {
					program.getListing().clearCodeUnits(r.getMinAddress(), r.getMaxAddress(),
						false);
				}
				all.removeIf(i -> e.getValue().contains(i.getMinAddress()));
			}
		}
		for (Instruction insn : all) {
			Want w = wants.get(insn.getMinAddress());
			if (w != null && w.cpre && (!w.bank[EPS].isEmpty() || !w.bank[EPD].isEmpty())) {
				// Unreachable by construction: only a packet's last member gets
				// ep_cpre, a last member never parks for its own packet, and a
				// branch is never a delayed writer.
				log.appendMsg("C6000 Packet Semantics",
					"internal: branch with park bits at " + insn.getMinAddress());
			}
		}
		commit(all, wants, log);
		// Add inlined delay slots Ghidra had not followed (those of unconditional
		// jumps). Recomputing the body from flow instead would drop code other
		// analyses attached to it.
		AddressSet grow = new AddressSet();
		for (Window w : windows) {
			if (w.end.compareTo(w.branch.insn.getMaxAddress()) > 0) {
				grow.add(w.branch.insn.getMaxAddress().next(), w.end);
			}
		}
		if (!f.getBody().contains(grow)) {
			try {
				f.setBody(f.getBody().union(grow));
			}
			catch (OverlappingFunctionException e) {
				log.appendMsg("C6000 Packet Semantics",
					"delay slots of " + f.getName() + " overlap another function");
			}
		}
	}

	private static Effects effectsOf(Instruction b, List<Window> windows) {
		for (Window w : windows) {
			if (w.branch.insn.getMinAddress().equals(b.getMinAddress())) return w.branch;
		}
		return null;
	}

	// ------------------------------------------------------------------
	// Branch delay slots

	private static final int BRANCH_DELAY = 5;
	private static final int MAX_WINDOW_BYTES = 254; // ep_ds is seven bits of halfwords

	/**
	 * Ghidra stops following at an unconditional jump, so its delay slots are
	 * missing from the function body and often not decoded at all. Add them to
	 * {@code body}, decoding one instruction at a time and no further than five
	 * cycles, so the window can be examined.
	 *
	 * @return the instructions decoded here, per jump, so unused ones can be removed
	 */
	private Map<Address, AddressSet> decodeJumpSlots(Function f, AddressSet body)
			throws CancelledException {
		Map<Address, AddressSet> out = new HashMap<>();
		if (epBr == null) return out;
		Listing listing = program.getListing();
		List<Instruction> jumps = new ArrayList<>();
		InstructionIterator it = listing.getInstructions(f.getBody(), true);
		while (it.hasNext()) {
			Instruction insn = it.next();
			String m = baseMnemonic(insn.getMnemonicString());
			if ((m.equals("B") || m.equals("BNOP") || m.equals("BDEC") || m.equals("BPOS")) &&
				!f.getBody().contains(insn.getMaxAddress().next())) {
				jumps.add(insn);
			}
		}
		Disassembler dis = Disassembler.getDisassembler(program, monitor, null);
		for (Instruction jump : jumps) {
			monitor.checkCancelled();
			AddressSet got = new AddressSet();
			try {
				int cycle = 0;
				int packetCycles = nopCycles(jump);
				boolean more = parallelWithNext(jump);
				Address a = jump.getMaxAddress().next();
				while (true) {
					if (!more) {
						cycle += packetCycles;
						packetCycles = 1;
						if (cycle > BRANCH_DELAY) break;
					}
					Instruction x = listing.getInstructionAt(a);
					if (x == null) {
						if (listing.getDefinedDataContaining(a) != null ||
							listing.getInstructionContaining(a) != null) {
							break;
						}
						int len = compactSlot(a) ? 2 : 4;
						dis.disassemble(a, new AddressSet(a, a.add(len - 1)), false);
						x = listing.getInstructionAt(a);
						if (x == null) break;
						got.add(x.getMinAddress(), x.getMaxAddress());
					}
					body.add(x.getMinAddress(), x.getMaxAddress());
					a = x.getMaxAddress().next();
					if (isHeader(x)) continue;
					packetCycles = Math.max(packetCycles, nopCycles(x));
					more = parallelWithNext(x);
				}
			}
			catch (MemoryAccessException | ghidra.program.model.address.AddressOutOfBoundsException e) {
				// Leave what was decoded; the window check will find it incomplete.
			}
			if (!got.isEmpty()) out.put(jump.getMinAddress(), got);
		}
		return out;
	}

	private boolean compactSlot(Address a) {
		if (is16 == null) return false;
		BigInteger v = program.getProgramContext().getValue(is16, a, false);
		return v != null && v.testBit(0);
	}

	/** Choose the branches of one run whose delay slots get inlined. */
	private List<Window> windows(List<Packet> run) {
		List<Window> out = new ArrayList<>();
		for (int pi = 0; pi < run.size(); pi++) {
			Packet p = run.get(pi);
			for (int mi = 0; mi < p.members.size(); mi++) {
				Effects e = p.members.get(mi);
				if (!e.branch || undecided(e.insn)) continue;
				Window w = new Window(e, pi, mi);
				List<Effects> slots = new ArrayList<>(p.members.subList(mi + 1, p.members.size()));
				int horizon = p.cycle + BRANCH_DELAY;
				boolean complete = p.covers(horizon);
				w.last = pi;
				for (int k = pi + 1; k < run.size() && !complete; k++) {
					Packet q = run.get(k);
					slots.addAll(q.members);
					w.last = k;
					complete = q.cycle + q.cycles > horizon;
				}
				if (slots.isEmpty() && complete) continue; // BNOP 5: the window is its own NOPs
				boolean work = slots.isEmpty();
				for (Effects s : slots) {
					work |= !baseMnemonic(s.insn.getMnemonicString()).equals("NOP");
				}
				if (!work && !delayedWriteInFlight(run, pi, mi)) continue;
				String why = null;
				if (!complete) why = "branch delay slots are not all decoded";
				for (int k = pi; k <= w.last && why == null; k++) {
					if (run.get(k).inLoop) why = "branch delay slots in a software-pipelined loop";
				}
				ReferenceManager refs = program.getReferenceManager();
				for (Effects s : slots) {
					if (why != null) break;
					if (s.flow || s.compactBranch) why = "branch in another branch's delay slots";
					else if (hasFlowInto(refs, s.insn.getMinAddress())) {
						why = "jump into a branch's delay slots";
					}
					else if (e.writes.intersects(s.reads) || e.writes.intersects(s.writes)) {
						if (p.members.contains(s)) why = "branch writes a register its packet uses";
					}
				}
				w.end = slots.isEmpty() ? e.insn.getMaxAddress() :
					slots.get(slots.size() - 1).insn.getMaxAddress();
				if (DEBUG) {
					StringBuilder sb = new StringBuilder();
					for (Effects x : slots) sb.append(" | ").append(x.insn.getMinAddress())
						.append(' ').append(x.insn);
					ghidra.util.Msg.info(this, "C6000 packet semantics: window " +
						e.insn.getMinAddress() + " c=" + p.cycle + "+" + p.cycles + sb);
				}
				if (why == null && w.end.subtract(e.insn.getMaxAddress()) > MAX_WINDOW_BYTES) {
					why = "branch delay slots too long to inline";
				}
				if (why == null && !slotWidthsAgree(e.insn, w.end)) {
					why = "branch delay slots mix 16- and 32-bit instructions";
				}
				if (why != null) {
					skip(e, why);
					continue;
				}
				out.add(w);
				slotted.put(e, w);
			}
		}
		return out;
	}

	/**
	 * An unpredicated register branch that no analyzer has classified yet
	 * (still {@code c_branch_terminal=0}, no flow override) is left for the
	 * register-branch analyzer; it is revisited once that decides.
	 */
	private boolean undecided(Instruction insn) {
		Register terminal = program.getRegister("c_branch_terminal");
		if (terminal == null || insn.getFlowOverride() != FlowOverride.NONE) return false;
		if (insn.getMnemonicString().replaceFirst("^_", "").startsWith("[")) return false;
		if (insn.getNumOperands() == 0 || insn.getRegister(0) == null) return false;
		return !flag(insn, terminal);
	}

	/**
	 * Ghidra finds a branch's delay-slot instructions (for fall-through and
	 * function bodies) by parsing them with the branch's own context, so every
	 * slot must decode to the same length under it.
	 */
	private boolean slotWidthsAgree(Instruction branch, Address end) {
		RegisterValue value =
			program.getProgramContext().getRegisterValue(contextReg, branch.getMinAddress());
		ProcessorContextImpl context = new ProcessorContextImpl(program.getLanguage());
		if (value != null) context.setRegisterValue(value);
		Address a = branch.getMaxAddress().next();
		try {
			while (a.compareTo(end) <= 0) {
				Instruction actual = program.getListing().getInstructionAt(a);
				if (actual == null) return false;
				InstructionPrototype proto = program.getLanguage()
						.parse(new MemoryBufferImpl(program.getMemory(), a), context, true);
				if (proto.getLength() != actual.getLength()) return false;
				a = actual.getMaxAddress().next();
			}
		}
		catch (Exception e) {
			return false;
		}
		return true;
	}

	/** Is a multi-cycle result still in flight when this branch issues? */
	private static boolean delayedWriteInFlight(List<Packet> run, int pi, int mi) {
		int issue = run.get(pi).cycle;
		for (int k = pi; k >= 0; k--) {
			Packet q = run.get(k);
			if (q.cycle + 10 < issue) break;
			for (int j = 0; j < q.members.size() && (k < pi || j < mi); j++) {
				Effects e = q.members.get(j);
				if (!e.delayed.isEmpty() && q.cycle + e.delay >= issue) return true;
			}
		}
		return false;
	}

	private Want want(Map<Address, Want> wants, Effects e) {
		return wants.computeIfAbsent(e.insn.getMinAddress(), a -> new Want());
	}

	private void skip(Effects at, String why) {
		result.skipped++;
		if (DEBUG) {
			ghidra.util.Msg.info(this, "C6000 packet semantics: skip " +
				at.insn.getMinAddress() + " " + why);
		}
		program.getBookmarkManager().setBookmark(at.insn.getMinAddress(),
			ghidra.program.model.listing.BookmarkType.WARNING, BOOKMARK, why);
	}

	private void packetHazards(Packet p, Map<Address, Want> wants) {
		int n = p.members.size();
		if (n < 2) return;
		BitSet commit = new BitSet(64);
		List<int[]> stashes = new ArrayList<>(); // member index, register
		for (int i = 0; i < n; i++) {
			BitSet mine = p.members.get(i).immediateWrites();
			for (int r = mine.nextSetBit(0); r >= 0; r = mine.nextSetBit(r + 1)) {
				for (int j = i + 1; j < n; j++) {
					if (p.members.get(j).reads.get(r)) {
						stashes.add(new int[] { i, r });
						commit.set(r);
						break;
					}
				}
			}
		}
		if (stashes.isEmpty()) return;
		Effects last = p.last();
		String why = null;
		if (p.inLoop) {
			why = "packet hazard inside a software-pipelined loop";
		}
		for (int i = 0; i < n - 1 && why == null; i++) {
			Effects m = p.members.get(i);
			// A branch lifted with its delay slots reads at issue and jumps
			// after the whole window, so later members are no obstacle.
			if ((m.flow || m.compactBranch) && !slotted.containsKey(m)) {
				why = "packet hazard with a branch that is not the last member";
			}
		}
		for (int[] s : stashes) {
			for (int j = 0; j < n && why == null; j++) {
				if (j != s[0] && p.members.get(j).writes.get(s[1])) {
					why = "two members of one packet write " + regName(s[1]);
				}
			}
		}
		if (why == null && last.flow) {
			if (last.compactBranch && !slotted.containsKey(last)) {
				why = "compact branch carries its followers' p-code";
			}
			BitSet clash = (BitSet) last.reads.clone();
			clash.and(commit);
			if (why == null && !clash.isEmpty()) {
				why = "packet's branch reads a register written in the same packet";
			}
		}
		if (why != null) {
			skip(p.members.get(0), why);
			return;
		}
		for (int[] s : stashes) {
			want(wants, p.members.get(s[0])).bank[EPS].set(s[1]);
			result.packetHazards++;
		}
		Want lw = want(wants, last);
		lw.bank[EPC].or(commit);
		if (last.flow) lw.cpre = true;
	}

	private void delayHazards(List<Packet> run, int pi, Map<Address, Want> wants,
			List<Window> windows) {
		Packet p = run.get(pi);
		for (int wi = 0; wi < p.members.size(); wi++) {
			Effects w = p.members.get(wi);
			if (w.delayed.isEmpty()) continue;
			int lands = p.cycle + w.delay;
			for (int r = w.delayed.nextSetBit(0); r >= 0; r = w.delayed.nextSetBit(r + 1)) {
				// Is the old value observed (or overwritten) before the result lands?
				boolean hazard = false;
				for (int j = wi + 1; j < p.members.size() && !hazard; j++) {
					Effects e = p.members.get(j);
					hazard = e.reads.get(r) || e.writes.get(r);
				}
				int qi = p.covers(lands) ? pi : -1; // protected load: lands in its own packet
				for (int k = pi + 1; k < run.size() && qi < 0; k++) {
					Packet q = run.get(k);
					if (q.cycle > lands) break;
					for (Effects e : q.members) {
						hazard |= e.reads.get(r) || e.writes.get(r);
					}
					if (q.covers(lands)) {
						qi = k;
						break;
					}
				}
				if (!hazard) continue;
				String why = delayProblem(run, pi, wi, qi, r, windows);
				if (why != null) {
					skip(w, why);
					continue;
				}
				Packet q = run.get(qi);
				want(wants, w).bank[EPD].set(r);
				Want lw = want(wants, q.last());
				lw.bank[EPE].set(r);
				if (q.last().flow) lw.cpre = true;
				result.delayHazards++;
			}
		}
	}

	private String delayProblem(List<Packet> run, int pi, int wi, int qi, int r,
			List<Window> windows) {
		Packet p = run.get(pi);
		if (qi < 0) return "delayed write lands after the end of straight-line code";
		if (p.inLoop) return "delayed write inside a software-pipelined loop";
		for (Window bw : windows) {
			// Issued in a branch's delay slots but landing after the branch:
			// the taken path would never see the parked value.
			if (bw.contains(pi, wi) && qi > bw.last) {
				return "delayed write lands after its branch takes effect";
			}
		}
		Packet q = run.get(qi);
		ReferenceManager refs = program.getReferenceManager();
		for (int k = pi; k <= qi; k++) {
			Packet x = run.get(k);
			for (int j = 0; j < x.members.size(); j++) {
				Effects e = x.members.get(j);
				boolean lastOfLanding = k == qi && j == x.members.size() - 1;
				if ((e.flow || e.compactBranch) && !lastOfLanding) {
					Window bw = slotted.get(e);
					if (bw == null) return "branch inside a delay window";
					if (bw.last < qi) return "delayed write lands after its branch takes effect";
				}
				if (k > pi && j == 0 && hasFlowInto(refs, e.insn.getMinAddress())) {
					return "entry point inside a delay window";
				}
				if (e != p.members.get(wi) && e.delayed.get(r)) {
					return "two delayed writes of " + regName(r) + " in flight";
				}
				if (k == qi && e.immediateWrites().get(r)) {
					return "write to " + regName(r) + " in the cycle its load lands";
				}
			}
		}
		Effects last = q.last();
		if (last.flow && (last.compactBranch || last.reads.get(r))) {
			return "branch reads a register whose delayed write lands with it";
		}
		return null;
	}

	private static boolean hasFlowInto(ReferenceManager refs, Address at) {
		for (Reference ref : refs.getReferencesTo(at)) {
			// A fall-through override is not an entry (the delayed-call analyzer
			// points one at the first delay slot).
			if (ref.getReferenceType().isFlow() && !ref.getReferenceType().isFallthrough()) {
				return true;
			}
		}
		return false;
	}

	// ------------------------------------------------------------------
	// Applying context

	private int dsOf(RegisterValue v) {
		if (v == null || epDs == null) return 0;
		RegisterValue sub = v.getRegisterValue(epDs);
		return sub != null && sub.hasValue() ? sub.getUnsignedValue().intValue() : 0;
	}

	private boolean differs(RegisterValue current, Want w) {
		for (int b = 0; b < 4; b++) {
			for (int r = 0; r < 64; r++) {
				boolean want = w != null && w.bank[b].get(r);
				if (bit(current, fields[b][r]) != want) return true;
			}
		}
		int ds = w == null ? 0 : w.ds;
		return bit(current, cpre) != (w != null && w.cpre) ||
			bit(current, any) != (w != null && w.any()) ||
			(epBr != null && (bit(current, epBr) != (ds != 0) || dsOf(current) != ds));
	}

	private static boolean bit(RegisterValue v, Register field) {
		if (v == null || field == null) return false;
		RegisterValue sub = v.getRegisterValue(field);
		return sub != null && sub.hasValue() && sub.getUnsignedValue().testBit(0);
	}

	private RegisterValue valueFor(RegisterValue current, Want w) {
		RegisterValue value = current == null ? new RegisterValue(contextReg) : current;
		for (int b = 0; b < 4; b++) {
			for (int r = 0; r < 64; r++) {
				boolean on = w != null && w.bank[b].get(r);
				value = value.assign(fields[b][r], on ? BigInteger.ONE : BigInteger.ZERO);
			}
		}
		value = value.assign(cpre, (w != null && w.cpre) ? BigInteger.ONE : BigInteger.ZERO);
		value = value.assign(any, (w != null && w.any()) ? BigInteger.ONE : BigInteger.ZERO);
		if (epBr != null) {
			int ds = w == null ? 0 : w.ds;
			value = value.assign(epBr, ds != 0 ? BigInteger.ONE : BigInteger.ZERO);
			value = value.assign(epDs, BigInteger.valueOf(ds));
		}
		return value;
	}

	/**
	 * Redecode every instruction whose context must change. A branch with
	 * inlined delay slots and its window (old or new) form one unit: Ghidra
	 * decodes delay-slot instructions as part of their branch.
	 *
	 * @return true if anything was redecoded
	 */
	private boolean commit(List<Instruction> all, Map<Address, Want> wants, MessageLog log)
			throws CancelledException {
		ProgramContext ctx = program.getProgramContext();
		TreeMap<Address, Address> units = new TreeMap<>();
		for (Instruction insn : all) {
			Address at = insn.getMinAddress();
			Want w = wants.get(at);
			long bytes = 2L * Math.max(w == null ? 0 : w.ds,
				dsOf(ctx.getRegisterValue(contextReg, at)));
			if (bytes > 0) {
				units.merge(at, insn.getMaxAddress().add(bytes),
					(a, b) -> a.compareTo(b) >= 0 ? a : b);
			}
		}
		boolean changed = false;
		Address covered = null;
		for (Instruction insn : all) {
			monitor.checkCancelled();
			Address at = insn.getMinAddress();
			if (covered != null && at.compareTo(covered) <= 0) continue;
			Address end = units.get(at);
			if (end == null) {
				end = insn.getMaxAddress();
			}
			else {
				covered = end;
			}
			changed |= redecode(at, end, wants, log);
		}
		return changed;
	}

	private record Saved(Reference[] refs, FlowOverride override, boolean fallOverridden,
			Address fallThrough, int length) {
	}

	private boolean redecode(Address start, Address end, Map<Address, Want> wants,
			MessageLog log) {
		ProgramContext ctx = program.getProgramContext();
		Listing listing = program.getListing();
		AddressSet range = new AddressSet(start, end);
		Map<Address, Saved> saved = new LinkedHashMap<>();
		boolean differs = false;
		for (Instruction old : listing.getInstructions(range, true)) {
			Address at = old.getMinAddress();
			RegisterValue cur = ctx.getRegisterValue(contextReg, at);
			Want wt = wants.get(at);
			if (differs(cur, wt)) {
				differs = true;
				if (DEBUG) {
					ghidra.util.Msg.info(this, "C6000 packet semantics: " + at + " " + old +
						" ds " + dsOf(cur) + "->" + (wt == null ? 0 : wt.ds) + " any " +
						bit(cur, any) + "->" + (wt != null && wt.any()) + " cpre " +
						bit(cur, cpre) + "->" + (wt != null && wt.cpre));
				}
			}
			saved.put(at, new Saved(old.getReferencesFrom(), old.getFlowOverride(),
				old.isFallThroughOverridden(),
				old.isFallThroughOverridden() ? old.getFallThrough() : null, old.getLength()));
		}
		if (!differs || !saved.containsKey(start)) return false;
		if (DEBUG) {
			ghidra.util.Msg.info(this, "C6000 packet semantics: redecode " + start + ".." + end);
		}
		listing.clearCodeUnits(start, end, false);
		for (Address at : saved.keySet()) {
			try {
				ctx.setRegisterValue(at, at, valueFor(ctx.getRegisterValue(contextReg, at),
					wants.get(at)));
			}
			catch (ContextChangeException e) {
				log.appendException(e);
			}
		}
		// Build the instructions directly from the stored context: Ghidra's flow
		// disassembler does not carry every per-address noflow bit into delay slots.
		Address slotsEnd = null;
		for (Address at : saved.keySet()) {
			boolean inSlot = slotsEnd != null && at.compareTo(slotsEnd) <= 0;
			Instruction made = create(at, inSlot, log);
			if (made != null && !inSlot && made.getPrototype().getDelaySlotByteCount() > 0) {
				slotsEnd = made.getMaxAddress().add(made.getPrototype().getDelaySlotByteCount());
			}
		}
		ReferenceManager manager = program.getReferenceManager();
		for (Map.Entry<Address, Saved> e : saved.entrySet()) {
			Address at = e.getKey();
			Saved s = e.getValue();
			Instruction fresh = listing.getInstructionAt(at);
			if (fresh == null || fresh.getLength() != s.length()) {
				log.appendMsg("C6000 Packet Semantics", "redecode changed instruction at " + at);
				continue;
			}
			if (s.override() != FlowOverride.NONE) fresh.setFlowOverride(s.override());
			// A fall-through into the branch's own delay slots is now implied.
			if (s.fallOverridden() && !intoOwnSlots(fresh, s.fallThrough())) {
				fresh.setFallThrough(s.fallThrough());
			}
			for (Reference ref : s.refs()) {
				if (ref.isMemoryReference() && !ref.getReferenceType().isFallthrough() &&
					manager.getReference(at, ref.getToAddress(), ref.getOperandIndex()) == null) {
					manager.addMemoryReference(at, ref.getToAddress(), ref.getReferenceType(),
						ref.getSource(), ref.getOperandIndex());
				}
			}
			result.redecoded++;
		}
		return true;
	}

	private Instruction create(Address at, boolean inDelaySlot, MessageLog log) {
		try {
			RegisterValue value = program.getProgramContext().getRegisterValue(contextReg, at);
			ProcessorContextImpl context = new ProcessorContextImpl(program.getLanguage());
			if (value != null) context.setRegisterValue(value);
			MemBuffer buf = new MemoryBufferImpl(program.getMemory(), at);
			InstructionPrototype proto = program.getLanguage().parse(buf, context, inDelaySlot);
			return program.getListing().createInstruction(at, proto, buf, context, 0);
		}
		catch (Exception e) {
			log.appendMsg("C6000 Packet Semantics", "cannot redecode " + at + ": " + e);
			return null;
		}
	}

	private static boolean intoOwnSlots(Instruction branch, Address to) {
		int bytes = branch.getPrototype().getDelaySlotByteCount();
		if (to == null || bytes == 0) return false;
		return to.compareTo(branch.getMaxAddress()) > 0 &&
			to.compareTo(branch.getMaxAddress().add(bytes)) <= 0;
	}
}
