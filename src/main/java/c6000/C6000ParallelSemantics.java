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
import ghidra.program.disassemble.Disassembler;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.lang.Register;
import ghidra.program.model.lang.RegisterValue;
import ghidra.program.model.listing.*;
import ghidra.program.model.mem.MemoryAccessException;
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
 * <p>Hazards the model cannot express (branches inside a delay window, entry
 * points inside a window, two in-flight writes of one register, software
 * pipelined loop bodies) are left as they were and marked with a warning
 * bookmark in category {@value #BOOKMARK}.
 */
public final class C6000ParallelSemantics {

	public static final String BOOKMARK = "C6000 packet semantics";

	private static final String[] BANKS = { "eps", "epd", "epc", "epe" };
	private static final int EPS = 0, EPD = 1, EPC = 2, EPE = 3;

	/** Totals from one run. */
	public static final class Result {
		public int packetHazards, delayHazards, skipped, redecoded;

		@Override
		public String toString() {
			return String.format("packet=%d delay=%d skipped=%d redecoded=%d",
				packetHazards, delayHazards, skipped, redecoded);
		}
	}

	private final Program program;
	private final TaskMonitor monitor;
	private final Register contextReg;
	private final Register cpre;
	private final Register any;
	private final Register[][] fields = new Register[4][64];
	private final Result result = new Result();

	private C6000ParallelSemantics(Program program, TaskMonitor monitor) {
		this.program = program;
		this.monitor = monitor;
		this.contextReg = program.getProgramContext().getBaseContextRegister();
		this.cpre = program.getRegister("ep_cpre");
		this.any = program.getRegister("ep_any");
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

	/** {@code [!A0]LDW.D1} -> {@code LDW}. */
	public static String baseMnemonic(String mnemonic) {
		String m = mnemonic.toUpperCase(Locale.ROOT);
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

		Effects(Instruction insn) {
			this.insn = insn;
			BitSet written = new BitSet(64);
			for (PcodeOp op : insn.getPcode()) {
				if (touchesShadow(op)) continue; // wrapper copies from a previous run
				for (Varnode in : op.getInputs()) {
					units(in, bit -> { if (!written.get(bit)) reads.set(bit); });
				}
				units(op.getOutput(), bit -> { written.set(bit); writes.set(bit); });
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
		}

		BitSet immediateWrites() {
			BitSet b = (BitSet) writes.clone();
			b.andNot(delayed);
			return b;
		}
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
		return insn.getMnemonicString().equals("CPKT");
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
	private List<List<Packet>> runs(Function f) {
		List<List<Packet>> runs = new ArrayList<>();
		List<Packet> run = new ArrayList<>();
		Packet packet = null;
		Address expected = null;
		int cycle = 0;
		boolean inLoop = false;
		InstructionIterator it = program.getListing().getInstructions(f.getBody(), true);
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

		boolean any() {
			return cpre || !bank[EPS].isEmpty() || !bank[EPD].isEmpty() ||
				!bank[EPC].isEmpty() || !bank[EPE].isEmpty();
		}
	}

	private void function(Function f, MessageLog log) throws CancelledException {
		Map<Address, Want> wants = new HashMap<>();
		List<Instruction> all = new ArrayList<>();
		for (List<Packet> run : runs(f)) {
			for (Packet p : run) {
				for (Effects e : p.members) {
					all.add(e.insn);
				}
			}
			for (int i = 0; i < run.size(); i++) {
				monitor.checkCancelled();
				packetHazards(run.get(i), wants);
				delayHazards(run, i, wants);
			}
		}
		for (Instruction insn : all) {
			monitor.checkCancelled();
			Want w = wants.get(insn.getMinAddress());
			if (w != null && w.cpre && (!w.bank[EPS].isEmpty() || !w.bank[EPD].isEmpty())) {
				// Unreachable by construction: only a packet's last member gets
				// ep_cpre, a last member never parks for its own packet, and a
				// branch is never a delayed writer.
				log.appendMsg("C6000 Packet Semantics",
					"internal: branch with park bits at " + insn.getMinAddress());
			}
			apply(insn.getMinAddress(), w, log);
		}
	}

	private Want want(Map<Address, Want> wants, Effects e) {
		return wants.computeIfAbsent(e.insn.getMinAddress(), a -> new Want());
	}

	private void skip(Effects at, String why) {
		result.skipped++;
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
			if (p.members.get(i).flow || p.members.get(i).compactBranch) {
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
			if (last.compactBranch) why = "compact branch carries its followers' p-code";
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

	private void delayHazards(List<Packet> run, int pi, Map<Address, Want> wants) {
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
				String why = delayProblem(run, pi, wi, qi, r);
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

	private String delayProblem(List<Packet> run, int pi, int wi, int qi, int r) {
		Packet p = run.get(pi);
		if (qi < 0) return "delayed write lands after the end of straight-line code";
		if (p.inLoop) return "delayed write inside a software-pipelined loop";
		Packet q = run.get(qi);
		ReferenceManager refs = program.getReferenceManager();
		for (int k = pi; k <= qi; k++) {
			Packet x = run.get(k);
			for (int j = 0; j < x.members.size(); j++) {
				Effects e = x.members.get(j);
				boolean lastOfLanding = k == qi && j == x.members.size() - 1;
				if ((e.flow || e.compactBranch) && !lastOfLanding) {
					return "branch inside a delay window";
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
			if (ref.getReferenceType().isFlow()) return true;
		}
		return false;
	}

	// ------------------------------------------------------------------
	// Applying context

	private boolean differs(RegisterValue current, Want w) {
		for (int b = 0; b < 4; b++) {
			for (int r = 0; r < 64; r++) {
				boolean want = w != null && w.bank[b].get(r);
				if (bit(current, fields[b][r]) != want) return true;
			}
		}
		return bit(current, cpre) != (w != null && w.cpre) ||
			bit(current, any) != (w != null && w.any());
	}

	private static boolean bit(RegisterValue v, Register field) {
		if (v == null || field == null) return false;
		RegisterValue sub = v.getRegisterValue(field);
		return sub != null && sub.hasValue() && sub.getUnsignedValue().testBit(0);
	}

	private void apply(Address at, Want w, MessageLog log) {
		ProgramContext ctx = program.getProgramContext();
		RegisterValue current = ctx.getRegisterValue(contextReg, at);
		if (!differs(current, w)) return;
		Listing listing = program.getListing();
		Instruction old = listing.getInstructionAt(at);
		if (old == null) return;
		Address end = old.getMaxAddress();
		Reference[] saved = old.getReferencesFrom();
		FlowOverride override = old.getFlowOverride();
		Address fallThrough = old.isFallThroughOverridden() ? old.getFallThrough() : null;
		boolean fallOverridden = old.isFallThroughOverridden();
		int length = old.getLength();

		RegisterValue value = current == null ? new RegisterValue(contextReg) : current;
		for (int b = 0; b < 4; b++) {
			for (int r = 0; r < 64; r++) {
				boolean on = w != null && w.bank[b].get(r);
				value = value.assign(fields[b][r], on ? BigInteger.ONE : BigInteger.ZERO);
			}
		}
		value = value.assign(cpre, (w != null && w.cpre) ? BigInteger.ONE : BigInteger.ZERO);
		value = value.assign(any, (w != null && w.any()) ? BigInteger.ONE : BigInteger.ZERO);

		listing.clearCodeUnits(at, end, false);
		try {
			ctx.setRegisterValue(at, at, value);
		}
		catch (ContextChangeException e) {
			log.appendException(e);
		}
		Disassembler.getDisassembler(program, monitor, null)
				.disassemble(at, new AddressSet(at, end), false);
		Instruction fresh = listing.getInstructionAt(at);
		if (fresh == null || fresh.getLength() != length) {
			log.appendMsg("C6000 Packet Semantics", "redecode changed instruction at " + at);
			return;
		}
		if (override != FlowOverride.NONE) fresh.setFlowOverride(override);
		if (fallOverridden) fresh.setFallThrough(fallThrough);
		ReferenceManager manager = program.getReferenceManager();
		for (Reference ref : saved) {
			if (ref.isMemoryReference() &&
				manager.getReference(at, ref.getToAddress(), ref.getOperandIndex()) == null) {
				manager.addMemoryReference(at, ref.getToAddress(), ref.getReferenceType(),
					ref.getSource(), ref.getOperandIndex());
			}
		}
		result.redecoded++;
	}
}
