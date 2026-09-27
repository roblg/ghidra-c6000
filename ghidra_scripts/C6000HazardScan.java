// SPDX-License-Identifier: Apache-2.0
// Measures where sequential, per-instruction p-code disagrees with C6000
// hardware timing:
//   PACKET: an instruction reads a register written by an earlier member of
//           the same execute packet (hardware reads the pre-packet value).
//   DELAY:  an instruction reads (or overwrites) the destination of a
//           multi-cycle instruction (load, multiply, FP) before that result
//           lands (hardware still sees the old value).
//   BRANCH: a branch whose five delay cycles hold work other than NOPs
//           (hardware runs that work before the branch takes effect).
// With the packet-semantics analyzer installed, *_FIXED rows are hazards whose
// eps/epd context bit is set, and branches lifted with their delay slots
// (ep_br), so the lifted p-code already models them.
// Usage: -postScript C6000HazardScan.java [outfile.tsv]
// Set DEBUG=1 to print every hazard to the log as well.
//@category C6000

import java.io.File;
import java.io.PrintWriter;
import java.util.*;

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.lang.Register;
import ghidra.program.model.listing.*;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.Varnode;

public class C6000HazardScan extends GhidraScript {

	static int delaySlots(String m) {
		return c6000.C6000ParallelSemantics.delaySlots(m);
	}

	private boolean touchesShadow(PcodeOp op) {
		if (isShadow(op.getOutput())) return true;
		for (Varnode in : op.getInputs()) if (isShadow(in)) return true;
		return false;
	}

	private boolean isShadow(Varnode v) {
		if (v == null || !v.isRegister()) return false;
		Register r = currentProgram.getRegister(v.getAddress(), v.getSize());
		return r != null && r.getName().matches(".*_(sv|pk|dl)");
	}

	/** True if the packet-semantics context bit {@code prefix+reg} is set at insn. */
	private boolean handled(Instruction insn, String prefix, String reg) {
		Register field = currentProgram.getRegister(prefix + reg);
		if (field == null) return false;
		var v = currentProgram.getProgramContext().getValue(field, insn.getMinAddress(), false);
		return v != null && v.testBit(0);
	}

	private boolean isGpr(Register r) {
		return r != null && r.getName().matches("[AB]\\d+");
	}

	/** General-register 4-byte units covered by a register-space varnode. */
	private Set<String> units(Varnode v) {
		Set<String> out = new HashSet<>();
		if (v == null || !v.isRegister()) return out;
		for (int off = 0; off < v.getSize(); off += 4) {
			Register r = currentProgram.getRegister(v.getAddress().add(off), 4);
			if (isGpr(r)) out.add(r.getName());
		}
		return out;
	}

	private static class Effects {
		Set<String> reads = new HashSet<>();
		Set<String> writes = new HashSet<>();
		Set<String> delayed = new HashSet<>(); // subset of writes landing late
		int delay;
	}

	private Effects effects(Instruction insn) {
		Effects e = new Effects();
		Set<String> writtenSoFar = new HashSet<>();
		if (slotted(insn)) {
			// The branch's p-code carries its delay slots; they are scanned
			// as instructions of their own.
			return e;
		}
		for (PcodeOp op : insn.getPcode()) {
			if (touchesShadow(op)) continue; // packet-semantics wrapper copies
			for (Varnode in : op.getInputs()) {
				for (String u : units(in)) {
					if (!writtenSoFar.contains(u)) e.reads.add(u);
				}
			}
			for (String u : units(op.getOutput())) {
				writtenSoFar.add(u);
				e.writes.add(u);
			}
		}
		e.delay = delaySlots(insn.getMnemonicString());
		if (e.delay > 0 && insn.getNumOperands() > 0) {
			// Only the destination operand lands late; base-register
			// updates (*A4++) take effect immediately.
			for (Object o : insn.getOpObjects(insn.getNumOperands() - 1)) {
				if (o instanceof Register r) {
					for (Register c : expand(r)) {
						if (e.writes.contains(c.getName())) e.delayed.add(c.getName());
					}
				}
			}
		}
		return e;
	}

	private List<Register> expand(Register r) {
		if (isGpr(r)) return List.of(r);
		List<Register> out = new ArrayList<>();
		for (Register c : r.getChildRegisters()) out.addAll(expand(c));
		if (out.isEmpty()) {
			for (int off = 0; off < r.getMinimumByteSize(); off += 4) {
				Register c = currentProgram.getRegister(r.getAddress().add(off), 4);
				if (isGpr(c)) out.add(c);
			}
		}
		return out;
	}

	private boolean parallelWithNext(Instruction insn) throws Exception {
		Address a = insn.getMinAddress();
		if (insn.getLength() == 4) return (getInt(a) & 1) != 0;
		long base = a.getOffset() & ~31L;
		int header = getInt(a.getNewAddress(base + 28));
		return ((header >>> ((a.getOffset() - base) / 2)) & 1) != 0;
	}

	/** Cycles a packet member occupies; mirrors C6000ParallelSemantics. */
	private int nopCycles(Instruction insn) {
		String m = insn.getMnemonicString().toUpperCase().replaceFirst("^_", "")
				.replaceAll("^\\[[^]]*\\]", "").replaceAll("\\..*", "");
		if (m.equals("CALLP")) return 6;
		if (m.startsWith("LD")) {
			// PROT=1 compact fetch packet: four NOP cycles after each load.
			Register prot = currentProgram.getRegister("c_prot");
			var v = prot == null ? null
					: currentProgram.getProgramContext().getValue(prot, insn.getMinAddress(), false);
			if (v != null && v.testBit(0)) return 5;
		}
		int operand, self;
		if (m.equals("NOP")) { operand = 0; self = 0; }
		else if (m.equals("BNOP")) { operand = 1; self = 1; }
		else if (m.equals("ADDKPC")) { operand = 2; self = 1; }
		else return 1;
		if (insn.getNumOperands() <= operand) return 1;
		for (Object o : insn.getOpObjects(operand)) {
			if (o instanceof ghidra.program.model.scalar.Scalar s) {
				return (int) Math.max(1, s.getUnsignedValue() + self);
			}
		}
		String text = insn.getDefaultOperandRepresentation(operand);
		if (text != null && text.matches("[0-9]")) return Math.max(1, Integer.parseInt(text) + self);
		return 1;
	}


	private record Pending(String reg, int landsAt, Instruction writer) {}

	/** A branch whose five delay cycles are being watched for real work. */
	private static final class Window {
		final Instruction branch;
		final int issue;
		boolean work;

		Window(Instruction branch, int issue) {
			this.branch = branch;
			this.issue = issue;
		}
	}

	private boolean slotted(Instruction insn) {
		Register br = currentProgram.getRegister("ep_br");
		if (br == null) return false;
		var v = insn.getRegisterValue(br);
		return v != null && v.hasValue() && v.getUnsignedValue().testBit(0);
	}

	private static boolean isBranch(Instruction insn) {
		String m = insn.getMnemonicString().toUpperCase().replaceAll("^\\[[^]]*\\]", "")
				.replaceAll("\\..*", "");
		return m.equals("B") || m.equals("BNOP") || m.equals("BDEC") || m.equals("BPOS");
	}

	private int branchWork, branchSlotted;

	private void closeWindow(Window w, PrintWriter out, boolean debug) {
		if (w == null || !w.work) return;
		branchWork++;
		boolean ok = slotted(w.branch);
		if (ok) branchSlotted++;
		report(out, debug, ok ? "BRANCH_FIXED" : "BRANCH", w.branch, w.branch, "-");
	}

	@Override
	public void run() throws Exception {
		String[] args = getScriptArgs();
		boolean debug = System.getenv("DEBUG") != null;
		PrintWriter out = args.length > 0 ? new PrintWriter(new File(args[0])) : null;

		int packets = 0, multi = 0, packetHaz = 0, delayHaz = 0, delayWaw = 0;
		int packetFixed = 0, delayFixed = 0;
		Map<String, Integer> byWriter = new TreeMap<>();
		Set<Function> affected = new HashSet<>();

		for (Function f : currentProgram.getFunctionManager().getFunctions(true)) {
			if (monitor.isCancelled()) break;
			List<Pending> pending = new ArrayList<>();
			List<Window> windows = new ArrayList<>();
			int cycle = 0;
			Instruction prevEnd = null;
			InstructionIterator it = currentProgram.getListing().getInstructions(f.getBody(), true);
			List<Instruction> pkt = new ArrayList<>();
			while (it.hasNext()) {
				Instruction insn = it.next();
				// Non-contiguous code restarts timing (conservative: drop pending).
				if (prevEnd != null && pkt.isEmpty() &&
					insn.getMinAddress().subtract(prevEnd.getMaxAddress()) > 5) {
					pending.clear();
					for (Window w : windows) closeWindow(w, out, debug);
					windows.clear();
				}
				pkt.add(insn);
				boolean more;
				try {
					more = parallelWithNext(insn);
				}
				catch (Exception e) {
					more = false;
				}
				if (more && it.hasNext()) continue;

				packets++;
				if (pkt.size() > 1) multi++;
				List<Effects> eff = new ArrayList<>();
				for (Instruction p : pkt) eff.add(effects(p));
				// Delay-slot work: later members of a branch's packet and the
				// packets of the next five cycles.
				for (Window w : windows) {
					if (w.issue < cycle && cycle <= w.issue + 5) {
						for (Instruction p : pkt) w.work |= !isNop(p);
					}
				}
				for (int j = 0; j < pkt.size(); j++) {
					if (!isBranch(pkt.get(j)) || nopCycles(pkt.get(j)) > 5) continue;
					Window w = new Window(pkt.get(j), cycle);
					for (int k = j + 1; k < pkt.size(); k++) w.work |= !isNop(pkt.get(k));
					windows.add(w);
				}

				// Same-packet read after an earlier member's write.
				for (int j = 0; j < pkt.size(); j++) {
					for (int i = 0; i < j; i++) {
						for (String r : eff.get(j).reads) {
							if (eff.get(i).writes.contains(r)) {
								packetHaz++;
								affected.add(f);
								boolean ok = handled(pkt.get(i), "eps", r) || handled(pkt.get(i), "epd", r);
								if (ok) packetFixed++;
								report(out, debug, ok ? "PACKET_FIXED" : "PACKET", pkt.get(j),
									pkt.get(i), r);
							}
						}
					}
				}
				// Reads/writes of registers whose pending result has not landed.
				for (int j = 0; j < pkt.size(); j++) {
					for (Pending p : pending) {
						if (p.landsAt < cycle) continue;
						if (eff.get(j).reads.contains(p.reg)) {
							delayHaz++;
							affected.add(f);
							byWriter.merge(p.writer.getMnemonicString(), 1, Integer::sum);
							boolean ok = handled(p.writer, "epd", p.reg);
							if (ok) delayFixed++;
							report(out, debug, ok ? "DELAY_FIXED" : "DELAY", pkt.get(j), p.writer,
								p.reg);
						}
						else if (eff.get(j).writes.contains(p.reg) && pkt.get(j) != p.writer) {
							delayWaw++;
							affected.add(f);
							boolean ok = handled(p.writer, "epd", p.reg);
							if (ok) delayFixed++;
							report(out, debug, ok ? "DELAY_WAW_FIXED" : "DELAY_WAW", pkt.get(j),
								p.writer, p.reg);
						}
					}
				}
				int packetCycles = 1;
				for (int j = 0; j < pkt.size(); j++) {
					Effects e = eff.get(j);
					for (String r : e.delayed) {
						pending.add(new Pending(r, cycle + e.delay, pkt.get(j)));
					}
					packetCycles = Math.max(packetCycles, nopCycles(pkt.get(j)));
				}
				cycle += packetCycles;
				final int now = cycle;
				pending.removeIf(p -> p.landsAt < now);
				windows.removeIf(w -> {
					if (w.issue + 5 >= now) return false;
					closeWindow(w, out, debug);
					return true;
				});
				prevEnd = pkt.get(pkt.size() - 1);
				pkt.clear();
			}
			for (Window w : windows) closeWindow(w, out, debug);
		}
		if (out != null) out.close();
		println(String.format(
			"C6000_HAZARDS packets=%d multi=%d packet_raw=%d delay_raw=%d delay_waw=%d functions=%d/%d",
			packets, multi, packetHaz, delayHaz, delayWaw, affected.size(),
			currentProgram.getFunctionManager().getFunctionCount()));
		println(String.format("C6000_HAZARDS handled: packet %d/%d delay %d/%d",
			packetFixed, packetHaz, delayFixed, delayHaz + delayWaw));
		println(String.format("C6000_HAZARDS branch delay slots with work: %d, inlined %d",
			branchWork, branchSlotted));
		println("C6000_HAZARDS delay_raw by writer: " + byWriter);
		Map<String, Integer> reasons = new TreeMap<>();
		var marks = currentProgram.getBookmarkManager().getBookmarksIterator("Warning");
		while (marks.hasNext()) {
			var b = marks.next();
			if ("C6000 packet semantics".equals(b.getCategory())) {
				reasons.merge(b.getComment(), 1, Integer::sum);
			}
		}
		println("C6000_HAZARDS unsupported (bookmarked): " + reasons);
	}

	private static boolean isNop(Instruction insn) {
		String m = insn.getMnemonicString().toUpperCase().replaceFirst("^_", "");
		return m.equals("NOP") || m.startsWith("NOP ") || m.equals("CPKT");
	}

	private void report(PrintWriter out, boolean debug, String kind, Instruction at,
			Instruction writer, String reg) {
		String line = String.format("%s\t%s\t%s\t%s\t%s\t%s", kind, at.getMinAddress(), at,
			writer.getMinAddress(), writer, reg);
		if (out != null) out.println(line);
		if (debug) println(line);
	}
}
