// SPDX-License-Identifier: Apache-2.0
// @category C6000
// Execute tests/fixtures/packet-semantics.py in the p-code emulator and check
// that execute packets read pre-packet registers, that load and multiply
// results land after their delay slots, and that branch delay slots run
// before the branch takes effect.

import java.util.Map;

import ghidra.app.emulator.EmulatorHelper;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Bookmark;
import ghidra.program.model.listing.BookmarkType;

public class C6000PacketSemanticsTest extends GhidraScript {
	@Override
	protected void run() throws Exception {
		Address start = toAddr(0x1000);
		Address stop = toAddr(0x1060);
		if (getFunctionAt(start) == null) {
			throw new AssertionError("no function at 0x1000; import with auto-analysis");
		}
		for (Bookmark b : currentProgram.getBookmarkManager().getBookmarks(start,
			BookmarkType.WARNING)) {
			throw new AssertionError("unsupported hazard: " + b.getComment());
		}
		EmulatorHelper emu = new EmulatorHelper(currentProgram);
		try {
			Map<String, Long> init = Map.of("A0", 0L, "A1", 5L, "A2", 7L, "A4", 0x1800L,
				"A5", 0x55L, "A8", 0x99L);
			for (Map.Entry<String, Long> e : init.entrySet()) {
				emu.writeRegister(e.getKey(), e.getValue());
			}
			emu.getEmulator().setExecuteAddress(0x1000);
			int steps = 0;
			var ctx = currentProgram.getProgramContext();
			while (!emu.getExecutionAddress().equals(stop)) {
				// The emulator flows its own decode context and does not read
				// per-address noflow values, which carry the packet masks.
				// Unset fields must read as zero rather than keep the last value.
				var base = ctx.getBaseContextRegister();
				var stored = ctx.getRegisterValue(base, emu.getExecutionAddress());
				var zero = new ghidra.program.model.lang.RegisterValue(base,
					java.math.BigInteger.ZERO);
				emu.setContextRegister(stored == null ? zero : zero.combineValues(stored));
				Address pc = emu.getExecutionAddress();
				if (!emu.step(monitor) || ++steps > 200) {
					throw new AssertionError("emulation stopped at " +
						emu.getExecutionAddress() + ": " + emu.getLastError());
				}
				if (System.getenv("DEBUG") != null) {
					println(String.format("%s -> %s A5=%x A5_dl=%x", pc,
						emu.getExecutionAddress(), emu.readRegister("A5"),
						emu.readRegister("A5_dl")));
				}
			}
			Map<String, Long> want = Map.ofEntries(Map.entry("A1", 0xffffffffL),
				Map.entry("A2", 5L), Map.entry("A5", 0x11223344L), Map.entry("A6", 0x55L),
				Map.entry("A7", 0x11223344L), Map.entry("A8", 35L), Map.entry("A9", 0x99L),
				Map.entry("A10", 35L), Map.entry("A12", 4L), Map.entry("A14", 7L));
			StringBuilder bad = new StringBuilder();
			for (Map.Entry<String, Long> e : want.entrySet()) {
				long got = emu.readRegister(e.getKey()).longValue() & 0xffffffffL;
				if (got != e.getValue()) {
					bad.append(String.format(" %s=0x%x(want 0x%x)", e.getKey(), got,
						e.getValue()));
				}
			}
			if (bad.length() > 0) throw new AssertionError("wrong registers:" + bad);
		}
		finally {
			emu.dispose();
		}
		println("C6000_PACKET_SEMANTICS_OK");
	}
}
