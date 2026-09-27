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

import ghidra.app.services.AbstractAnalyzer;
import ghidra.app.services.AnalysisPriority;
import ghidra.app.services.AnalyzerType;
import ghidra.app.util.importer.MessageLog;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.listing.Program;
import ghidra.util.exception.CancelledException;
import ghidra.util.task.TaskMonitor;

/**
 * Gives execute packets and delay slots hardware-accurate p-code; see
 * {@link C6000ParallelSemantics}. Runs after the late branch pass so function
 * bodies and call/return flows are settled, and re-runs on code added later.
 */
public class C6000ParallelSemanticsAnalyzer extends AbstractAnalyzer {
	public C6000ParallelSemanticsAnalyzer() {
		super("C6000 Packet Semantics",
			"Parks register writes so execute packets read pre-packet values and " +
				"multi-cycle results land after their delay slots",
			AnalyzerType.INSTRUCTION_ANALYZER);
		setDefaultEnablement(true);
		setPriority(AnalysisPriority.CODE_ANALYSIS.after().after());
	}

	@Override
	public boolean canAnalyze(Program program) {
		return C6000ParallelSemantics.supported(program);
	}

	@Override
	public boolean added(Program program, AddressSetView set, TaskMonitor monitor,
			MessageLog log) throws CancelledException {
		C6000ParallelSemantics.Result r =
			C6000ParallelSemantics.apply(program, set, monitor, log);
		if (r.redecoded > 0 || r.skipped > 0) {
			log.appendMsg(getName(), r.toString());
		}
		return true;
	}
}
