/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
 *
 * This file is part of NTI.
 *
 * NTI is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * NTI is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.patternunfolding;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.Printer;
import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Variable;

class TrsPatternUnfolderTest {

	@Test
	@DisplayName("print complete TRS pattern-unfolding iterations and counts")
	void printCompletePatternUnfoldingIterationsAndCounts() throws IOException {
		RecordingPrinter printer = new RecordingPrinter();

		TrsPatternUnfolder.printUnfoldings(chainTrs(), 2, printer);

		assertEquals(List.of(
				"== Pattern unfoldings ==",
				"** Iteration 0:",
				"p(_0) -> q(_0):?",
				"q(a) -> a:?",
				"** 2 unfolded rules generated",
				"** Iteration 1:",
				"p(a) -> a:?",
				"** 1 unfolded rules generated",
				"** Iteration 2:",
				"** 0 unfolded rules generated",
				"================",
				"Total number of generated unfolded rules = 3"),
				printer.lines());
	}

	@Test
	@DisplayName("preserve a consistent partial report when interrupted")
	void preserveConsistentPartialReportWhenInterrupted() throws IOException {
		RecordingPrinter printer = new RecordingPrinter();

		Thread.currentThread().interrupt();
		try {
			TrsPatternUnfolder.printUnfoldings(chainTrs(), 2, printer);
		}
		finally {
			Thread.interrupted();
		}

		assertEquals(List.of(
				"== Pattern unfoldings ==",
				"================",
				"Total number of generated unfolded rules = 0"),
				printer.lines());
	}

	private static Trs chainTrs() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = List.of(
				parser.parseTrsRule("p(X) -> q(X)", variables),
				parser.parseTrsRule("q(a) -> a", variables));

		return new Trs("", new LinkedList<>(rules), "FULL");
	}

	private static final class RecordingPrinter extends Printer {

		private final List<String> lines = new ArrayList<>();

		private RecordingPrinter() {
			super(false);
		}

		@Override
		public void println(Object object) {
			this.lines.add(String.valueOf(object));
		}

		private List<String> lines() {
			return List.copyOf(this.lines);
		}
	}
}
