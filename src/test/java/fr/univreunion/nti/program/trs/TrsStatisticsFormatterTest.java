/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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

package fr.univreunion.nti.program.trs;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Variable;

class TrsStatisticsFormatterTest {

	private final TrsStatisticsFormatter formatter =
			new TrsStatisticsFormatter();

	@Test
	@DisplayName("format statistics without SCC aggregates for an acyclic TRS")
	void formatStatisticsForAnAcyclicTrs() throws IOException {
		Trs trs = new Trs("acyclic.trs", parseRules(
				"f(X) -> g(X)"), "FULL");
		String symbolStatistics = FunctionSymbol.toStringStat();

		String result = this.formatter.format(trs);

		assertEquals(
				"** BEGIN STATS for program: acyclic.trs\n" +
				"* 1 rule(s)\n" +
				"* 0 SCC(s)\n" +
				"* 0 initial dependency pair(s)\n" +
				"* " + symbolStatistics + "\n" +
				"** END STATS for program: acyclic.trs",
				result);
	}

	@Test
	@DisplayName("format ordered min max average and initial-pair statistics")
	void formatSccAggregatesAndInitialPairCount() throws IOException {
		Trs trs = new Trs("cyclic.trs", parseRules(
				"f(X) -> g(X)",
				"g(X) -> f(X)",
				"h(X) -> h(X)"), "FULL");
		String symbolStatistics = FunctionSymbol.toStringStat();

		String result = trs.toStringStat();

		assertEquals(
				"** BEGIN STATS for program: cyclic.trs\n" +
				"* 3 rule(s)\n" +
				"* 2 SCC(s) -- nb rules: min=1 max=2 avg=1.5\n" +
				"* 3 initial dependency pair(s)\n" +
				"* " + symbolStatistics + "\n" +
				"** END STATS for program: cyclic.trs",
				result);
	}

	private static List<RuleTrs> parseRules(String... ruleTexts)
			throws IOException {

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new ArrayList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return rules;
	}
}
