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

package fr.univreunion.nti.program.lp;

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

class LpStatisticsFormatterTest {

	private final LpStatisticsFormatter formatter =
			new LpStatisticsFormatter();

	@Test
	@DisplayName("format the complete statistics of an empty logic program")
	void formatEmptyProgramStatistics() {
		Lp lp = new Lp("empty.pl", List.of(), mode("empty"));

		String result = this.formatter.format(lp);

		assertEquals(
				"** BEGIN STATS for program: empty.pl\n" +
				"* 0 rule(s)\n" +
				"** END STATS for program: empty.pl",
				result);
	}

	@Test
	@DisplayName("format a non-empty program through Lp delegation")
	void formatNonEmptyProgramThroughLpDelegation() throws IOException {
		Lp lp = new Lp("program.pl", parseRules(
				"p(X) :- q(X).",
				"q(a)."), mode("p"));

		String result = lp.toStringStat();

		assertEquals(
				"** BEGIN STATS for program: program.pl\n" +
				"* 2 rule(s)\n" +
				"** END STATS for program: program.pl",
				result);
	}

	private static List<RuleLp> parseRules(String... ruleTexts)
			throws IOException {

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleLp> rules = new ArrayList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseLpRule(ruleText, variables));
		return rules;
	}

	private static Mode mode(String predicateName) {
		return new Mode(FunctionSymbol.intern(predicateName, 0), List.of());
	}
}
