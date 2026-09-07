/*
 * Copyright 2025 Etienne Payet <etienne.payet at univ-reunion.fr>
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

package fr.univreunion.nti.test;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.program.lp.patternunfolding.patternproducer.CorrectPatternRuleLpProducer;
import fr.univreunion.nti.term.Variable;

class TestCorrectPatternRuleLpProducer {

	@Test
	@DisplayName("build context-shift pattern fact")
	void buildContextShiftPatternFact() throws IOException {
		ParsedRules rules = parseRules(
				"p(0,A).",
				"p(s(X),Y) :- p(X,s(Y)).");

		PatternRuleLp result =
				CorrectPatternRuleLpProducer.tryBuildPatternFactFromContextShift(
						rules.first(),
						rules.second());

		assertNotNull(result);
		assertEquals(
				"p(hat[s(□)]^[1, 0](0),_3) :- e*",
				result.toString(rules.variableNames()));
	}

	@Test
	@DisplayName("build ternary context-shift pattern fact")
	void buildTernaryContextShiftPatternFact() throws IOException {
		ParsedRules rules = parseRules(
				"p(0,A,A).",
				"p(s(X),Y,Z) :- p(X,s(Y),Z).");

		PatternRuleLp result =
				CorrectPatternRuleLpProducer.tryBuildPatternFactFromContextShift(
						rules.first(),
						rules.second());

		assertNotNull(result);
		assertEquals(
				"p(hat[s(□)]^[1, 0](0),_4,hat[s(□)]^[1, 0](_4)) :- e*",
				result.toString(rules.variableNames()));
	}

	@Test
	@DisplayName("reject context-shift pattern fact with incompatible contexts")
	void rejectContextShiftPatternFactWithIncompatibleContexts()
			throws IOException {

		ParsedRules rules = parseRules(
				"p(0,A).",
				"p(s(X),Y) :- p(X,t(Y)).");

		assertNull(
				CorrectPatternRuleLpProducer.tryBuildPatternFactFromContextShift(
						rules.first(),
						rules.second()));
	}

	@Test
	@DisplayName("build pattern fact from two context shifts")
	void buildPatternFactFromTwoContextShifts() throws IOException {
		ParsedRules rules = parseRules(
				"p(a,b).",
				"p(s(X),Y) :- p(X,Y).",
				"p(X,s(Y)) :- p(X,Y).");

		PatternRuleLp result =
				CorrectPatternRuleLpProducer
						.tryBuildPatternFactFromTwoContextShifts(
								rules.first(),
								rules.second(),
								rules.third());

		assertNotNull(result);
		assertEquals(
				"p(hat[s(□)]^[1, 0](a),hat[s(□)]^[1, 0](b)) :- e*",
				result.toString(rules.variableNames()));
	}

	@Test
	@DisplayName("reject two context shifts with different root symbols")
	void rejectTwoContextShiftsWithDifferentRootSymbols() throws IOException {
		ParsedRules rules = parseRules(
				"p(a,b).",
				"p(s(X),Y) :- q(X,Y).",
				"p(X,s(Y)) :- p(X,Y).");

		assertNull(
				CorrectPatternRuleLpProducer
						.tryBuildPatternFactFromTwoContextShifts(
								rules.first(),
								rules.second(),
								rules.third()));
	}

	@Test
	@DisplayName("reject two context shifts with shared fact variables")
	void rejectTwoContextShiftsWithSharedFactVariables() throws IOException {
		ParsedRules rules = parseRules(
				"p(A,A).",
				"p(s(X),Y) :- p(X,Y).",
				"p(X,s(Y)) :- p(X,Y).");

		assertNull(
				CorrectPatternRuleLpProducer
						.tryBuildPatternFactFromTwoContextShifts(
								rules.first(),
								rules.second(),
								rules.third()));
	}

	@Test
	@DisplayName("reject two context shifts with incompatible contexts")
	void rejectTwoContextShiftsWithIncompatibleContexts() throws IOException {
		ParsedRules rules = parseRules(
				"p(a,b).",
				"p(s(X),Y) :- p(X,Y).",
				"p(X,t(Y)) :- p(X,Y).");

		assertNull(
				CorrectPatternRuleLpProducer
						.tryBuildPatternFactFromTwoContextShifts(
								rules.first(),
								rules.second(),
								rules.third()));
	}

	private static ParsedRules parseRules(String first, String second)
			throws IOException {
		return parseRules(first, second, null);
	}

	private static ParsedRules parseRules(
			String first,
			String second,
			String third) throws IOException {

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		return new ParsedRules(
				parser.parseLpRule(first, variables),
				parser.parseLpRule(second, variables),
				third == null ? null : parser.parseLpRule(third, variables),
				reverse(variables));
	}

	private static Map<Variable, String> reverse(
			Map<String, Variable> variables) {

		Map<Variable, String> result = new HashMap<>();
		for (Map.Entry<String, Variable> entry : variables.entrySet())
			result.put(entry.getValue(), entry.getKey());

		return result;
	}

	private record ParsedRules(
			RuleLp first,
			RuleLp second,
			RuleLp third,
			Map<Variable, String> variableNames) {}
}
