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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.patternunfolding.patternproducer;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;

class CorrectPatternRuleTrsProducerTest {

	private final ParserString parser = new ParserString();

	@Test
	void buildsRuleFromProposition9Candidate() throws IOException {
		RuleTrs firstRule = rule("f(s(X)) -> g(f(X))");
		RuleTrs secondRule = rule("f(0) -> a");

		Collection<PatternRuleTrs> patternRules =
				CorrectPatternRuleTrsProducer.collectPatternRulesWithProp9Wst25(
						firstRule, secondRule);

		assertEquals(1, patternRules.size());
		assertEquals(
				"f(hat[s(□)]^[1, 0](0)) -> hat[g(□)]^[1, 0](a):?",
				patternRules.iterator().next().toString(new HashMap<>()));
	}

	@Test
	void preservesCandidatePositionOrder() throws IOException {
		RuleTrs firstRule = rule("f(0) -> g(f(0),f(0))");
		RuleTrs secondRule = rule("f(0) -> a");

		Collection<PatternRuleTrs> patternRules =
				CorrectPatternRuleTrsProducer.collectPatternRulesWithProp9Wst25(
						firstRule, secondRule);

		assertEquals(
				List.of(
						"f(0) -> hat[g(□,f(0))]^[1, 0](a):?",
						"f(0) -> hat[g(f(0),□)]^[1, 0](a):?"),
				render(patternRules));
	}

	@Test
	void rejectsVariableRightHandSide() throws IOException {
		assertProp9Rejected("f(X) -> X", "f(0) -> a");
	}

	@Test
	void rejectsCandidateWithIncompatiblePositions() throws IOException {
		assertProp9Rejected("f(s(X)) -> g(f(X))", "f(0,0) -> a");
	}

	@Test
	void rejectsUnsuitablePumpingSubstitution() throws IOException {
		assertProp9Rejected("f(s(Y)) -> g(f(X))", "f(0) -> a");
	}

	@Test
	void buildsRuleFromBinaryContextShift() throws IOException {
		Collection<PatternRuleTrs> patternRules = collectContextShifts(
				"p(0,A) -> q(A)",
				"p(s(X),Y) -> p(X,s(Y))");

		assertEquals(List.of(
				"p(hat[s(□)]^[1, 0](0),_0) -> q(hat[s(□)]^[1, 0](_0)):?"),
				render(patternRules));
	}

	@Test
	void buildsRuleFromTernaryContextShift() throws IOException {
		Collection<PatternRuleTrs> patternRules = collectContextShifts(
				"p(0,A,A) -> q(A)",
				"p(s(X),Y,Z) -> p(X,s(Y),Z)");

		assertEquals(List.of(
				"p(hat[s(□)]^[1, 0](0),_0,hat[s(□)]^[1, 0](_0))"
						+ " -> q(hat[s(□)]^[1, 0](_0)):?"),
				render(patternRules));
	}

	@Test
	void preservesContextShiftCandidatePositionOrder() throws IOException {
		Collection<PatternRuleTrs> patternRules = collectContextShifts(
				"h(p(0,A),p(0,B)) -> q(A,B)",
				"p(s(X),Y) -> p(X,s(Y))");

		assertEquals(List.of(
				"h(p(hat[s(□)]^[1, 0](0),_0),p(0,_1))"
						+ " -> q(hat[s(□)]^[1, 0](_0),_1):?",
				"h(p(0,_0),p(hat[s(□)]^[1, 0](0),_1))"
						+ " -> q(_0,hat[s(□)]^[1, 0](_1)):?"),
				render(patternRules));
	}

	@Test
	void rejectsContextShiftWithIncompatibleContexts() throws IOException {
		assertTrue(collectContextShifts(
				"p(0,A) -> q(A)",
				"p(s(X),Y) -> p(X,t(Y))").isEmpty());
	}

	@Test
	void contextShiftSearchDoesNotModifyInputRules() throws IOException {
		RuleTrs firstRule = rule("h(p(0,A),p(0,B)) -> q(A,B)");
		RuleTrs secondRule = rule("p(s(X),Y) -> p(X,s(Y))");
		String firstBefore = firstRule.toString();
		String secondBefore = secondRule.toString();

		CorrectPatternRuleTrsProducer.collectPatternRulesFromContextShift(
				firstRule, secondRule);

		assertEquals(firstBefore, firstRule.toString());
		assertEquals(secondBefore, secondRule.toString());
	}

	@Test
	void buildsRuleFromTwoContextShifts() throws IOException {
		PatternRuleTrs patternRule = buildFromTwoContextShifts(
				"p(a,b) -> q",
				"p(s(X),Y) -> p(X,Y)",
				"p(X,s(Y)) -> p(X,Y)");

		assertEquals(
				"p(hat[s(□)]^[1, 0](a),hat[s(□)]^[1, 0](b)) -> q:?",
				patternRule.toString(new HashMap<>()));
	}

	@Test
	void rejectsTwoContextShiftsWithDifferentRootSymbols() throws IOException {
		assertNull(buildFromTwoContextShifts(
				"p(a,b) -> q",
				"p(s(X),Y) -> p(X,Y)",
				"r(X,s(Y)) -> r(X,Y)"));
	}

	@Test
	void rejectsTwoContextShiftsWithNonBinaryRoot() throws IOException {
		assertNull(buildFromTwoContextShifts(
				"p(a,b,c) -> q",
				"p(s(X),Y,Z) -> p(X,Y,Z)",
				"p(X,s(Y),Z) -> p(X,Y,Z)"));
	}

	@Test
	void rejectsTwoContextShiftsWithNonDistinctVariables() throws IOException {
		assertNull(buildFromTwoContextShifts(
				"p(a,b) -> q",
				"p(s(X),X) -> p(X,X)",
				"p(X,s(Y)) -> p(X,Y)"));
	}

	@Test
	void rejectsTwoContextShiftsWithIncompatibleContexts() throws IOException {
		assertNull(buildFromTwoContextShifts(
				"p(a,b) -> q",
				"p(s(X),Y) -> p(X,Y)",
				"p(X,t(Y)) -> p(X,Y)"));
	}

	@Test
	void twoContextShiftSearchDoesNotModifyInputRules() throws IOException {
		RuleTrs firstRule = rule("p(a,b) -> q");
		RuleTrs secondRule = rule("p(s(X),Y) -> p(X,Y)");
		RuleTrs thirdRule = rule("p(X,s(Y)) -> p(X,Y)");
		String firstBefore = firstRule.toString();
		String secondBefore = secondRule.toString();
		String thirdBefore = thirdRule.toString();

		CorrectPatternRuleTrsProducer.tryBuildPatternRuleFromTwoContextShifts(
				firstRule, secondRule, thirdRule);

		assertEquals(firstBefore, firstRule.toString());
		assertEquals(secondBefore, secondRule.toString());
		assertEquals(thirdBefore, thirdRule.toString());
	}

	/** Asserts that Proposition 9 produces no pattern rule. */
	private void assertProp9Rejected(String firstRule, String secondRule)
			throws IOException {

		Collection<PatternRuleTrs> patternRules =
				CorrectPatternRuleTrsProducer.collectPatternRulesWithProp9Wst25(
						rule(firstRule), rule(secondRule));

		assertTrue(patternRules.isEmpty());
	}

	/** Collects context-shift rules from separately parsed, variable-disjoint rules. */
	private Collection<PatternRuleTrs> collectContextShifts(
			String firstRule, String secondRule) throws IOException {
		return CorrectPatternRuleTrsProducer.collectPatternRulesFromContextShift(
				rule(firstRule), rule(secondRule));
	}

	/** Builds a rule from three separately parsed, variable-disjoint TRS rules. */
	private PatternRuleTrs buildFromTwoContextShifts(
			String firstRule, String secondRule, String thirdRule)
			throws IOException {
		return CorrectPatternRuleTrsProducer.tryBuildPatternRuleFromTwoContextShifts(
				rule(firstRule), rule(secondRule), rule(thirdRule));
	}

	/** Parses a rule with its own variable environment. */
	private RuleTrs rule(String text) throws IOException {
		return parser.parseTrsRule(text, new HashMap<>());
	}

	/** Renders pattern rules with a fresh variable-name map for each rule. */
	private static List<String> render(Collection<PatternRuleTrs> patternRules) {
		List<String> rendered = new ArrayList<>();
		for (PatternRuleTrs patternRule : patternRules)
			rendered.add(patternRule.toString(new HashMap<>()));
		return rendered;
	}
}
