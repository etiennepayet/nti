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

package fr.univreunion.nti.program.trs.ruleunfolding.unit;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class UnfoldedRuleTrsUnitTest {

	@Test
	@DisplayName("construct and deeply copy a unit rule")
	void constructAndDeeplyCopyAUnitRule() throws IOException {
		RuleTrs source = parseRule("f(X,X) -> g(X)");
		UnfoldedRuleTrsUnit original = unitRule(source, 0);
		ParentTrsUnit parent = ParentTrsUnit.of(
				original, source, new Position(0), false);

		UnfoldedRuleTrsUnit copy = original.deepCopy(3, parent);

		assertSame(source.getLeft(), original.getLeft());
		assertSame(source.getRight(), original.getRight());
		assertTrue(original.toString().endsWith(" [unit]"));
		assertNotSame(original, copy);
		assertNotSame(original.getLeft(), copy.getLeft());
		assertNotSame(original.getRight(), copy.getRight());
		assertEquals(original.toString(), copy.toString());
		assertEquals(3, copy.getIteration());
		assertSame(parent, copy.getParent());
	}

	@Test
	@DisplayName("deeply copy more variables than the inline workspace capacity")
	void deeplyCopyMoreVariablesThanTheInlineWorkspaceCapacity()
			throws IOException {

		RuleTrs source = parseRule("f(W,X,Y,Z) -> g(Z,Y,X,W)");
		UnfoldedRuleTrsUnit copy = unitRule(source, 0).deepCopy();

		for (int i = 0; i < 4; i++) {
			Term sourceVariable = source.getLeft().get(new Position(i));
			Term copiedVariable = copy.getLeft().get(new Position(i));
			Term copiedOccurrence = copy.getRight().get(new Position(3 - i));

			assertNotSame(sourceVariable, copiedVariable);
			assertSame(copiedVariable, copiedOccurrence);
		}
	}

	@Test
	@DisplayName("recognize only a shallow left-unification witness")
	void recognizeOnlyAShallowLeftUnificationWitness() throws IOException {
		UnfoldedRuleTrsUnit looping = unitRule(parseRule("f(X) -> f(X)"), 0);
		UnfoldedRuleTrsUnit nonLooping = unitRule(parseRule("f(0) -> g(0)"), 0);

		assertNotNull(looping.nonTerminationTest());
		assertNull(nonLooping.nonTerminationTest());
	}

	@Test
	@DisplayName("apply depth, embedding and connectivity elimination checks")
	void applyEliminationChecks() throws IOException {
		UnfoldedRuleTrsUnit retained = unitRule(
				parseRule("f(0) -> f(s(0))"), 0);
		UnfoldedRuleTrsUnit embedding = unitRule(
				parseRule("f(X) -> f(X)"), 0);
		UnfoldedRuleTrsUnit disconnected = unitRule(
				parseRule("f(0) -> g(0)"), 0);
		Parameters parameters = new Parameters();
		Trs trs = connectingTrs();
		SimpleCycleRegistry registry = new SimpleCycleRegistry();

		assertEquals(List.of(retained), retained.elim(parameters, trs, registry));
		assertTrue(embedding.elim(parameters, trs, registry).isEmpty());
		assertTrue(disconnected.elim(parameters, trs, registry).isEmpty());

		parameters.setMaxDepth(retained.depth() - 1);
		assertTrue(retained.elim(parameters, trs, registry).isEmpty());
	}

	@Test
	@DisplayName("unfold the right-hand side forwards")
	void unfoldTheRightHandSideForwards() throws IOException {
		UnfoldedRuleTrsUnit source = unitRule(
				parseRule("f(X) -> h(g(X))"), 0);
		RuleTrs rule = parseRule("g(Y) -> k(Y)");
		Parameters parameters = new Parameters();
		parameters.setVerboseMode(true);

		Collection<UnfoldedRuleTrs> result = source.unfoldForwardsWith(
				parameters, rule, new Position(0), 2);

		assertEquals(1, result.size());
		UnfoldedRuleTrs unfolded = result.iterator().next();
		assertEquals("f(_0) -> h(k(_0)) [unit]", unfolded.toString());
		assertEquals(2, unfolded.getIteration());
		ParentTrsUnit parent = assertInstanceOf(
				ParentTrsUnit.class, unfolded.getParent());
		assertSame(source, parent.getFather());
		assertSame(rule, parent.getMother());
		assertFalse(parent.unfoldsLeftSide());
	}

	@Test
	@DisplayName("unfold the left-hand side backwards")
	void unfoldTheLeftHandSideBackwards() throws IOException {
		UnfoldedRuleTrsUnit source = unitRule(
				parseRule("h(g(X)) -> f(X)"), 0);
		RuleTrs rule = parseRule("k(Y) -> g(Y)");
		Parameters parameters = new Parameters();
		parameters.setVerboseMode(true);

		Collection<UnfoldedRuleTrs> result = source.unfoldBackwardsWith(
				parameters, rule, new Position(0), 2);

		assertEquals(1, result.size());
		UnfoldedRuleTrs unfolded = result.iterator().next();
		assertEquals("h(k(_0)) -> f(_0) [unit]", unfolded.toString());
		assertEquals(2, unfolded.getIteration());
		ParentTrsUnit parent = assertInstanceOf(
				ParentTrsUnit.class, unfolded.getParent());
		assertTrue(parent.unfoldsLeftSide());
	}

	@Test
	@DisplayName("return no rule when direct unfolding cannot apply")
	void returnNoRuleWhenDirectUnfoldingCannotApply() throws IOException {
		UnfoldedRuleTrsUnit source = unitRule(
				parseRule("f(X) -> h(g(X))"), 0);
		RuleTrs unrelated = parseRule("q(Y) -> k(Y)");
		Parameters parameters = new Parameters();

		assertTrue(source.unfoldForwardsWith(
				parameters, unrelated, new Position(0), 1).isEmpty());
		assertTrue(source.unfoldBackwardsWith(
				parameters, unrelated, new Position(0), 1).isEmpty());
	}

	@Test
	@DisplayName("honor variable-position unfolding")
	void honorVariablePositionUnfolding() throws IOException {
		UnfoldedRuleTrsUnit source = unitRule(parseRule("f(X) -> g(X)"), 0);
		RuleTrs rule = parseRule("h(0) -> a");
		Parameters parameters = new Parameters();

		assertTrue(source.unfoldForwardsWith(
				parameters, rule, new Position(0), 1).isEmpty());

		parameters.setVariableUnfolding(true);
		Collection<UnfoldedRuleTrs> result = source.unfoldForwardsWith(
				parameters, rule, new Position(0), 1);
		assertEquals(1, result.size());
		assertEquals("f(h(0)) -> g(a) [unit]", result.iterator().next().toString());
	}

	@Test
	@DisplayName("stop before guided unfolding when interrupted")
	void stopBeforeGuidedUnfoldingWhenInterrupted() throws IOException {
		UnfoldedRuleTrsUnit source = unitRule(
				parseRule("f(g(0)) -> f(h(0))"), 0);
		Trs trs = parseTrs("g(X) -> h(X)", "h(X) -> g(X)");

		Thread.currentThread().interrupt();
		try {
			Collection<UnfoldedRuleTrs> result = source.unfold(
					new Parameters(), trs, new SimpleCycleRegistry(),
					1, new Proof(false));

			assertTrue(result.isEmpty());
			assertTrue(Thread.currentThread().isInterrupted());
		}
		finally {
			Thread.interrupted();
		}
	}

	@Test
	@DisplayName("try forward unfolding before backward unfolding")
	void tryForwardUnfoldingBeforeBackwardUnfolding() throws IOException {
		UnfoldedRuleTrsUnit source = unitRule(
				parseRule("f(g(0)) -> f(h(0))"), 0);
		Trs trs = parseTrs("g(X) -> h(X)", "h(X) -> g(X)");
		Proof proof = new Proof(false);

		Collection<UnfoldedRuleTrs> result = source.unfold(
				new Parameters(), trs, new SimpleCycleRegistry(), 1, proof);

		assertTrue(proof.isSuccess());
		assertEquals(1, result.size());
		assertEquals("f(g(0)) -> f(g(0)) [unit]",
				result.iterator().next().toString());
	}

	private static UnfoldedRuleTrsUnit unitRule(RuleTrs source, int iteration) {
		return new UnfoldedRuleTrsUnit(
				source.getLeft(), source.getRight(), iteration, null, List.of());
	}

	private static Trs connectingTrs() throws IOException {
		return parseTrs("s(X) -> X");
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		return new Trs("", parseRules(ruleTexts), "FULL");
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		return parseRules(ruleText).get(0);
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
