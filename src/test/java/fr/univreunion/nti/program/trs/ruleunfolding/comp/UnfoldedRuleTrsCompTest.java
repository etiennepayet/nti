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

package fr.univreunion.nti.program.trs.ruleunfolding.comp;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.program.trs.ruleunfolding.trans.UnfoldedRuleTrsTrans;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Variable;

class UnfoldedRuleTrsCompTest {

	@Test
	@DisplayName("build only a composed rule when its rules cannot be merged")
	void buildOnlyAComposedRuleWhenRulesCannotBeMerged() throws IOException {
		RuleTrs first = parseRule("f(X) -> g(X)");
		RuleTrs second = parseRule("h(Y) -> k(Y)");

		Collection<UnfoldedRuleTrs> result = instances(
				first, second, 0, List.of(), List.of());

		assertEquals(1, result.size());
		UnfoldedRuleTrsComp composed =
				assertInstanceOf(UnfoldedRuleTrsComp.class, result.iterator().next());
		assertSame(second, composed.getSecond());
		assertEquals(0, composed.getIteration());
	}

	@Test
	@DisplayName("build a composed rule before its merged transitory rule")
	void buildComposedRuleBeforeMergedTransitoryRule() throws IOException {
		RuleTrs first = parseRule("f(X) -> g(X)");
		RuleTrs second = parseRule("g(Y) -> h(Y)");

		Iterator<UnfoldedRuleTrs> result = instances(
				first, second, 2, List.of(), List.of()).iterator();

		UnfoldedRuleTrs composed = result.next();
		UnfoldedRuleTrs merged = result.next();
		assertInstanceOf(UnfoldedRuleTrsComp.class, composed);
		assertInstanceOf(UnfoldedRuleTrsTrans.class, merged);
		assertEquals("f(_0) -> h(_0) [trans]", merged.toString());
		assertEquals(2, merged.getIteration());
		assertFalse(result.hasNext());
	}

	@Test
	@DisplayName("expose the two rules and deeply copy the composed triple")
	void exposeRulesAndDeeplyCopyTheComposedTriple() throws IOException {
		RuleTrs first = parseRule("f(X,X) -> g(X)");
		RuleTrs second = parseRule("h(Y) -> k(s(Y))");
		UnfoldedRuleTrsComp original = composedRule(
				first, second, 0, List.of(), List.of());
		ParentTrsComp parent = ParentTrsComp.of(
				original, second, new Position(0), false);

		RuleTrs exposedFirst = original.getFirst();
		UnfoldedRuleTrsComp copy = original.deepCopy(4, parent);

		assertNotSame(original, exposedFirst);
		assertSame(original.getLeft(), exposedFirst.getLeft());
		assertSame(original.getRight(), exposedFirst.getRight());
		assertSame(second, original.getSecond());
		assertTrue(original.toString().startsWith("[f(_0,_0) -> g(_0), "));
		assertTrue(original.toString().endsWith("] [comp]"));

		assertNotSame(original, copy);
		assertNotSame(original.getLeft(), copy.getLeft());
		assertNotSame(original.getRight(), copy.getRight());
		assertNotSame(original.getSecond(), copy.getSecond());
		assertEquals(original.toString(), copy.toString());
		assertEquals(original.depth(), copy.depth());
		assertEquals(4, copy.getIteration());
		assertSame(parent, copy.getParent());
	}

	@Test
	@DisplayName("reject a null second rule")
	void rejectANullSecondRule() throws IOException {
		RuleTrs first = parseRule("f(X) -> g(X)");

		assertThrows(IllegalArgumentException.class, () -> instances(
				first, null, 0, List.of(), List.of()));
	}

	@Test
	@DisplayName("prefer shallow loop detection before recurrent-pair search")
	void detectAShallowLoopAndRejectAnUnrelatedPair() throws IOException {
		UnfoldedRuleTrsComp looping = composedRule(
				parseRule("f(X) -> f(X)"),
				parseRule("g(Y) -> h(Y)"), 0, List.of(), List.of());
		UnfoldedRuleTrsComp unrelated = composedRule(
				parseRule("f(0) -> g(0)"),
				parseRule("h(0) -> k(0)"), 0, List.of(), List.of());

		assertNotNull(looping.nonTerminationTest());
		assertNull(unrelated.nonTerminationTest());
	}

	@Test
	@DisplayName("apply depth, SCC, cycle and connectivity elimination checks")
	void applyEliminationChecks() throws IOException {
		RuleTrs first = parseRule("f(0) -> g(s(0))");
		RuleTrs second = parseRule("g(0) -> h(0)");
		RuleTrs cycleRule = parseRule("c(X) -> c(X)");
		RuleTrs remaining = parseRule("r(X) -> r(X)");
		UnfoldedRuleTrsComp retained = composedRule(
				first, second, 0, List.of(), List.of(cycleRule));
		UnfoldedRuleTrsComp withRemainingScc = composedRule(
				first, second, 0, List.of(remaining), List.of(cycleRule));
		UnfoldedRuleTrsComp disconnected = composedRule(
				first, parseRule("q(0) -> h(0)"),
				0, List.of(), List.of());
		Parameters parameters = new Parameters();
		Trs trs = connectingTrs();
		SimpleCycleRegistry registry = new SimpleCycleRegistry();

		assertEquals(List.of(retained), retained.elim(parameters, trs, registry));
		assertTrue(disconnected.elim(parameters, trs, registry).isEmpty());

		registry.add(Set.of(cycleRule));
		assertTrue(retained.elim(parameters, trs, registry).isEmpty());
		assertEquals(List.of(withRemainingScc),
				withRemainingScc.elim(parameters, trs, registry));

		parameters.setMaxDepth(withRemainingScc.depth() - 1);
		assertTrue(withRemainingScc.elim(parameters, trs, registry).isEmpty());
	}

	@Test
	@DisplayName("unfold the first rule forwards before merging the two rules")
	void unfoldFirstRuleForwardsBeforeMerging() throws IOException {
		UnfoldedRuleTrsComp source = composedRule(
				parseRule("f(X) -> h(g(X))"),
				parseRule("h(k(Y)) -> m(Y)"), 0, List.of(), List.of());
		RuleTrs unfoldingRule = parseRule("g(Z) -> k(Z)");
		Parameters parameters = new Parameters();
		parameters.setVerboseMode(true);

		Iterator<UnfoldedRuleTrs> result = source.unfoldForwardsWith(
				parameters, unfoldingRule, new Position(0), 2).iterator();

		UnfoldedRuleTrsComp composed =
				assertInstanceOf(UnfoldedRuleTrsComp.class, result.next());
		UnfoldedRuleTrsTrans merged =
				assertInstanceOf(UnfoldedRuleTrsTrans.class, result.next());
		assertEquals("[f(_0) -> h(k(_0)), h(k(_1)) -> m(_1)] [comp]",
				composed.toString());
		assertEquals("f(_0) -> m(_0) [trans]", merged.toString());
		assertEquals(2, composed.getIteration());
		ParentTrsComp parent = assertInstanceOf(
				ParentTrsComp.class, composed.getParent());
		assertSame(source, parent.getFather());
		assertSame(unfoldingRule, parent.getMother());
		assertFalse(parent.unfoldsLeftSide());
		assertSame(parent, merged.getParent());
		assertFalse(result.hasNext());
	}

	@Test
	@DisplayName("unfold the second rule backwards")
	void unfoldSecondRuleBackwards() throws IOException {
		UnfoldedRuleTrsComp source = composedRule(
				parseRule("f(X) -> q(X)"),
				parseRule("h(g(Y)) -> m(Y)"), 0, List.of(), List.of());
		RuleTrs unfoldingRule = parseRule("k(Z) -> g(Z)");
		Parameters parameters = new Parameters();
		parameters.setVerboseMode(true);

		Collection<UnfoldedRuleTrs> result = source.unfoldBackwardsWith(
				parameters, unfoldingRule, new Position(0), 2);

		assertEquals(1, result.size());
		UnfoldedRuleTrsComp unfolded = assertInstanceOf(
				UnfoldedRuleTrsComp.class, result.iterator().next());
		assertEquals("[f(_0) -> q(_0), h(k(_1)) -> m(_1)] [comp]",
				unfolded.toString());
		assertEquals(2, unfolded.getIteration());
		ParentTrsComp parent = assertInstanceOf(
				ParentTrsComp.class, unfolded.getParent());
		assertTrue(parent.unfoldsLeftSide());
	}

	@Test
	@DisplayName("return no rule when direct unfolding cannot apply")
	void returnNoRuleWhenDirectUnfoldingCannotApply() throws IOException {
		UnfoldedRuleTrsComp source = composedRule(
				parseRule("f(X) -> h(g(X))"),
				parseRule("q(k(Y)) -> m(Y)"), 0, List.of(), List.of());
		RuleTrs unrelated = parseRule("u(Z) -> v(Z)");
		Parameters parameters = new Parameters();

		assertTrue(source.unfoldForwardsWith(
				parameters, unrelated, new Position(0), 1).isEmpty());
		assertTrue(source.unfoldBackwardsWith(
				parameters, unrelated, new Position(0), 1).isEmpty());
	}

	@Test
	@DisplayName("honor variable-position unfolding in both composed rules")
	void honorVariablePositionUnfolding() throws IOException {
		UnfoldedRuleTrsComp source = composedRule(
				parseRule("f(X) -> g(X)"),
				parseRule("q(Y) -> r(Y)"), 0, List.of(), List.of());
		RuleTrs unfoldingRule = parseRule("h(0) -> a");
		Parameters parameters = new Parameters();

		assertTrue(source.unfoldForwardsWith(
				parameters, unfoldingRule, new Position(0), 1).isEmpty());
		assertTrue(source.unfoldBackwardsWith(
				parameters, unfoldingRule, new Position(0), 1).isEmpty());

		parameters.setVariableUnfolding(true);
		UnfoldedRuleTrsComp forwards = assertInstanceOf(
				UnfoldedRuleTrsComp.class,
				source.unfoldForwardsWith(parameters, unfoldingRule,
						new Position(0), 1).iterator().next());
		UnfoldedRuleTrsComp backwards = assertInstanceOf(
				UnfoldedRuleTrsComp.class,
				source.unfoldBackwardsWith(parameters, unfoldingRule,
						new Position(0), 1).iterator().next());
		assertEquals("[f(h(0)) -> g(a), q(_0) -> r(_0)] [comp]",
				forwards.toString());
		assertEquals("[f(_0) -> g(_0), q(h(0)) -> r(a)] [comp]",
				backwards.toString());
	}

	@Test
	@DisplayName("apply LEFTMOST, LEFTMOST_NE and ALL disagreement strategies")
	void applyDisagreementStrategies() throws IOException {
		UnfoldedRuleTrsComp source = composedRule(
				parseRule("f(a,k(0)) -> f(a,g(0))"),
				parseRule("f(b,k(0)) -> m(0)"), 0, List.of(), List.of());
		Trs trs = parseTrs("g(X) -> k(X)", "k(X) -> g(X)");

		Proof leftmostProof = new Proof(false);
		Collection<UnfoldedRuleTrs> leftmost = source.unfold(
				parameters(StrategyLoop.LEFTMOST), trs,
				new SimpleCycleRegistry(), 1, leftmostProof);
		Proof leftmostNeProof = new Proof(false);
		Collection<UnfoldedRuleTrs> leftmostNe = source.unfold(
				parameters(StrategyLoop.LEFTMOST_NE), trs,
				new SimpleCycleRegistry(), 1, leftmostNeProof);
		Proof allProof = new Proof(false);
		Collection<UnfoldedRuleTrs> all = source.unfold(
				parameters(StrategyLoop.ALL), trs,
				new SimpleCycleRegistry(), 1, allProof);

		assertTrue(leftmost.isEmpty());
		assertFalse(leftmostProof.isSuccess());
		assertEquals(1, leftmostNe.size());
		assertTrue(leftmostNeProof.isSuccess());
		assertEquals("[f(a,k(0)) -> f(a,k(0)), f(b,k(0)) -> m(0)] [comp]",
				leftmostNe.iterator().next().toString());
		assertEquals(1, all.size());
		assertTrue(allProof.isSuccess());
	}

	@Test
	@DisplayName("stop guided unfolding when interrupted")
	void stopGuidedUnfoldingWhenInterrupted() throws IOException {
		UnfoldedRuleTrsComp source = composedRule(
				parseRule("f(0) -> h(g(0))"),
				parseRule("h(k(0)) -> m(0)"), 0, List.of(), List.of());
		Trs trs = parseTrs("g(X) -> k(X)", "k(X) -> g(X)");

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

	private static UnfoldedRuleTrsComp composedRule(
			RuleTrs first, RuleTrs second, int iteration,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		return (UnfoldedRuleTrsComp) instances(
				first, second, iteration, scc, simpleCycle).iterator().next();
	}

	private static Collection<UnfoldedRuleTrs> instances(
			RuleTrs first, RuleTrs second, int iteration,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		return UnfoldedRuleTrsComp.getInstances(
				first.getLeft(), first.getRight(), iteration, null,
				second, scc, simpleCycle);
	}

	private static Trs connectingTrs() throws IOException {
		return new Trs("", List.of(parseRule("s(X) -> X")), "FULL");
	}

	private static Parameters parameters(StrategyLoop strategy) {
		Parameters parameters = new Parameters();
		parameters.setStrategy(strategy);
		return parameters;
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new ArrayList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return new Trs("", rules, "FULL");
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		return parser.parseTrsRule(ruleText, variables);
	}
}
