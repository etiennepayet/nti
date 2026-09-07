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

package fr.univreunion.nti.program.trs.ruleunfolding.trans;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.program.trs.ruleunfolding.comp.UnfoldedRuleTrsComp;
import fr.univreunion.nti.program.trs.ruleunfolding.unit.UnfoldedRuleTrsUnit;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Variable;

class UnfoldedRuleTrsTransTest {

	@Test
	@DisplayName("build one iteration-zero transitory rule")
	void buildOneIterationZeroTransitoryRule() throws IOException {
		RuleTrs source = parseRule("f(X) -> g(X)");

		Collection<UnfoldedRuleTrs> result = instances(source, 0, List.of(), List.of());

		assertEquals(1, result.size());
		UnfoldedRuleTrsTrans transitoryRule =
				assertInstanceOf(UnfoldedRuleTrsTrans.class, result.iterator().next());
		assertSame(source.getLeft(), transitoryRule.getLeft());
		assertSame(source.getRight(), transitoryRule.getRight());
		assertEquals(0, transitoryRule.getIteration());
		assertTrue(transitoryRule.toString().endsWith(" [trans]"));
	}

	@Test
	@DisplayName("deep-copy terms while replacing iteration and parent")
	void deepCopyTermsWhileReplacingIterationAndParent() throws IOException {
		UnfoldedRuleTrsTrans original = transitoryRule(
				parseRule("f(X,X) -> g(X)"), 0, List.of(), List.of());
		ParentTrsTrans parent = ParentTrsTrans.of(original, null, null, false);

		UnfoldedRuleTrsTrans copy = original.deepCopy(3, parent);

		assertNotSame(original, copy);
		assertNotSame(original.getLeft(), copy.getLeft());
		assertNotSame(original.getRight(), copy.getRight());
		assertEquals(original.toString(), copy.toString());
		assertEquals(3, copy.getIteration());
		assertSame(parent, copy.getParent());
	}

	@Test
	@DisplayName("recognize only a shallow left-unification witness")
	void recognizeOnlyAShallowLeftUnificationWitness() throws IOException {
		UnfoldedRuleTrsTrans looping = transitoryRule(
				parseRule("f(X) -> f(X)"), 0, List.of(), List.of());
		UnfoldedRuleTrsTrans nonLooping = transitoryRule(
				parseRule("f(0) -> g(0)"), 0, List.of(), List.of());

		assertNotNull(looping.nonTerminationTest());
		assertNull(nonLooping.nonTerminationTest());
	}

	@Test
	@DisplayName("retain a transitory rule with remaining dependency pairs")
	void retainRuleWithRemainingDependencyPairsUnlessTooDeep() throws IOException {
		RuleTrs source = parseRule("f(s(0)) -> g(s(0))");
		RuleTrs remaining = parseRule("h(X) -> h(X)");
		UnfoldedRuleTrsTrans rule = transitoryRule(
				source, 0, List.of(remaining), List.of(source));
		Parameters parameters = new Parameters();
		Trs trs = emptyTrs();

		assertEquals(List.of(rule),
				rule.elim(parameters, trs, new SimpleCycleRegistry()));

		parameters.setMaxDepth(rule.depth() - 1);
		assertTrue(rule.elim(parameters, trs, new SimpleCycleRegistry()).isEmpty());
	}

	@Test
	@DisplayName("apply embedding, connectivity and cycle checks without an SCC")
	void applyEliminationChecksWithoutAnScc() throws IOException {
		RuleTrs retainedSource = parseRule("f(0) -> f(s(0))");
		UnfoldedRuleTrsTrans retained = transitoryRule(
				retainedSource, 0, List.of(), List.of(retainedSource));
		UnfoldedRuleTrsTrans embedding = transitoryRule(
				parseRule("f(X) -> f(X)"), 0, List.of(), List.of());
		UnfoldedRuleTrsTrans disconnected = transitoryRule(
				parseRule("f(0) -> g(0)"), 0, List.of(), List.of());
		Parameters parameters = new Parameters();
		Trs trs = connectingTrs();
		SimpleCycleRegistry registry = new SimpleCycleRegistry();

		assertEquals(List.of(retained), retained.elim(parameters, trs, registry));
		assertTrue(embedding.elim(parameters, trs, registry).isEmpty());
		assertTrue(disconnected.elim(parameters, trs, registry).isEmpty());

		registry.add(Set.of(retainedSource));
		assertTrue(retained.elim(parameters, trs, registry).isEmpty());
	}

	@Test
	@DisplayName("reject direct forward and backward unfolding")
	void rejectDirectForwardAndBackwardUnfolding() throws IOException {
		RuleTrs source = parseRule("f(X) -> g(X)");
		UnfoldedRuleTrsTrans rule = transitoryRule(
				source, 0, List.of(), List.of());
		Parameters parameters = new Parameters();
		Position root = new Position();

		assertThrows(UnsupportedOperationException.class,
				() -> rule.unfoldForwardsWith(parameters, source, root, 1));
		assertThrows(UnsupportedOperationException.class,
				() -> rule.unfoldBackwardsWith(parameters, source, root, 1));
	}

	@Test
	@DisplayName("convert an exhausted transitory rule into one unit rule")
	void convertAnExhaustedTransitoryRuleIntoOneUnitRule() throws IOException {
		UnfoldedRuleTrsTrans rule = transitoryRule(
				parseRule("f(0) -> f(s(0))"), 0, List.of(), List.of());
		SimpleCycleRegistry registry = new SimpleCycleRegistry();

		Trs trs = connectingTrs();
		Collection<UnfoldedRuleTrs> result = rule.unfold(
				new Parameters(), trs, registry, 1, null);

		assertEquals(1, result.size());
		UnfoldedRuleTrs unitRule = result.iterator().next();
		assertInstanceOf(UnfoldedRuleTrsUnit.class, unitRule);
		assertEquals(1, unitRule.getIteration());
		assertTrue(rule.unfold(
				new Parameters(), trs, registry, 1, null).isEmpty());
	}

	@Test
	@DisplayName("preserve composed-rule order for the unfolding strategy")
	void preserveComposedRuleOrderForTheUnfoldingStrategy() throws IOException {
		RuleTrs source = parseRule("f(0) -> f(s(0))");
		RuleTrs remaining = parseRule("f(s(0)) -> f(0)");
		Parameters defaultParameters = new Parameters();
		Parameters allParameters = new Parameters();
		allParameters.setStrategy(StrategyLoop.ALL);
		Trs trs = connectingTrs();

		List<Class<?>> defaultTypes = types(transitoryRule(
				source, 0, List.of(remaining), List.of(source)).unfold(
						defaultParameters, trs, new SimpleCycleRegistry(), 1, null));
		List<Class<?>> allTypes = types(transitoryRule(
				source, 0, List.of(remaining), List.of(source)).unfold(
						allParameters, trs, new SimpleCycleRegistry(), 1, null));

		assertEquals(List.of(UnfoldedRuleTrsComp.class, UnfoldedRuleTrsUnit.class),
				defaultTypes);
		assertEquals(List.of(
				UnfoldedRuleTrsComp.class,
				UnfoldedRuleTrsComp.class,
				UnfoldedRuleTrsUnit.class), allTypes);
	}

	private static List<Class<?>> types(Collection<UnfoldedRuleTrs> rules) {
		List<Class<?>> types = new ArrayList<>();
		for (UnfoldedRuleTrs rule : rules) types.add(rule.getClass());
		return types;
	}

	private static UnfoldedRuleTrsTrans transitoryRule(
			RuleTrs source, int iteration, Collection<RuleTrs> scc,
			Collection<RuleTrs> simpleCycle) {

		Iterator<UnfoldedRuleTrs> rules =
				instances(source, iteration, scc, simpleCycle).iterator();
		return (UnfoldedRuleTrsTrans) rules.next();
	}

	private static Collection<UnfoldedRuleTrs> instances(
			RuleTrs source, int iteration, Collection<RuleTrs> scc,
			Collection<RuleTrs> simpleCycle) {

		return UnfoldedRuleTrsTrans.getUnfoldedInstances(
				source.getLeft(), source.getRight(), iteration, null,
				scc, simpleCycle);
	}

	private static Trs emptyTrs() {
		return new Trs("", List.of(), "FULL");
	}

	private static Trs connectingTrs() throws IOException {
		return new Trs("", List.of(parseRule("s(X) -> X")), "FULL");
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		return parser.parseTrsRule(ruleText, variables);
	}
}
