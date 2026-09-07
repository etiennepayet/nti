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

package fr.univreunion.nti.program.trs.ruleunfolding;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.trans.UnfoldedRuleTrsTrans;
import fr.univreunion.nti.term.Variable;

class TrsSyntacticLoopCollectorTest {

	private final TrsSyntacticLoopCollector collector =
			new TrsSyntacticLoopCollector();

	@Test
	@DisplayName("return no initial rule for empty dependency pairs")
	void returnNoInitialRuleForEmptyDependencyPairs() {
		Collection<UnfoldedRuleTrs> result =
				this.collector.collectFrom(new DependencyPairs(List.of()));

		assertTrue(result.isEmpty());
	}

	@Test
	@DisplayName("build an iteration-zero transitory rule for a syntactic loop")
	void buildIterationZeroTransitoryRuleForSyntacticLoop() throws IOException {
		RuleTrs dependencyPair = parseRules("f(X) -> f(X)").get(0);

		Collection<UnfoldedRuleTrs> result = this.collector.collectFrom(
				new DependencyPairs(List.of(dependencyPair)));

		assertEquals(1, result.size());
		UnfoldedRuleTrs unfoldedRule = result.iterator().next();
		assertInstanceOf(UnfoldedRuleTrsTrans.class, unfoldedRule);
		assertEquals(0, unfoldedRule.getIteration());
		assertSame(dependencyPair.getLeft(), unfoldedRule.getLeft());
		assertSame(dependencyPair.getRight(), unfoldedRule.getRight());
		assertNotNull(unfoldedRule.nonTerminationTest());
	}

	@Test
	@DisplayName("preserve dependency-pair and SCC order")
	void preserveDependencyPairAndSccOrder() throws IOException {
		List<RuleTrs> firstSccRules = parseRules(
				"f(X) -> g(X)", "g(X) -> f(X)");
		List<RuleTrs> secondSccRules = parseRules("h(X) -> h(X)");
		List<DependencyPairs> sccs = List.of(
				new DependencyPairs(firstSccRules),
				new DependencyPairs(secondSccRules));

		Collection<UnfoldedRuleTrs> result = this.collector.collectFrom(sccs);

		assertEquals(3, result.size());
		Iterator<UnfoldedRuleTrs> unfoldedRules = result.iterator();
		for (RuleTrs dependencyPair : List.of(
				firstSccRules.get(0), firstSccRules.get(1), secondSccRules.get(0))) {
			UnfoldedRuleTrs unfoldedRule = unfoldedRules.next();
			assertSame(dependencyPair.getLeft(), unfoldedRule.getLeft());
			assertSame(dependencyPair.getRight(), unfoldedRule.getRight());
		}
	}

	@Test
	@DisplayName("collect from the SCCs of a TRS dependency graph")
	void collectFromTheSccsOfATrsDependencyGraph() throws IOException {
		Trs trs = new Trs("", parseRules(
				"f(X) -> g(X)", "g(X) -> f(X)"), "FULL");

		Collection<UnfoldedRuleTrs> fromTrs = this.collector.collectFrom(trs);
		Collection<UnfoldedRuleTrs> fromSccs = this.collector.collectFrom(
				trs.getDependencyGraph().getSCCs());

		assertEquals(render(fromSccs), render(fromTrs));
	}

	private static List<String> render(Collection<UnfoldedRuleTrs> rules) {
		List<String> renderedRules = new ArrayList<>();
		for (UnfoldedRuleTrs rule : rules)
			renderedRules.add(rule.getIteration() + ":" + rule);
		return renderedRules;
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
