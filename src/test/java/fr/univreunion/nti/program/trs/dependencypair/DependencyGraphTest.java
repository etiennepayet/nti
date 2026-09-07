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

package fr.univreunion.nti.program.trs.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CancellationException;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Variable;

class DependencyGraphTest {

	private static final int DENSE_GRAPH_NODE_COUNT = 317;

	@Test
	@DisplayName("build ordered SCCs and retain only their internal arcs")
	void buildOrderedSccsAndRetainOnlyTheirInternalArcs() throws IOException {
		List<RuleTrs> dependencyPairs = parseRules(
				"f(X) -> g(X)",
				"g(X) -> f(X)",
				"h(X) -> h(X)");
		Trs trs = new Trs("", dependencyPairs, "FULL");
		RuleTrs f = dependencyPairs.get(0);
		RuleTrs g = dependencyPairs.get(1);
		RuleTrs h = dependencyPairs.get(2);

		DependencyGraph graph = new DependencyGraph(
				trs, new DependencyPairs(dependencyPairs));

		assertEquals(
				List.of(List.of(h), List.of(f, g)),
				toLists(graph.getSCCs()));
		assertEquals(expectedGraphRendering(dependencyPairs, List.of(
				List.of(g), List.of(f), List.of(h))), graph.toString());
	}

	@Test
	@DisplayName("compute SCCs using only the selected dependency pairs")
	void computeSccsUsingOnlySelectedDependencyPairs() throws IOException {
		List<RuleTrs> dependencyPairs = parseRules(
				"f(X) -> g(X)",
				"g(X) -> f(X)",
				"h(X) -> h(X)");
		Trs trs = new Trs("", dependencyPairs, "FULL");
		DependencyGraph graph = new DependencyGraph(
				trs, new DependencyPairs(dependencyPairs));

		Deque<DependencyPairs> sccs = graph.getSCCs(
				List.of(dependencyPairs.get(0), dependencyPairs.get(2)));

		assertEquals(
				List.of(List.of(dependencyPairs.get(2))),
				toLists(sccs));
	}

	@Test
	@DisplayName("avoid comparisons for guaranteed candidates and retain the fallback")
	void avoidGuaranteedComparisonsAndRetainNonlinearFallback()
			throws IOException {
		List<CountingRuleTrs> countingRules = parseRules(
				"v(X) -> X",
				"f(X) -> f(X)",
				"g(X) -> g(X)",
				"f(s(X)) -> f(X)",
				"h(X, X) -> h(X, X)",
				"k(X, Y) -> h(a(X), b(Y))").stream()
				.map(CountingRuleTrs::new)
				.toList();
		List<RuleTrs> dependencyPairs = new ArrayList<>(countingRules);
		Trs trs = new Trs("", dependencyPairs, "FULL");
		countingRules.forEach(CountingRuleTrs::resetLeftAccessCount);

		new DependencyGraph(trs, new DependencyPairs(dependencyPairs));

		assertEquals(1, countingRules.get(0).leftAccessCount());
		assertEquals(1, countingRules.get(1).leftAccessCount());
		assertEquals(1, countingRules.get(2).leftAccessCount());
		assertEquals(1, countingRules.get(3).leftAccessCount());
		assertEquals(2, countingRules.get(4).leftAccessCount());
		assertEquals(1, countingRules.get(5).leftAccessCount());
	}

	@Test
	@DisplayName("cancel graph construction without publishing a partial graph")
	void cancelGraphConstructionWithoutPublishingPartialGraph()
			throws IOException {
		Trs trs = new Trs("", parseRules("f(X) -> f(X)"), "FULL");

		Thread.currentThread().interrupt();
		try {
			assertThrows(CancellationException.class, trs::getDependencyGraph);
		}
		finally {
			Thread.interrupted();
		}

		assertNotNull(trs.getDependencyGraph());
	}

	@Test
	@DisplayName("abort before retaining more than the approximate arc bound")
	void abortBeforeRetainingMoreThanApproximateArcBound()
			throws IOException {
		List<RuleTrs> dependencyPairs = parseDenseSelfLoops(
				DENSE_GRAPH_NODE_COUNT);
		Trs trs = new Trs("", dependencyPairs, "FULL");

		DependencyGraphLimitException failure = assertThrows(
				DependencyGraphLimitException.class,
				() -> new DependencyGraph(
						trs, new DependencyPairs(dependencyPairs)));

		assertTrue(failure.getMessage().contains("100000 approximate arcs"));
	}

	private static String expectedGraphRendering(
			List<RuleTrs> nodes, List<List<RuleTrs>> successors) {
		StringBuilder result = new StringBuilder("** Nodes:\n");
		StringBuilder arcs = new StringBuilder("** Successors:\n");
		for (int i = 0; i < nodes.size(); i++) {
			RuleTrs node = nodes.get(i);
			String address = address(node);
			result.append(address).append(": ").append(node).append("\n");
			arcs.append(address).append(" -> {");
			for (int j = 0; j < successors.get(i).size(); j++) {
				if (j > 0) arcs.append(", ");
				arcs.append(address(successors.get(i).get(j)));
			}
			arcs.append("}\n");
		}
		return result.append(arcs).toString();
	}

	private static String address(RuleTrs rule) {
		return "@" + Integer.toHexString(System.identityHashCode(rule));
	}

	private static List<List<RuleTrs>> toLists(
			Deque<DependencyPairs> sccs) {
		List<List<RuleTrs>> result = new ArrayList<>();
		for (DependencyPairs scc : sccs)
			result.add(new ArrayList<>(scc.toDeque()));
		return result;
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

	private static List<RuleTrs> parseDenseSelfLoops(int ruleCount)
			throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new ArrayList<>();
		for (int ruleIndex = 0; ruleIndex < ruleCount; ruleIndex++) {
			String variableName = "X" + ruleIndex;
			rules.add(parser.parseTrsRule(
					"f(" + variableName + ") -> f(" + variableName + ")",
					variables));
		}
		return rules;
	}

	private static final class CountingRuleTrs extends RuleTrs {

		private int leftAccessCount;

		private CountingRuleTrs(RuleTrs rule) {
			super(rule.getLeft(), rule.getRight());
		}

		@Override
		public fr.univreunion.nti.term.Function getLeft() {
			this.leftAccessCount++;
			return super.getLeft();
		}

		private void resetLeftAccessCount() {
			this.leftAccessCount = 0;
		}

		private int leftAccessCount() {
			return this.leftAccessCount;
		}
	}
}
