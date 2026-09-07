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

import java.io.IOException;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Variable;

class DependencyGraphSccComputerTest {

	private final DependencyGraphSccComputer computer =
			new DependencyGraphSccComputer();

	@Test
	@DisplayName("preserve SCC and node order, retain loops and discard acyclic nodes")
	void preserveOrderAndRetainExactlyCyclicComponents() throws IOException {
		List<RuleTrs> rules = parseRules(
				"a(X) -> b(X)",
				"b(X) -> a(X)",
				"c(X) -> c(X)",
				"d(X) -> e(X)",
				"e(X) -> f(X)");
		RuleTrs a = rules.get(0);
		RuleTrs b = rules.get(1);
		RuleTrs c = rules.get(2);
		RuleTrs d = rules.get(3);
		RuleTrs e = rules.get(4);
		Map<RuleTrs, List<RuleTrs>> successors = arcs(
				a, List.of(b),
				b, List.of(a, c),
				c, List.of(c),
				d, List.of(e));
		Map<RuleTrs, List<RuleTrs>> predecessors = arcs(
				a, List.of(b),
				b, List.of(a),
				c, List.of(b, c),
				e, List.of(d));

		Deque<DependencyPairs> sccs = this.computer.compute(
				new DependencyPairs(rules), predecessors, successors);

		assertEquals(List.of(List.of(a, b), List.of(c)), toLists(sccs));
		assertEquals(List.of(a), successors.get(b));
		assertEquals(List.of(c), predecessors.get(c));
		assertEquals(List.of(), successors.get(d));
		assertEquals(List.of(), predecessors.get(e));
	}

	@Test
	@DisplayName("restrict traversal and singleton-loop detection to the subgraph")
	void restrictTraversalToTheSpecifiedSubgraph() throws IOException {
		List<RuleTrs> rules = parseRules(
				"a(X) -> b(X)",
				"b(X) -> c(X)",
				"c(X) -> a(X)",
				"d(X) -> d(X)");
		RuleTrs a = rules.get(0);
		RuleTrs b = rules.get(1);
		RuleTrs c = rules.get(2);
		RuleTrs d = rules.get(3);
		Map<RuleTrs, List<RuleTrs>> successors = arcs(
				a, List.of(b),
				b, List.of(c),
				c, List.of(a),
				d, List.of(d));
		Map<RuleTrs, List<RuleTrs>> predecessors = arcs(
				a, List.of(c),
				b, List.of(a),
				c, List.of(b),
				d, List.of(d));

		Deque<DependencyPairs> sccs = this.computer.compute(
				List.of(a, b, d), predecessors, successors);

		assertEquals(List.of(List.of(d)), toLists(sccs));
	}

	private static Map<RuleTrs, List<RuleTrs>> arcs(Object... entries) {
		Map<RuleTrs, List<RuleTrs>> arcs = new LinkedHashMap<>();
		for (int i = 0; i < entries.length; i += 2) {
			RuleTrs node = (RuleTrs) entries[i];
			@SuppressWarnings("unchecked")
			List<RuleTrs> adjacentNodes = (List<RuleTrs>) entries[i + 1];
			arcs.put(node, new ArrayList<>(adjacentNodes));
		}
		return arcs;
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
}
