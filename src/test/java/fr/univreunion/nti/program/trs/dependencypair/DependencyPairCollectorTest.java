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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class DependencyPairCollectorTest {

	private final DependencyPairCollector collector =
			new DependencyPairCollector();

	@Test
	@DisplayName("preserve TRS rule and right-hand-side position order")
	void preserveRuleAndRightHandSidePositionOrder() throws IOException {
		Trs trs = new Trs("", parseRules(
				"f(X) -> c(g(X),h(k(X)),u(X))",
				"p(X) -> q(r(X))",
				"g(X) -> X",
				"h(X) -> X",
				"k(X) -> X",
				"q(X) -> X",
				"r(X) -> X"), "FULL");

		DependencyPairs dependencyPairs = this.collector.collectFrom(trs);

		assertEquals(List.of(
				"f^#(_0) -> g^#(_0)",
				"f^#(_0) -> h^#(k(_0))",
				"f^#(_0) -> k^#(_0)",
				"p^#(_0) -> q^#(r(_0))",
				"p^#(_0) -> r^#(_0)"), render(dependencyPairs));
	}

	@Test
	@DisplayName("select defined roots and tuple only dependency-pair roots")
	void selectDefinedRootsAndTupleOnlyPairRoots() throws IOException {
		List<RuleTrs> rules = parseRules(
				"f(g(X)) -> c(g(h(X)),u(X))",
				"g(X) -> X",
				"h(X) -> X");
		Trs trs = new Trs("", rules, "FULL");

		DependencyPairs dependencyPairs = this.collector.collectFrom(trs);

		assertEquals(2, dependencyPairs.size());
		RuleTrs first = dependencyPairs.iterator().next();
		assertTrue(first.getLeft().getRootSymbol().isTupleSymbol());
		assertTrue(first.getRight().getRootSymbol().isTupleSymbol());
		Term leftArgument = ((Function) first.getLeft()).getChild(0);
		Term rightArgument = ((Function) first.getRight()).getChild(0);
		assertFalse(leftArgument.getRootSymbol().isTupleSymbol());
		assertFalse(rightArgument.getRootSymbol().isTupleSymbol());
		assertSame(((Function) rules.get(0).getLeft()).getChild(0), leftArgument);
		Term originalRightArgument = ((Function)
				((Function) rules.get(0).getRight()).getChild(0)).getChild(0);
		assertSame(originalRightArgument, rightArgument);
	}

	@Test
	@DisplayName("return no dependency pair when no right-hand-side root is defined")
	void returnNoPairWithoutDefinedRightHandSideRoot() throws IOException {
		Trs trs = new Trs("", parseRules("f(X) -> c(u(X),v(X))"), "FULL");

		DependencyPairs dependencyPairs = this.collector.collectFrom(trs);

		assertEquals(0, dependencyPairs.size());
	}

	private static List<String> render(DependencyPairs dependencyPairs) {
		List<String> result = new ArrayList<>();
		for (RuleTrs dependencyPair : dependencyPairs)
			result.add(dependencyPair.toString());
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
