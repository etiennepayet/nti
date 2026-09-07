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

package fr.univreunion.nti.program.trs.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.term.Variable;

class DependencyPairsTest {

	@Test
	@DisplayName("preserve rule order and representation")
	void preserveRuleOrderAndRepresentation() throws IOException {
		List<RuleTrs> rules = parseRules(
				"f(X) -> g(X)", "g(X) -> h(X)");

		DependencyPairs dependencyPairs = new DependencyPairs(rules);

		assertEquals(2, dependencyPairs.size());
		assertTrue(dependencyPairs.contains(rules.get(0)));
		assertTrue(dependencyPairs.contains(rules.get(1)));
		assertEquals(rules, toList(dependencyPairs));
		assertEquals(rules.toString(), dependencyPairs.toString());
	}

	@Test
	@DisplayName("deep-copy rules independently and in order")
	void deepCopyRulesIndependentlyAndInOrder() throws IOException {
		DependencyPairs original = new DependencyPairs(parseRules(
				"f(X) -> g(X)", "g(X) -> h(X)"));

		DependencyPairs copy = original.copy();

		assertNotSame(original, copy);
		assertEquals(original.size(), copy.size());
		Iterator<RuleTrs> originalIterator = original.iterator();
		Iterator<RuleTrs> copyIterator = copy.iterator();
		while (originalIterator.hasNext()) {
			RuleTrs originalRule = originalIterator.next();
			RuleTrs copiedRule = copyIterator.next();
			assertNotSame(originalRule, copiedRule);
			assertEquals(originalRule.toString(), copiedRule.toString());
		}
		assertFalse(copyIterator.hasNext());

		originalIterator = original.iterator();
		originalIterator.next();
		originalIterator.remove();
		assertEquals(1, original.size());
		assertEquals(2, copy.size());
	}

	@Test
	@DisplayName("return an independent deque containing the same rules")
	void returnIndependentDequeContainingSameRules() throws IOException {
		List<RuleTrs> rules = parseRules(
				"f(X) -> g(X)", "g(X) -> h(X)");
		DependencyPairs dependencyPairs = new DependencyPairs(rules);

		Deque<RuleTrs> deque = dependencyPairs.toDeque();

		assertEquals(rules, new ArrayList<>(deque));
		assertSame(rules.get(0), deque.getFirst());
		deque.removeFirst();
		assertEquals(1, deque.size());
		assertEquals(2, dependencyPairs.size());
	}

	@Test
	@DisplayName("convert rules to ordered pairs of their original terms")
	void convertRulesToOrderedPairsOfOriginalTerms() throws IOException {
		List<RuleTrs> rules = parseRules(
				"f(X) -> g(X)", "g(X) -> h(X)");
		DependencyPairs dependencyPairs = new DependencyPairs(rules);

		Collection<PairOfTerms> converted = dependencyPairs.toPairsOfTerms();
		Iterator<PairOfTerms> pairs = converted.iterator();
		for (RuleTrs rule : rules) {
			PairOfTerms pair = pairs.next();
			assertSame(rule, pair.rule());
			assertSame(rule.getLeft(), pair.left());
			assertSame(rule.getRight(), pair.right());
		}
		assertFalse(pairs.hasNext());
	}

	private static List<RuleTrs> toList(DependencyPairs dependencyPairs) {
		List<RuleTrs> rules = new ArrayList<>();
		for (RuleTrs rule : dependencyPairs) rules.add(rule);
		return rules;
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
