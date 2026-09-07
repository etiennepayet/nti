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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
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
import fr.univreunion.nti.term.Variable;

class DependencyPairProblemCollectionTest {

	@Test
	@DisplayName("deep-copy problems while sharing one copied TRS")
	void deepCopyProblemsWithSharedCopiedTrs() throws IOException {
		DependencyPairProblemCollection original = twoIndependentProblems();
		List<DependencyPairProblem> originalProblems = toList(original);

		DependencyPairProblemCollection copy = original.copy();
		List<DependencyPairProblem> copiedProblems = toList(copy);

		assertEquals(originalProblems.size(), copiedProblems.size());
		assertFalse(copiedProblems.isEmpty());
		Trs copiedTrs = copiedProblems.get(0).getTRS();
		assertNotSame(originalProblems.get(0).getTRS(), copiedTrs);
		for (int i = 0; i < originalProblems.size(); i++) {
			DependencyPairProblem originalProblem = originalProblems.get(i);
			DependencyPairProblem copiedProblem = copiedProblems.get(i);
			assertNotSame(originalProblem, copiedProblem);
			assertSame(copiedTrs, copiedProblem.getTRS());
			assertCopiedRules(
					originalProblem.getDependencyPairs(),
					copiedProblem.getDependencyPairs());
		}
	}

	@Test
	@DisplayName("copy an empty problem collection")
	void copyEmptyCollection() {
		DependencyPairProblemCollection original =
				new DependencyPairProblemCollection();

		DependencyPairProblemCollection copy = original.copy();

		assertNotSame(original, copy);
		assertTrue(copy.isEmpty());
	}

	@Test
	@DisplayName("compute the average dependency-pair count")
	void computeAverageDependencyPairCount() throws IOException {
		Trs trs = parseTrs(
				"f(X) -> f(X)",
				"g(X) -> g(X)",
				"h(X) -> h(X)");
		List<RuleTrs> rules = new ArrayList<>();
		for (RuleTrs rule : trs) rules.add(rule);
		DependencyPairProblemCollection problems =
				new DependencyPairProblemCollection();
		problems.add(new DependencyPairProblem(
				trs, new DependencyPairs(rules.subList(0, 1))));
		problems.add(new DependencyPairProblem(
				trs, new DependencyPairs(rules)));

		assertEquals(2.0f, problems.averageNbOfDependencyPairs());
	}

	@Test
	@DisplayName("add collections in order and clear them independently")
	void addCollectionsInOrderAndClearIndependently() throws IOException {
		DependencyPairProblemCollection source = twoIndependentProblems();
		List<DependencyPairProblem> sourceProblems = toList(source);
		DependencyPairProblemCollection target =
				new DependencyPairProblemCollection();

		assertTrue(target.addAll(source));
		assertEquals(sourceProblems, toList(target));

		source.clear();

		assertTrue(source.isEmpty());
		assertEquals(sourceProblems, toList(target));
		target.clear();
		assertTrue(target.isEmpty());
	}

	private static void assertCopiedRules(
			DependencyPairs original, DependencyPairs copy) {

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
	}

	private static DependencyPairProblemCollection twoIndependentProblems()
			throws IOException {

		Trs trs = parseTrs("f(X) -> f(X)", "g(X) -> g(X)");
		DependencyPairProblemCollection problems =
				new InitialDependencyPairProblemCollector().collectFrom(trs);
		assertEquals(2, problems.size());
		return problems;
	}

	private static List<DependencyPairProblem> toList(
			DependencyPairProblemCollection problems) {

		List<DependencyPairProblem> result = new ArrayList<>();
		for (DependencyPairProblem problem : problems) result.add(problem);
		return result;
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new ArrayList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return new Trs("", rules, "FULL");
	}
}
