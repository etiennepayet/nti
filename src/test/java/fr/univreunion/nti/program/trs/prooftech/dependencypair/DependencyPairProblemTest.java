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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Variable;

class DependencyPairProblemTest {

	@Test
	@DisplayName("deep-copy a problem with a complete TRS")
	void deepCopyProblemWithCompleteTrs() throws IOException {
		DependencyPairProblem original = problem();

		DependencyPairProblem copy = original.copy();

		assertEquals(original.toString(), copy.toString());
		assertNotNull(copy.getTRS().getDependencyGraph());
		assertIndependentProblemCopy(original, copy);
	}

	@Test
	@DisplayName("shallow-copy a problem without rebuilding the TRS dependency graph")
	void shallowCopyProblemWithoutDependencyGraph() throws IOException {
		DependencyPairProblem original = problem();

		DependencyPairProblem copy = original.shallowCopy();

		assertEquals(original.toString(), copy.toString());
		assertNull(copy.getTRS().getDependencyGraph());
		assertIndependentProblemCopy(original, copy);
	}

	private static void assertIndependentProblemCopy(
			DependencyPairProblem original, DependencyPairProblem copy) {

		assertNotSame(original, copy);
		assertNotSame(original.getTRS(), copy.getTRS());
		assertCopiedRules(original.getTRS(), copy.getTRS());
		assertCopiedRules(
				original.getDependencyPairs(), copy.getDependencyPairs());
		assertEquals(original.nbDependencyPairs(), copy.nbDependencyPairs());

		Iterator<RuleTrs> originalPairs =
				original.getDependencyPairs().iterator();
		originalPairs.next();
		originalPairs.remove();

		assertEquals(0, original.nbDependencyPairs());
		assertEquals(1, copy.nbDependencyPairs());
	}

	private static void assertCopiedRules(
			Iterable<RuleTrs> original, Iterable<RuleTrs> copy) {

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

	private static DependencyPairProblem problem() throws IOException {
		Trs trs = parseTrs("f(s(X)) -> f(X)");
		return new InitialDependencyPairProblemCollector()
				.collectFrom(trs).iterator().next();
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
