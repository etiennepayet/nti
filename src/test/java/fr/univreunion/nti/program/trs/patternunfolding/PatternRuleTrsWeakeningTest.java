/*
 * Copyright 2025 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.patternunfolding;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class PatternRuleTrsWeakeningTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void keepsOriginalFirstThenAddsFunctionWeakening() throws IOException {
		PatternRuleTrs rule = rule(
				"gt(X,Y){X->s(X),Y->s(Y)}{X->s(X),Y->0}",
				"true{}{}",
				2);
		SimplePatternTerm patternTerm = patternTerm(
				"gt(X1,Y1){X1->s(X1)}{X1->s(0),Y1->0}");

		Collection<PatternRuleTrs> weakened =
				rule.weaken(rule.getLeft(), patternTerm);

		assertEquals(
				List.of(
						"gt(hat[s(□)]^[1, 1](_0),hat[s(□)]^[1, 0](0)) -> true:?",
						"gt(s(_0),0) -> true:?"),
				render(weakened));
		assertSame(rule, weakened.iterator().next());
		assertEquals(2, new ArrayList<>(weakened).get(1).getIteration());
	}

	@Test
	void keepsOriginalFirstThenAddsHatWeakeningsInOrder() throws IOException {
		PatternRuleTrs rule = rule(
				"gt(X1,Y1){X1->s(X1)}{X1->0,Y1->0}",
				"true{}{}",
				3);
		SimplePatternTerm patternTerm = patternTerm(
				"gt(X,Y){X->s(X),Y->s(Y)}{X->s(X),Y->0}");

		Collection<PatternRuleTrs> weakened =
				rule.weaken(rule.getLeft(), patternTerm);

		assertEquals(
				List.of(
						"gt(hat[s(□)]^[1, 0](0),0) -> true:?",
						"gt(hat[s(□)]^[1, 1](0),0) -> true:?",
						"gt(hat[s(□)]^[1, 1, 1](0),0) -> true:?"),
				render(weakened));
		assertSame(rule, weakened.iterator().next());
	}

	@Test
	void keepsOnlyOriginalForMissingOrWrongArityTerms() throws IOException {
		PatternRuleTrs rule = rule("f(X){}{}", "g(X){}{}", 0);
		SimplePatternTerm wrongArity = patternTerm("f(X){X->s(X)}{X->0}");

		assertOnlyOriginal(rule, rule.weaken(null, wrongArity));
		assertOnlyOriginal(rule, rule.weaken(rule.getLeft(), null));
		assertOnlyOriginal(rule, rule.weaken(rule.getLeft(), wrongArity));
	}

	/** Asserts that weakening returned the original rule only. */
	private static void assertOnlyOriginal(
			PatternRuleTrs rule,
			Collection<PatternRuleTrs> weakened) {

		assertEquals(1, weakened.size());
		assertSame(rule, weakened.iterator().next());
	}

	/** Renders rules with a fresh, stable variable-name map for each rule. */
	private static List<String> render(Collection<PatternRuleTrs> rules) {
		List<String> rendered = new ArrayList<>();
		for (PatternRuleTrs rule : rules)
			rendered.add(rule.toString(new HashMap<>()));
		return rendered;
	}

	/** Builds a pattern rule from textual simple pattern terms. */
	private PatternRuleTrs rule(
			String left,
			String right,
			int iteration) throws IOException {

		return PatternRuleTrs.tryBuild(
				patternTerm(left),
				patternTerm(right),
				iteration);
	}

	/** Parses one textual simple pattern term. */
	private SimplePatternTerm patternTerm(String text) throws IOException {
		return parser.parseSimplePatternTerm(text, variables);
	}
}
