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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.argument.ArgumentIclp25;
import fr.univreunion.nti.term.Variable;

class PatternRuleTrsUnfoldTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void preservesPositionThenRuleOrder() throws IOException {
		PatternRuleTrs source = rule("f(X){}{}", "g(h(X),q(X)){}{}", 0);
		PatternRuleTrs hRule = rule("h(Y){}{}", "a(Y){}{}", 0);
		PatternRuleTrs qRule = rule("q(Z){}{}", "b(Z){}{}", 0);

		Collection<PatternRuleTrs> unfolded =
				source.unfold(List.of(hRule, qRule), 4, null);

		List<String> rendered = new ArrayList<>();
		for (PatternRuleTrs rule : unfolded)
			rendered.add(rule.toString(new HashMap<>()));
		assertEquals(
				List.of(
						"f(_0) -> g(a(_0),q(_0)):?",
						"f(_0) -> g(h(_0),b(_0)):?"),
				rendered);
	}

	@Test
	void stopsImmediatelyWithoutClearingInterruption() throws IOException {
		PatternRuleTrs source = rule("f(X){}{}", "g(h(X)){}{}", 0);
		PatternRuleTrs unfoldingRule = rule("h(Y){}{}", "k(Y){}{}", 0);

		Thread.currentThread().interrupt();
		try {
			Collection<PatternRuleTrs> unfolded =
					source.unfold(List.of(unfoldingRule), 1, null);

			assertTrue(unfolded.isEmpty());
			assertTrue(Thread.currentThread().isInterrupted());
		}
		finally {
			Thread.interrupted();
		}
	}

	@Test
	void stopsAtFirstNonTerminationWitnessAndUpdatesProof() throws IOException {
		PatternRuleTrs source = rule("p(X){}{}", "h(X){}{}", 0);
		PatternRuleTrs firstRule = rule("h(Y){}{}", "p(Y){}{}", 0);
		PatternRuleTrs secondRule = rule("h(Z){}{}", "p(Z){}{}", 0);
		Proof proof = new Proof(false);

		Collection<PatternRuleTrs> unfolded =
				source.unfold(List.of(firstRule, secondRule), 3, proof);

		assertEquals(1, unfolded.size());
		PatternRuleTrs witness = unfolded.iterator().next();
		assertEquals(0, witness.getAlpha());
		assertEquals("p(0)", witness.getNonTerminatingTerm().toString());
		assertInstanceOf(ArgumentIclp25.class, proof.getArgument());
	}

	@Test
	void preservesUnfoldingOfDistinctWeakenedSources() throws IOException {
		PatternRuleTrs source = rule(
				"p(X){X->s(X)}{X->0}",
				"gt(X,Y){X->s(X),Y->s(Y)}{X->s(X),Y->0}",
				0);
		PatternRuleTrs unfoldingRule = rule(
				"gt(X1,Y1){X1->s(X1)}{X1->s(0),Y1->0}",
				"true{}{}",
				0);

		Collection<PatternRuleTrs> unfolded =
				source.unfold(List.of(unfoldingRule), 3, null);
		List<String> rendered = new ArrayList<>();
		for (PatternRuleTrs rule : unfolded)
			rendered.add(rule.toString(new HashMap<>()));

		assertEquals(List.of("p(0) -> true:?"), rendered);
	}

	/** Builds a pattern rule from textual simple pattern terms. */
	private PatternRuleTrs rule(
			String left,
			String right,
			int iteration) throws IOException {

		return PatternRuleTrs.tryBuild(
				parser.parseSimplePatternTerm(left, variables),
				parser.parseSimplePatternTerm(right, variables),
				iteration);
	}
}
