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

package fr.univreunion.nti.program.lp.binaryunfolding;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.UnfoldedRuleLp;
import fr.univreunion.nti.term.Variable;

class LpBinaryUnfolderTest {

	@Test
	@DisplayName("accumulate unfolded rules between iterations")
	void accumulateUnfoldedRulesBetweenIterations()
			throws IOException, InterruptedException {

		LpBinaryUnfolder unfolder = new LpBinaryUnfolder(List.of(
				parseRule("p(X) :- q(X)."),
				parseRule("q(X) :- r(X)."),
				parseRule("r(a).")));

		Collection<UnfoldedRuleLp> firstIteration =
				unfolder.unfoldNext(1);
		Collection<UnfoldedRuleLp> secondIteration =
				unfolder.unfoldNext(2);

		assertTrue(containsRule(firstIteration, "q(_0) :- r(_0)"));
		assertTrue(containsRule(firstIteration, "r(a)."));
		assertTrue(containsRule(secondIteration, "q(a)."));
		assertTrue(containsRule(secondIteration, "p(_0) :- r(_0)"));
	}

	@Test
	@DisplayName("preserve candidate order across predicate buckets")
	void preserveCandidateOrderAcrossPredicateBuckets()
			throws IOException, InterruptedException {

		LpBinaryUnfolder unfolder = new LpBinaryUnfolder(List.of(
				parseRule("p(X) :- q(X)."),
				parseRule("q(a)."),
				parseRule("r(c)."),
				parseRule("q(b).")));

		unfolder.unfoldNext(1);

		assertEquals(
				List.of("p(a).", "p(b)."),
				unfolder.unfoldNext(2).stream()
						.map(Object::toString)
						.toList());
	}

	@Test
	@DisplayName("stop unfolding when interrupted")
	void stopUnfoldingWhenInterrupted() throws IOException {
		LpBinaryUnfolder unfolder = new LpBinaryUnfolder(List.of(
				parseRule("p(X) :- q(X).")));

		Thread.currentThread().interrupt();
		try {
			assertThrows(
					InterruptedException.class,
					() -> unfolder.unfoldNext(1));
		}
		finally {
			Thread.interrupted();
		}
	}

	private static RuleLp parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		return parser.parseLpRule(ruleText, variables);
	}

	private static boolean containsRule(
			Collection<UnfoldedRuleLp> rules,
			String expectedRule) {

		for (UnfoldedRuleLp rule : rules)
			if (expectedRule.equals(rule.toString()))
				return true;

		return false;
	}
}
