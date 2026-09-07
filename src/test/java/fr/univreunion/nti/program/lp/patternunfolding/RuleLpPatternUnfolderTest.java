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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.lp.patternunfolding;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.AbstractCollection;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.term.Variable;

class RuleLpPatternUnfolderTest {

	private final ParserString parser = new ParserString();

	@Test
	void rejectsNonPositiveIterations() throws IOException {
		RuleLp sourceRule = lpRule("p(X) :- q(X).");

		assertThrows(
				IllegalArgumentException.class,
				() -> RuleLpPatternUnfolder.unfold(sourceRule, List.of(), 0));
		assertThrows(
				IllegalArgumentException.class,
				() -> RuleLpPatternUnfolder.unfold(sourceRule, List.of(), -1));
	}

	@Test
	void preservesIdentityThenCandidateOrder() throws IOException {
		RuleLp sourceRule = lpRule("p(X) :- q(X).");
		PatternRuleLp firstCandidate = patternRule(
				"q(Y){}{}", "a(Y){}{}", 0);
		PatternRuleLp nonMatchingCandidate = patternRule(
				"r(Y){}{}", "c(Y){}{}", 0);
		PatternRuleLp secondCandidate = patternRule(
				"q(Z){}{}", "b(Z){}{}", 0);

		Collection<PatternRuleLp> unfolded = RuleLpPatternUnfolder.unfold(
				sourceRule,
				List.of(firstCandidate, nonMatchingCandidate, secondCandidate),
				1);

		assertEquals(
				List.of(
						"p(_0) :- q(_0)",
						"p(_0) :- a(_0)",
						"p(_0) :- b(_0)"),
				render(unfolded));
	}

	@Test
	void carriesFactUnfoldingToNextBodyAtom() throws IOException {
		RuleLp sourceRule = lpRule("p(X) :- q(X), r(X).");
		PatternRuleLp firstFact = patternFact("q(Y){}{}", 0);
		PatternRuleLp secondFact = patternFact("r(Z){}{}", 0);

		Collection<PatternRuleLp> unfolded = RuleLpPatternUnfolder.unfold(
				sourceRule, List.of(firstFact, secondFact), 1);

		assertEquals(
				List.of(
						"p(_0) :- q(_0)",
						"p(_0) :- r(_0)",
						"p(_0) :- e*"),
				render(unfolded));
	}

	@Test
	void onlyEmitsRulesReachingCurrentIteration() throws IOException {
		RuleLp sourceRule = lpRule("p(X) :- q(X).");
		PatternRuleLp oldCandidate = patternRule(
				"q(Y){}{}", "a(Y){}{}", 0);
		PatternRuleLp precedingCandidate = patternRule(
				"q(Z){}{}", "b(Z){}{}", 1);

		assertTrue(RuleLpPatternUnfolder.unfold(
				sourceRule, List.of(oldCandidate), 2).isEmpty());
		assertEquals(
				List.of("p(_0) :- b(_0)"),
				render(RuleLpPatternUnfolder.unfold(
						sourceRule,
						List.of(oldCandidate, precedingCandidate),
						2)));
	}

	@Test
	void leavesSourceAndCandidateRulesReusable() throws IOException {
		RuleLp sourceRule = lpRule("p(X) :- q(f(X)).");
		PatternRuleLp candidate = patternRule(
				"q(f(Y)){}{}", "r(Y){}{}", 0);
		String sourceBefore = sourceRule.toString();
		String candidateBefore = candidate.toString();

		List<String> firstUnfolding = render(RuleLpPatternUnfolder.unfold(
				sourceRule, List.of(candidate), 1));

		assertEquals(sourceBefore, sourceRule.toString());
		assertEquals(candidateBefore, candidate.toString());
		assertEquals(
				firstUnfolding,
				render(RuleLpPatternUnfolder.unfold(
						sourceRule, List.of(candidate), 1)));
	}

	@Test
	void returnsCompletedPrefixWhenInterrupted() throws IOException {
		RuleLp sourceRule = lpRule("p(X) :- q(X).");
		PatternRuleLp firstCandidate = patternRule(
				"q(Y){}{}", "a(Y){}{}", 0);
		PatternRuleLp secondCandidate = patternRule(
				"q(Z){}{}", "b(Z){}{}", 0);
		Collection<PatternRuleLp> interruptingCandidates =
				interruptBeforeSecondCandidate(
						List.of(firstCandidate, secondCandidate));

		try {
			Collection<PatternRuleLp> unfolded = RuleLpPatternUnfolder.unfold(
					sourceRule, interruptingCandidates, 1);

			assertEquals(
					List.of("p(_0) :- q(_0)", "p(_0) :- a(_0)"),
					render(unfolded));
			assertTrue(Thread.currentThread().isInterrupted());
		}
		finally {
			Thread.interrupted();
		}
	}

	private RuleLp lpRule(String text) throws IOException {
		return parser.parseLpRule(text, new HashMap<>());
	}

	private PatternRuleLp patternRule(
			String left,
			String right,
			int iteration) throws IOException {
		HashMap<String, Variable> variables = new HashMap<>();
		return PatternRuleLp.tryBuild(
				parser.parseSimplePatternTerm(left, variables),
				parser.parseSimplePatternTerm(right, variables),
				iteration);
	}

	private PatternRuleLp patternFact(
			String left,
			int iteration) throws IOException {
		return PatternRuleLp.tryBuildFact(
				parser.parseSimplePatternTerm(left, new HashMap<>()),
				iteration);
	}

	private static List<String> render(Collection<PatternRuleLp> rules) {
		List<String> rendered = new ArrayList<>();
		for (PatternRuleLp rule : rules)
			rendered.add(rule.toString());
		return rendered;
	}

	private static Collection<PatternRuleLp> interruptBeforeSecondCandidate(
			List<PatternRuleLp> candidates) {
		return new AbstractCollection<>() {
			@Override
			public Iterator<PatternRuleLp> iterator() {
				Iterator<PatternRuleLp> iterator = candidates.iterator();
				return new Iterator<>() {
					private int hasNextCalls;

					@Override
					public boolean hasNext() {
						if (++this.hasNextCalls == 2)
							Thread.currentThread().interrupt();
						return iterator.hasNext();
					}

					@Override
					public PatternRuleLp next() {
						return iterator.next();
					}
				};
			}

			@Override
			public int size() {
				return candidates.size();
			}
		};
	}
}
