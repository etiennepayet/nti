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
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Variable;

class RuleLpBinaryUnfolderTest {

	@Test
	@DisplayName("reject non-positive iteration")
	void rejectNonPositiveIteration() throws IOException {
		RuleLp sourceRule = parseRule("p(a).");

		assertThrows(
				IllegalArgumentException.class,
				() -> RuleLpBinaryUnfolder.unfold(sourceRule, List.of(), 0));
		assertThrows(
				IllegalArgumentException.class,
				() -> RuleLpBinaryUnfolder.unfold(sourceRule, List.of(), -1));
	}

	@Test
	@DisplayName("unfold fact only at first iteration")
	void unfoldFactOnlyAtFirstIteration() throws IOException {
		RuleLp sourceRule = parseRule("p(a).");

		Collection<UnfoldedRuleLp> firstIteration =
				RuleLpBinaryUnfolder.unfold(sourceRule, List.of(), 1);
		Collection<UnfoldedRuleLp> secondIteration =
				RuleLpBinaryUnfolder.unfold(sourceRule, List.of(), 2);

		assertEquals(1, firstIteration.size());
		assertEquals("p(a).", firstIteration.iterator().next().toString());
		assertTrue(secondIteration.isEmpty());
	}

	@Test
	@DisplayName("unfold with identity")
	void unfoldWithIdentity() throws IOException {
		RuleLp sourceRule = parseRule("p(X) :- q(X).");

		Collection<UnfoldedRuleLp> unfolded =
				RuleLpBinaryUnfolder.unfold(sourceRule, List.of(), 1);

		UnfoldedRuleLp unfoldedRule = singleRule(unfolded);
		assertEquals(1, unfoldedRule.getIteration());
		assertEquals("p(_0) :- q(_0)", unfoldedRule.toString());
	}

	@Test
	@DisplayName("preserve identity-first and candidate order")
	void preserveIdentityFirstAndCandidateOrder() throws IOException {
		RuleLp sourceRule = parseRule("p(X) :- q(X).");
		UnfoldedRuleLp firstMatch =
				unfoldedRule(parseRule("q(b)."), 0);
		UnfoldedRuleLp nonMatch =
				unfoldedRule(parseRule("r(c)."), 0);
		UnfoldedRuleLp secondMatch =
				unfoldedRule(parseRule("q(a)."), 0);

		Collection<UnfoldedRuleLp> unfolded =
				RuleLpBinaryUnfolder.unfold(
						sourceRule,
						List.of(firstMatch, nonMatch, secondMatch),
						1);

		assertEquals(
				List.of("p(_0) :- q(_0)", "p(b).", "p(a)."),
				unfolded.stream().map(Object::toString).toList());
	}

	@Test
	@DisplayName("unfold last atom with fact")
	void unfoldLastAtomWithFact() throws IOException {
		RuleLp sourceRule = parseRule("p(X) :- q(X).");
		UnfoldedRuleLp unfoldingFact =
				unfoldedRule(parseRule("q(a)."), 0);

		Collection<UnfoldedRuleLp> unfolded =
				RuleLpBinaryUnfolder.unfold(
						sourceRule,
						List.of(unfoldingFact),
						1);

		assertTrue(containsRule(unfolded, "p(a)."));
	}

	@Test
	@DisplayName("unfold non-last atom with fact")
	void unfoldNonLastAtomWithFact() throws IOException {
		RuleLp sourceRule = parseRule("p(X) :- q(X), r(X).");
		UnfoldedRuleLp unfoldingFact =
				unfoldedRule(parseRule("q(a)."), 0);

		Collection<UnfoldedRuleLp> unfolded =
				RuleLpBinaryUnfolder.unfold(
						sourceRule,
						List.of(unfoldingFact),
						1);

		assertTrue(containsRule(unfolded, "p(a) :- r(a)"));
	}

	@Test
	@DisplayName("unfold with non-fact rule")
	void unfoldWithNonFactRule() throws IOException {
		RuleLp sourceRule = parseRule("p(X) :- q(X).");
		UnfoldedRuleLp unfoldingRule =
				unfoldedRule(parseRule("q(X) :- r(X)."), 0);

		Collection<UnfoldedRuleLp> unfolded =
				RuleLpBinaryUnfolder.unfold(
						sourceRule,
						List.of(unfoldingRule),
						1);

		assertTrue(containsRule(unfolded, "p(_0) :- r(_0)"));
	}

	@Test
	@DisplayName("ignore unfolding rule whose head does not unify")
	void ignoreUnfoldingRuleWhoseHeadDoesNotUnify() throws IOException {
		RuleLp sourceRule = parseRule("p(X) :- q(X).");
		UnfoldedRuleLp nonMatchingRule =
				unfoldedRule(parseRule("r(a) :- s(a)."), 0);

		Collection<UnfoldedRuleLp> unfolded =
				RuleLpBinaryUnfolder.unfold(
						sourceRule,
						List.of(nonMatchingRule),
						1);

		assertEquals(1, unfolded.size());
		assertTrue(containsRule(unfolded, "p(_0) :- q(_0)"));
	}

	@Test
	@DisplayName("reject incompatible predicates before copying")
	void rejectIncompatiblePredicatesBeforeCopying() throws IOException {
		CopyCountingRule sourceRule =
				new CopyCountingRule(parseRule("p(X) :- q(X)."));
		CopyCountingRule nonMatchingRule =
				new CopyCountingRule(parseRule("r(a) :- s(a)."));

		assertNull(BinaryUnfoldingMatch.tryBuild(
				0, 0, sourceRule, nonMatchingRule, 1));
		assertEquals(0, sourceRule.copyCount);
		assertEquals(0, nonMatchingRule.copyCount);
	}

	private static RuleLp parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		return parser.parseLpRule(ruleText, variables);
	}

	private static UnfoldedRuleLp unfoldedRule(RuleLp rule, int iteration) {
		return UnfoldedRuleLp.of(rule.getHead(), bodyOf(rule), iteration);
	}

	private static Function[] bodyOf(RuleLp rule) {
		Function[] body = new Function[rule.getBodyLength()];
		for (int bodyIndex = 0; bodyIndex < body.length; bodyIndex++)
			body[bodyIndex] = rule.getBody(bodyIndex);

		return body;
	}

	private static UnfoldedRuleLp singleRule(Collection<UnfoldedRuleLp> rules) {
		assertEquals(1, rules.size());
		return rules.iterator().next();
	}

	private static boolean containsRule(
			Collection<UnfoldedRuleLp> rules,
			String expectedRule) {

		for (UnfoldedRuleLp rule : rules)
			if (expectedRule.equals(rule.toString()))
				return true;

		return false;
	}

	private static final class CopyCountingRule extends UnfoldedRuleLp {

		private int copyCount;

		private CopyCountingRule(RuleLp rule) {
			super(rule.getHead(), bodyOf(rule), 0);
		}

		@Override
		public UnfoldedRuleLp deepCopy() {
			this.copyCount++;
			return super.deepCopy();
		}
	}
}
