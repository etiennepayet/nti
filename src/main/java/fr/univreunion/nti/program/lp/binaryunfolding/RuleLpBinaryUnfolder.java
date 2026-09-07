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

import java.util.Collection;
import java.util.LinkedList;

import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.UnfoldedRuleLp;
import fr.univreunion.nti.term.Function;

/**
 * Applies the binary logic-program unfolding operator to one rule.
 *
 * <p>The operator is defined in M. Codish and C. Taboch,
 * <a href="https://doi.org/10.1016/S0743-1066(99)00006-0">A Semantic
 * Basis for the Termination Analysis of Logic Programs</a>, Journal of
 * Logic Programming 41(1), 103--123, 1999.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class RuleLpBinaryUnfolder {

	/**
	 * Unfolds the given rule once using the given collection of rules.
	 * <p>
	 * Applies the T^{\beta}_P operator of Codish and Taboch (1999), cited
	 * in the class documentation, to the provided rule.
	 *
	 * @param sourceRule the logic programming rule to unfold
	 * @param unfoldingRules a collection of rules for unfolding
	 * <code>sourceRule</code>
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 * @throws IllegalArgumentException if the given iteration
	 * is negative or zero
	 */
	public static Collection<UnfoldedRuleLp> unfold(
			RuleLp sourceRule,
			Collection<UnfoldedRuleLp> unfoldingRules,
			int iteration) {

		return unfoldWithCandidates(
				sourceRule,
				ignored -> unfoldingRules,
				iteration);
	}

	/**
	 * Unfolds the given rule using candidates selected by head predicate.
	 *
	 * @param sourceRule the logic programming rule to unfold
	 * @param unfoldingRuleIndex the indexed rules available for unfolding
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 */
	static Collection<UnfoldedRuleLp> unfold(
			RuleLp sourceRule,
			BinaryUnfoldingRuleIndex unfoldingRuleIndex,
			int iteration) {

		return unfoldWithCandidates(
				sourceRule,
				unfoldingRuleIndex,
				iteration);
	}

	/**
	 * Unfolds the given rule using the provided candidate selector.
	 *
	 * @param sourceRule the logic programming rule to unfold
	 * @param candidateSelector the unfolding-candidate selector
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 */
	private static Collection<UnfoldedRuleLp> unfoldWithCandidates(
			RuleLp sourceRule,
			CandidateSelector candidateSelector,
			int iteration) {

		if (iteration <= 0)
			throw new IllegalArgumentException(
					"unfolding a rule with a negative iteration");

		if (sourceRule.isFact())
			return unfoldFact(sourceRule, iteration);

		return unfoldRuleWithBody(sourceRule, candidateSelector, iteration);
	}

	/**
	 * Unfolds the given fact.
	 *
	 * @param sourceRule the fact to unfold
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded facts
	 */
	private static Collection<UnfoldedRuleLp> unfoldFact(
			RuleLp sourceRule,
			int iteration) {

		LinkedList<UnfoldedRuleLp> result = new LinkedList<>();

		// Here, sourceRule is a fact. We add it to the
		// result only if we are at iteration 1.
		if (iteration == 1)
			result.add(UnfoldedRuleLp.fact(sourceRule.getHead(), 1));

		return result;
	}

	/**
	 * Unfolds the given rule, whose body is non-empty.
	 *
	 * @param sourceRule the logic programming rule to unfold
	 * @param candidateSelector the unfolding-candidate selector
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 */
	private static Collection<UnfoldedRuleLp> unfoldRuleWithBody(
			RuleLp sourceRule,
			CandidateSelector candidateSelector,
			int iteration) {

		// The thread running this unfolding.
		Thread currentThread = Thread.currentThread();

		LinkedList<UnfoldedRuleLp> result = new LinkedList<>();

		// We implement a slight modification of T^{\beta}_P.
		// Generated binary rules are associated with their iteration
		// number. We generate a new rule in 'result' only when we
		// have used a rule of the immediately preceding iteration.
		// Hence, the "previous iteration" checks before adding
		// something to result.

		LinkedList<UnfoldedRuleLp> rulesInProgress = new LinkedList<>();
		rulesInProgress.add(UnfoldedRuleLp.of(
				sourceRule.getHead(),
				bodyOf(sourceRule),
				0));

		int lastIndex = sourceRule.getBodyLength() - 1;
		for (int bodyIndex = 0; bodyIndex <= lastIndex; bodyIndex++) {
			if (currentThread.isInterrupted()) break;

			LinkedList<UnfoldedRuleLp> unfoldedWithFacts = rulesInProgress;
			rulesInProgress = new LinkedList<>();

			// Suppose that sourceRule has the form h <- b_1,...,b_n.
			// The invariant of this for loop is: at that point,
			// b_1,...,b_{bodyIndex-1} have been unfolded with facts and
			// the list 'unfoldedWithFacts' contains all the
			// corresponding instantiations of this rule. Therefore,
			// all elements of 'unfoldedWithFacts' have the form
			// h' <- b'_1,...,b'_n where
			// (h',b'_1,...,b'_n) = (h,b_1,...,b_n)\theta for a
			// substitution \theta which is the mgu computed so far.

			result.addAll(unfoldAtBodyIndex(
					bodyIndex,
					unfoldedWithFacts,
					candidateSelector.candidatesFor(
							sourceRule.getBody(bodyIndex)),
					rulesInProgress,
					lastIndex,
					iteration));
		}

		return result;
	}

	/**
	 * Unfolds all rules in progress at the given body index.
	 *
	 * @param bodyIndex the selected body atom index
	 * @param unfoldedWithFacts the rules in progress computed so far
	 * after unfolding previous body atoms with facts
	 * @param unfoldingRules a collection of rules for unfolding
	 * @param nextRulesInProgress the collection to which rules still
	 * in progress must be added for the next body index
	 * @param lastIndex the index of the last atom in the body
	 * @param iteration the current iteration of the unfolding operator
	 * @return the unfolded rules generated at the given body index
	 */
	private static Collection<UnfoldedRuleLp> unfoldAtBodyIndex(
			int bodyIndex,
			Collection<UnfoldedRuleLp> unfoldedWithFacts,
			Collection<UnfoldedRuleLp> unfoldingRules,
			Collection<UnfoldedRuleLp> nextRulesInProgress,
			int lastIndex,
			int iteration) {

		Thread currentThread = Thread.currentThread();
		LinkedList<UnfoldedRuleLp> result = new LinkedList<>();

		for (UnfoldedRuleLp rule : unfoldedWithFacts) {
			if (currentThread.isInterrupted()) break;

			// First, unfold rule with id but only if the
			// resulting rule belongs to the current iteration.
			if (comesFromPreviousIteration(rule, iteration))
				result.add(IdentityBinaryUnfolder.unfold(
						rule,
						bodyIndex,
						iteration));

			// Then, unfold rule with the provided unfolding rules.
			for (UnfoldedRuleLp unfoldingRule : unfoldingRules) {
				if (currentThread.isInterrupted()) break;

				result.addAll(BinaryUnfoldingRuleApplicator.unfoldAtIndex(
						bodyIndex,
						unfoldingRule,
						rule,
						nextRulesInProgress,
						lastIndex,
						iteration));
			}
		}

		return result;
	}

	/**
	 * Returns whether the given rule was produced during the iteration
	 * immediately preceding the current one.
	 *
	 * @param rule the rule computed so far during the unfolding
	 * @param iteration the current iteration of the unfolding operator
	 * @return <code>true</code> if and only if <code>rule</code>
	 * comes from the immediately preceding iteration
	 */
	private static boolean comesFromPreviousIteration(
			UnfoldedRuleLp rule,
			int iteration) {

		return rule.getIteration() == iteration - 1;
	}

	/**
	 * Returns the body of the given rule as an array.
	 *
	 * @param rule a logic programming rule
	 * @return the body atoms of <code>rule</code>
	 */
	private static Function[] bodyOf(RuleLp rule) {
		Function[] body = new Function[rule.getBodyLength()];
		for (int bodyIndex = 0; bodyIndex < body.length; bodyIndex++)
			body[bodyIndex] = rule.getBody(bodyIndex);

		return body;
	}

	/**
	 * Disables construction.
	 */
	private RuleLpBinaryUnfolder() {
	}

	/** Selects the unfolding candidates for a body atom. */
	@FunctionalInterface
	interface CandidateSelector {

		/**
		 * Returns the rules that may unfold the given body atom.
		 *
		 * @param bodyAtom the body atom to unfold
		 * @return its unfolding candidates
		 */
		Collection<UnfoldedRuleLp> candidatesFor(Function bodyAtom);
	}
}
