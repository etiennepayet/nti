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
 * Applies one binary unfolding rule to one selected body atom.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class BinaryUnfoldingRuleApplicator {

	/**
	 * Unfolds the atom at index <code>bodyIndex</code> in the body of
	 * the provided rule using the provided unfolding rule.
	 *
	 * @param bodyIndex the index of the current atom to consider in
	 * the body of the rule
	 * @param unfoldingRule the rule that we have to use to unfold
	 * @param rule the rule computed so far during the unfolding
	 * @param rulesInProgress the collection to which rules still in
	 * progress must be added
	 * @param lastIndex the index of the last atom in the body of the rule
	 * @param iteration the current iteration of the unfolding operator
	 * @return a collection of unfolded rules
	 */
	static Collection<UnfoldedRuleLp> unfoldAtIndex(
			int bodyIndex,
			UnfoldedRuleLp unfoldingRule,
			UnfoldedRuleLp rule,
			Collection<UnfoldedRuleLp> rulesInProgress,
			int lastIndex,
			int iteration) {

		LinkedList<UnfoldedRuleLp> result = new LinkedList<>();

		BinaryUnfoldingMatch match = BinaryUnfoldingMatch.tryBuild(
				bodyIndex,
				lastIndex,
				rule,
				unfoldingRule,
				iteration);
		if (match == null) return result;

		if (match.isFact())
			result.addAll(unfoldWithFactRule(
					match.step(),
					match.rule(),
					rulesInProgress));
		else if (match.step().reachesCurrentIteration())
			result.add(unfoldWithNonFactRule(
					match.unfoldingRule(),
					match.rule(),
					match.step().iteration()));

		return result;
	}

	/**
	 * Unfolds the current body atom with a fact.
	 *
	 * @param step the unfolding step metadata
	 * @param rule the copied rule computed so far during the unfolding
	 * @param rulesInProgress the collection to which rules still in
	 * progress must be added
	 * @return the resulting unfolded facts
	 */
	private static Collection<UnfoldedRuleLp> unfoldWithFactRule(
			BinaryUnfoldingStep step,
			UnfoldedRuleLp rule,
			Collection<UnfoldedRuleLp> rulesInProgress) {

		LinkedList<UnfoldedRuleLp> result = new LinkedList<>();

		if (!step.isLastBodyAtom())
			// The selected body atom is not the last one: the current atom
			// in the body of the rule cannot be unfolded with a fact.
			rulesInProgress.add(UnfoldedRuleLp.of(
					rule.getHead(),
					bodyOf(rule),
					step.latestSourceIteration()));
		else if (step.reachesCurrentIteration())
			// The last atom in the body of the rule can be
			// unfolded with a fact. This results in a new fact.
			result.add(UnfoldedRuleLp.fact(
					rule.getHead(),
					step.iteration()));

		return result;
	}

	/**
	 * Unfolds the current body atom with a non-fact rule.
	 *
	 * @param unfoldingRule the copied non-fact rule used for unfolding
	 * @param rule the copied rule computed so far during the unfolding
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rule
	 */
	private static UnfoldedRuleLp unfoldWithNonFactRule(
			UnfoldedRuleLp unfoldingRule,
			UnfoldedRuleLp rule,
			int iteration) {

		Function[] unfoldedBody = {
				unfoldingRule.getBody(0)
		};

		return UnfoldedRuleLp.of(
				rule.getHead(),
				unfoldedBody,
				iteration);
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
	private BinaryUnfoldingRuleApplicator() {
	}
}
