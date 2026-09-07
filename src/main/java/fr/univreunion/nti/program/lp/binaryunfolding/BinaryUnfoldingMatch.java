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

import fr.univreunion.nti.program.lp.UnfoldedRuleLp;

/**
 * Stores the copied rules and metadata for a successful binary unfolding
 * unification step.
 *
 * @param step the unfolding step metadata
 * @param rule the copied rule computed so far during the unfolding
 * @param unfoldingRule the copied rule used for unfolding
 */
record BinaryUnfoldingMatch(
		BinaryUnfoldingStep step,
		UnfoldedRuleLp rule,
		UnfoldedRuleLp unfoldingRule) {

	/**
	 * Tries to build a successful unfolding match.
	 *
	 * @param bodyIndex the selected body atom index
	 * @param lastIndex the index of the last atom in the body
	 * @param rule the rule computed so far during the unfolding
	 * @param unfoldingRule the rule used for unfolding
	 * @param iteration the current iteration of the unfolding operator
	 * @return the corresponding match, or <code>null</code> if the
	 * selected body atom does not unify with the unfolding rule head
	 */
	static BinaryUnfoldingMatch tryBuild(
			int bodyIndex,
			int lastIndex,
			UnfoldedRuleLp rule,
			UnfoldedRuleLp unfoldingRule,
			int iteration) {

		if (rule.getBody(bodyIndex).getRootSymbol() !=
				unfoldingRule.getHead().getRootSymbol())
			return null;

		BinaryUnfoldingStep step = BinaryUnfoldingStep.of(
				bodyIndex,
				lastIndex,
				rule,
				unfoldingRule,
				iteration);
		UnfoldedRuleLp ruleCopy = rule.deepCopy();
		UnfoldedRuleLp unfoldingRuleCopy = unfoldingRule.deepCopy();

		if (!ruleCopy.getBody(bodyIndex).unifyWith(unfoldingRuleCopy.getHead()))
			return null;

		return new BinaryUnfoldingMatch(
				step,
				ruleCopy,
				unfoldingRuleCopy);
	}

	/**
	 * Returns whether the copied unfolding rule is a fact.
	 *
	 * @return <code>true</code> if and only if the copied unfolding
	 * rule is a fact
	 */
	boolean isFact() {
		return this.unfoldingRule.isFact();
	}
}
