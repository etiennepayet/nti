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
 * Groups metadata for one binary unfolding step.
 *
 * @param bodyIndex the selected body atom index
 * @param lastIndex the index of the last atom in the body of the rule
 * @param latestSourceIteration the latest iteration among the two
 * source rules used for this unfolding step
 * @param iteration the current iteration of the unfolding operator
 */
record BinaryUnfoldingStep(
		int bodyIndex,
		int lastIndex,
		int latestSourceIteration,
		int iteration) {

	/**
	 * Builds the metadata for one unfolding step.
	 *
	 * @param bodyIndex the selected body atom index
	 * @param lastIndex the index of the last atom in the body
	 * @param rule the rule computed so far during the unfolding
	 * @param unfoldingRule the rule used for unfolding
	 * @param iteration the current iteration of the unfolding operator
	 * @return the corresponding unfolding step metadata
	 */
	static BinaryUnfoldingStep of(
			int bodyIndex,
			int lastIndex,
			UnfoldedRuleLp rule,
			UnfoldedRuleLp unfoldingRule,
			int iteration) {

		return new BinaryUnfoldingStep(
				bodyIndex,
				lastIndex,
				Math.max(rule.getIteration(), unfoldingRule.getIteration()),
				iteration);
	}

	/**
	 * Returns whether the selected body atom is the last one.
	 *
	 * @return <code>true</code> if and only if the selected body
	 * atom is the last one
	 */
	boolean isLastBodyAtom() {
		return this.bodyIndex == this.lastIndex;
	}

	/**
	 * Returns whether this unfolding step reaches the current iteration.
	 *
	 * @return <code>true</code> if and only if this unfolding step
	 * reaches the current iteration
	 */
	boolean reachesCurrentIteration() {
		return this.latestSourceIteration == this.iteration - 1;
	}
}
