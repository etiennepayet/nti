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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.lp.binaryunfolding;

import java.util.LinkedList;
import java.util.List;

import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.UnfoldedRuleLp;

/**
 * Generates LP unfolded rules by applying the binary
 * unfolding operator.
 * <p>
 * This class owns only the unfolding state: the unfolded
 * rules produced so far and the computation of each new
 * iteration of the binary unfolding operator.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class LpBinaryUnfolder {

	/**
	 * The rules of the logic program.
	 */
	private final LinkedList<RuleLp> programRules = new LinkedList<>();

	/**
	 * All unfolded rules produced so far, indexed by head predicate.
	 */
	private final BinaryUnfoldingRuleIndex unfoldingRuleIndex =
			new BinaryUnfoldingRuleIndex();

	/**
	 * Builds an unfolder for the provided logic program rules.
	 *
	 * @param rules the rules of the logic program
	 */
	public LpBinaryUnfolder(Iterable<RuleLp> rules) {
		for (RuleLp rule : rules)
			this.programRules.add(rule);
	}

	/**
	 * Computes one iteration of the binary unfolding operator.
	 * The generated rules are added to the internal unfolding
	 * state before being returned.
	 *
	 * @param iteration the current iteration number
	 * @return the rules generated during this iteration
	 * @throws InterruptedException if the current thread is interrupted
	 */
	public List<UnfoldedRuleLp> unfoldNext(int iteration)
			throws InterruptedException {

		Thread currentThread = Thread.currentThread();
		LinkedList<UnfoldedRuleLp> generatedRules = new LinkedList<>();

		for (RuleLp rule : this.programRules) {
			if (currentThread.isInterrupted())
				throw new InterruptedException();

			generatedRules.addAll(RuleLpBinaryUnfolder.unfold(
					rule,
					this.unfoldingRuleIndex,
					iteration));
		}

		this.unfoldingRuleIndex.addAll(generatedRules);
		return generatedRules;
	}
}
