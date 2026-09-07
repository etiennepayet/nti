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

package fr.univreunion.nti.program.lp.patternunfolding;

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.program.lp.RuleLp;

/**
 * Generates LP pattern rules by applying the pattern
 * unfolding operator.
 * <p>
 * This class owns only the unfolding state: the initial set
 * <code>B</code> of correct pattern rules, the pattern rules
 * produced so far, and the computation of each new iteration
 * of the pattern unfolding operator.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LpPatternUnfolder {

	/**
	 * The rules of the logic program.
	 */
	private final List<RuleLp> rules = new ArrayList<>();

	/**
	 * All pattern rules produced so far, indexed by left-hand predicate and
	 * initialized with the correct pattern rules used as the set <code>B</code>
	 * in the pattern unfolding operator.
	 */
	private final PatternUnfoldingRuleIndex unfoldingRuleIndex =
			new PatternUnfoldingRuleIndex();

	/**
	 * Builds an unfolder for the provided logic program rules.
	 *
	 * @param rules the rules of the logic program
	 */
	public LpPatternUnfolder(Iterable<RuleLp> rules) {
		for (RuleLp r : rules)
			this.rules.add(r);

		this.unfoldingRuleIndex.addAll(
				CorrectPatternRuleLpCollector.collectFrom(this.rules));
	}

	/**
	 * Computes one iteration of the pattern unfolding operator.
	 *
	 * @param iteration the current iteration number
	 * @return the pattern rules generated during this iteration
	 * @throws InterruptedException if the current thread is interrupted
	 */
	public List<PatternRuleLp> unfoldNext(int iteration) throws InterruptedException {
		Thread currentThread = Thread.currentThread();
		List<PatternRuleLp> unfolded = new ArrayList<>();

		for (RuleLp r : this.rules) {
			if (currentThread.isInterrupted())
				throw new InterruptedException();

			unfolded.addAll(RuleLpPatternUnfolder.unfold(
					r,
					this.unfoldingRuleIndex,
					iteration));
		}

		this.unfoldingRuleIndex.addAll(unfolded);
		return unfolded;
	}
}
