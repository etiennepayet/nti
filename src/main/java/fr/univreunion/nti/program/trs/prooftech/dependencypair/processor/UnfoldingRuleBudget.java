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

package fr.univreunion.nti.program.trs.prooftech.dependencypair.processor;

/**
 * A generated-rule budget local to one unfolding processor attempt.
 */
final class UnfoldingRuleBudget {

	/** The maximum number of generated rules. */
	private final int maximum;

	/** The number of rules generated so far. */
	private int generatedRuleCount;

	/**
	 * Builds a budget with the specified maximum.
	 *
	 * @param maximum the maximum number of generated rules
	 */
	UnfoldingRuleBudget(int maximum) {
		if (maximum < 0)
			throw new IllegalArgumentException("negative unfolding-rule budget");
		this.maximum = maximum;
	}

	/**
	 * Indicates whether another unfolding call may be started.
	 *
	 * @return {@code true} if this budget has remaining capacity
	 */
	boolean hasRemainingCapacity() {
		return this.generatedRuleCount < this.maximum;
	}

	/**
	 * Records generated rules.
	 *
	 * @param count the number of newly generated rules
	 */
	void recordGeneratedRules(int count) {
		this.generatedRuleCount += count;
	}

	/**
	 * Returns the number of rules generated so far.
	 *
	 * @return the number of generated rules
	 */
	int getGeneratedRuleCount() {
		return this.generatedRuleCount;
	}
}
