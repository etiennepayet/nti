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

package fr.univreunion.nti.program.trs;

import java.util.Deque;

import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * Builds the textual statistics of a TRS.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class TrsStatisticsFormatter {

	/**
	 * Returns a String representation of some statistics about the specified TRS.
	 *
	 * @param trs the TRS whose statistics have to be formatted
	 * @return a String representation of some statistics about the specified TRS
	 */
	public String format(Trs trs) {
		// Introductory message.
		StringBuilder s = new StringBuilder("** BEGIN STATS for program: ");
		s.append(trs.getName());

		// The number of rules of this program.
		s.append("\n* ");
		s.append(trs.size());
		s.append(" rule(s)");

		// The SCCs of the dependency graph of this TRS.
		Deque<DependencyPairs> sccs = trs.getDependencyGraph().getSCCs();
		SccStatistics sccStatistics = computeSccStatistics(sccs);
		s.append("\n* ").append(sccStatistics.count()).append(" SCC(s)");
		if (sccStatistics.count() > 0) {
			s.append(" -- nb rules: min=");
			s.append(sccStatistics.minimumRuleCount());
			s.append(" max=").append(sccStatistics.maximumRuleCount());
			s.append(" avg=").append(sccStatistics.averageRuleCount());
		}

		// The initial dependency pairs in the cyclic SCCs.
		s.append("\n* ");
		s.append(sccStatistics.totalRuleCount());
		s.append(" initial dependency pair(s)");

		// Function symbols.
		s.append("\n* ").append(FunctionSymbol.toStringStat());

		// Ending message.
		s.append("\n** END STATS for program: ");
		s.append(trs.getName());

		return s.toString();
	}

	/**
	 * Computes aggregate rule counts for the specified SCCs.
	 *
	 * @param sccs the SCCs to aggregate
	 * @return the computed SCC statistics
	 */
	private static SccStatistics computeSccStatistics(
			Deque<DependencyPairs> sccs) {
		int minimumRuleCount = -1;
		int maximumRuleCount = -1;
		int totalRuleCount = 0;

		for (DependencyPairs scc : sccs) {
			int ruleCount = scc.size();
			totalRuleCount += ruleCount;
			if (minimumRuleCount < 0 || ruleCount < minimumRuleCount)
				minimumRuleCount = ruleCount;
			if (maximumRuleCount < ruleCount)
				maximumRuleCount = ruleCount;
		}

		int count = sccs.size();
		float averageRuleCount = count == 0
				? 0.0f
				: ((float) totalRuleCount) / count;
		return new SccStatistics(
				count,
				minimumRuleCount,
				maximumRuleCount,
				totalRuleCount,
				averageRuleCount);
	}

	/**
	 * Aggregate rule counts for a collection of SCCs.
	 */
	private record SccStatistics(
			int count,
			int minimumRuleCount,
			int maximumRuleCount,
			int totalRuleCount,
			float averageRuleCount) {}
}
