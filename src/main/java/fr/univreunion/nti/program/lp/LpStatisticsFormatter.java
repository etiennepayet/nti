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

package fr.univreunion.nti.program.lp;

/**
 * Builds the textual statistics of an LP.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LpStatisticsFormatter {

	/**
	 * Returns a String representation of some statistics about the specified LP.
	 *
	 * @param lp the LP whose statistics have to be formatted
	 * @return a String representation of some statistics about the specified LP
	 */
	public String format(Lp lp) {
		// Introductory message.
		return "** BEGIN STATS for program: " + lp.getName() +

				// The number of rules of this program.
				"\n* " +
				lp.size() +
				" rule(s)" +

				// Ending message.
				"\n** END STATS for program: " +
				lp.getName();
	}
}
