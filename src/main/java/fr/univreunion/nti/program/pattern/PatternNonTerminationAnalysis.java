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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.pattern;

import fr.univreunion.nti.term.Function;

/**
 * The result of pattern nontermination analysis.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

record PatternNonTerminationAnalysis(
		Function nonTerminatingTerm,
		int alpha) {

	/**
	 * Returns an unsuccessful analysis result.
	 *
	 * @return the unsuccessful result
	 */
	static PatternNonTerminationAnalysis failure() {
		return new PatternNonTerminationAnalysis(null, -1);
	}
}
