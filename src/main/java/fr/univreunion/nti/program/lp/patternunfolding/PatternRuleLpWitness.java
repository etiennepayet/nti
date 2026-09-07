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

import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.term.Function;

/**
 * Handles the nontermination-witness behavior of logic programming
 * pattern rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleLpWitness {

	/**
	 * A short String representation of a logic programming
	 * pattern-rule witness.
	 */
	static final String SHORT_DESCRIPTION =
			"(extracted from a LP pattern rule [Payet, ICLP'25])";

	/**
	 * Checks whether the given pattern rule is a nontermination
	 * witness of the given mode.
	 *
	 * @param patternRule a pattern rule used as a nontermination
	 * witness
	 * @param mode a mode whose nontermination is to be proved
	 * @return a nonterminating atomic query corresponding to
	 * <code>mode</code>, or <code>null</code> if
	 * <code>patternRule</code> is not a nontermination witness of
	 * <code>mode</code>
	 */
	static Function provesNonTerminationOf(
			PatternRuleLp patternRule,
			Mode mode) {

		Function nonterminating = patternRule.getNonTerminatingTerm();

		if (nonterminating != null &&
				nonterminating.getRootSymbol() == mode.getPredSymbol())
			return nonterminating;

		return null;
	}

	/**
	 * Disables construction.
	 */
	private PatternRuleLpWitness() {
	}
}
