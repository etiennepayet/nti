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

import java.util.Map;

import fr.univreunion.nti.term.Variable;

/**
 * Formats logic programming pattern rules in progress.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleLpInProgressFormatter {

	/**
	 * Returns a string representation of the given rule in progress
	 * relatively to the provided set of variable symbols.
	 *
	 * @param rule a rule in progress
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of <code>rule</code>
	 */
	static String format(
			PatternRuleLpInProgress rule,
			Map<Variable, String> variables) {

		return rule.getPatternSubstitution().toString(variables) +
				" -- iteration = " + rule.getIteration();
	}

	/**
	 * Disables construction.
	 */
	private PatternRuleLpInProgressFormatter() {
	}
}
