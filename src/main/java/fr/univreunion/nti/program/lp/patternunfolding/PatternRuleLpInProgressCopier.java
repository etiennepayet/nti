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

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.term.Term;

/**
 * Builds deep copies of logic programming pattern rules in progress.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleLpInProgressCopier {

	/**
	 * Returns a deep copy of the given rule in progress i.e.,
	 * a copy where each subterm is also copied, even variable
	 * subterms.
	 * <p>
	 * The returned copy is "flattened" i.e., each of its subterms
	 * is the only element of its class and is its own schema.
	 *
	 * @param rule the rule in progress to copy
	 * @return a deep copy of <code>rule</code>
	 */
	static PatternRuleLpInProgress deepCopy(PatternRuleLpInProgress rule) {
		return deepCopy(rule, new HashMap<>());
	}

	/**
	 * Returns a deep copy of the given rule in progress i.e.,
	 * a copy where each subterm is also copied, even variable
	 * subterms.
	 * <p>
	 * The specified map is used to store subterm copies and is
	 * constructed incrementally.
	 * <p>
	 * The returned copy is "flattened" i.e., each of its subterms
	 * is the only element of its class and is its own schema.
	 *
	 * @param rule the rule in progress to copy
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of <code>rule</code>
	 */
	static PatternRuleLpInProgress deepCopy(
			PatternRuleLpInProgress rule,
			Map<Term, Term> copies) {

		return new PatternRuleLpInProgress(
				rule.getPatternSubstitution().deepCopy(copies),
				rule.getIteration());
	}

	/**
	 * Disables construction.
	 */
	private PatternRuleLpInProgressCopier() {
	}
}
