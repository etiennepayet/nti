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

package fr.univreunion.nti.program.trs.patternunfolding;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Creates flattened deep copies of TRS pattern rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleTrsCopier {

	/**
	 * Returns a flattened deep copy with a fresh copy map.
	 *
	 * @param patternRule the pattern rule to copy
	 * @return the deep copy
	 */
	static PatternRuleTrs deepCopy(PatternRuleTrs patternRule) {
		return deepCopy(patternRule, new HashMap<>());
	}

	/**
	 * Returns a flattened deep copy using the incrementally constructed map.
	 *
	 * @param patternRule the pattern rule to copy
	 * @param copies pairs whose values are deep copies of their keys
	 * @return the deep copy
	 */
	static PatternRuleTrs deepCopy(
			PatternRuleTrs patternRule,
			Map<Term, Term> copies) {

		SimplePatternTerm right = patternRule.getRight();
		Function nonTerminatingTerm = patternRule.getNonTerminatingTerm();

		return new PatternRuleTrs(
				patternRule.getLeft().deepCopy(copies),
				right == null ? null : right.deepCopy(copies),
				patternRule.getIteration(),
				nonTerminatingTerm == null
						? null
						: (Function) nonTerminatingTerm.deepCopy(copies),
				patternRule.getAlpha());
	}

	/** Prevents instantiation of this utility class. */
	private PatternRuleTrsCopier() {
	}
}
