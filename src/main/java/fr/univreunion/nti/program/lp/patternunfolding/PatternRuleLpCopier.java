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

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Builds deep copies of logic programming pattern rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleLpCopier {

	/**
	 * Returns a deep copy of the given pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param patternRule the pattern rule to copy
	 * @return a deep copy of <code>patternRule</code>
	 */
	static PatternRuleLp deepCopy(PatternRuleLp patternRule) {
		return deepCopy(patternRule, new HashMap<>());
	}

	/**
	 * Returns a deep copy of the given pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param patternRule the pattern rule to copy
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of <code>patternRule</code>
	 */
	static PatternRuleLp deepCopy(
			PatternRuleLp patternRule,
			Map<Term, Term> copies) {

		SimplePatternTerm right = patternRule.getRight();
		Function nonterminating = patternRule.getNonTerminatingTerm();

		return new PatternRuleLp(
				patternRule.getLeft().deepCopy(copies),
				(right == null ? null : right.deepCopy(copies)),
				patternRule.getIteration(),
				(nonterminating == null ? null : (Function) nonterminating.deepCopy(copies)),
				patternRule.getAlpha());
	}

	/**
	 * Disables construction.
	 */
	private PatternRuleLpCopier() {
	}
}
