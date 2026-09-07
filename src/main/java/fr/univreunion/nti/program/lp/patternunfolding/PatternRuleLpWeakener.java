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

import java.util.Collection;
import java.util.LinkedList;

import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Weakens the left-hand side of fact pattern rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class PatternRuleLpWeakener {

	/**
	 * If the pattern rule is a fact then attempts to weaken it based
	 * on its left-hand side and the provided pattern term.
	 *
	 * @param patternRule the pattern rule to weaken
	 * @param patternTerm a pattern term for weakening the rule
	 * @return a collection of weakened versions of the left-hand side
	 * of the pattern rule
	 */
	static Collection<Term> weakenLeftIfFact(
			PatternRuleLp patternRule,
			SimplePatternTerm patternTerm) {

		Collection<Term> weakenedLefts = new LinkedList<>();

		SimplePatternTerm left = patternRule.getLeft();
		if (!canWeakenLeftWith(patternRule, left, patternTerm))
			return weakenedLefts;

		// The indexes to use for weakening this pattern rule
		// are computed from the left-hand side of this rule
		// w.r.t. patternTerm.
		SimplePatternTerm.WeakeningIndexes weakeningIndexes =
				left.computeWeakeningIndexes(patternTerm);
		if (weakeningIndexes == null)
			return weakenedLefts;

		addWeakenedLefts(left, weakeningIndexes, weakenedLefts);

		return weakenedLefts;
	}

	/**
	 * Checks whether the pattern rule can attempt weakening with
	 * the provided pattern term.
	 *
	 * @param patternRule the pattern rule to weaken
	 * @param left the left-hand side of the rule
	 * @param patternTerm a pattern term for weakening the rule
	 * @return <code>true</code> iff weakening can be attempted
	 */
	private static boolean canWeakenLeftWith(
			PatternRuleLp patternRule,
			SimplePatternTerm left,
			SimplePatternTerm patternTerm) {

		// We perform weakening only if the rule is a fact, its
		// left-hand side has the same root symbol as patternTerm
		// and the arity of both pattern terms is equal to 1.
		return patternRule.isFact() &&
				left.getUpsilon().getRootSymbol() ==
						patternTerm.getUpsilon().getRootSymbol() &&
				left.getArity() == 1 &&
				patternTerm.getArity() == 1;
	}

	/**
	 * Adds the weakened left-hand sides selected by the computed
	 * weakening indexes.
	 *
	 * @param left the left-hand side to weaken
	 * @param weakeningIndexes the computed weakening indexes
	 * @param weakenedLefts the collection to fill with weakened
	 * left-hand sides
	 */
	private static void addWeakenedLefts(
			SimplePatternTerm left,
			SimplePatternTerm.WeakeningIndexes weakeningIndexes,
			Collection<Term> weakenedLefts) {

		int functionIndex = weakeningIndexes.functionWeakeningIndex();
		int hatIndex = weakeningIndexes.hatWeakeningIndex();

		if (isFunctionWeakeningOnly(functionIndex, hatIndex)) {
			// Here, we compute left(functionIndex), which is
			// an element of {left(n) | n \in \nat}.
			weakenedLefts.add(left.instantiateAt(functionIndex));
		}
		else if (isHatWeakeningOnly(functionIndex, hatIndex)) {
			addHatWeakenedLefts(left, hatIndex, weakenedLefts);
		}
	}

	/**
	 * Checks whether the indexes select the finite instantiation
	 * weakening case.
	 *
	 * @param functionIndex the ordinary-function weakening index
	 * @param hatIndex the hat-function weakening index
	 * @return <code>true</code> iff only the ordinary-function
	 * weakening index is defined
	 */
	private static boolean isFunctionWeakeningOnly(
			int functionIndex, int hatIndex) {

		return 0 <= functionIndex && hatIndex < 0;
	}

	/**
	 * Checks whether the indexes select the hat-function weakening
	 * case.
	 *
	 * @param functionIndex the ordinary-function weakening index
	 * @param hatIndex the hat-function weakening index
	 * @return <code>true</code> iff only the hat-function weakening
	 * index is defined
	 */
	private static boolean isHatWeakeningOnly(
			int functionIndex, int hatIndex) {

		return functionIndex < 0 && 0 <= hatIndex;
	}

	/**
	 * Adds the two weakened left-hand sides derived from a
	 * hat-function weakening index.
	 *
	 * @param left the left-hand side to weaken
	 * @param hatIndex the hat-function weakening index
	 * @param weakenedLefts the collection to fill with weakened
	 * left-hand sides
	 */
	private static void addHatWeakenedLefts(
			SimplePatternTerm left,
			int hatIndex,
			Collection<Term> weakenedLefts) {

		SimplePatternTerm.WeakeningSubstitutions weakeningSubstitutions =
				left.buildWeakeningSubstitutions(hatIndex);

		weakenedLefts.add(left.getBaseTerm().apply(weakeningSubstitutions.first()));
		weakenedLefts.add(left.getBaseTerm().apply(weakeningSubstitutions.second()));
	}

	/**
	 * Disables construction.
	 */
	private PatternRuleLpWeakener() {
	}
}
