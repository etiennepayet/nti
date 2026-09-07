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

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Builds logic programming pattern rules.
 *
 * <p>The rule representation and its special form are defined by E. Payet in
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleLpFactory {

	/**
	 * Tries to build a pattern rule from the specified left-hand
	 * side, right-hand side and unfolding iteration.
	 *
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified arguments
	 */
	static PatternRuleLp tryBuild(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		if (hasValidRequiredInput(left, iteration))
			return new PatternRuleLp(left, right, iteration);

		return null;
	}

	/**
	 * Tries to build a pattern fact, i.e., a pattern rule which
	 * has the specified left-hand side and an empty right-hand
	 * side (i.e., <code>e*</code> in the Payet (2025) article cited in the
	 * class documentation).
	 *
	 * @param left the left-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified arguments
	 */
	static PatternRuleLp tryBuildFact(
			SimplePatternTerm left, int iteration) {

		if (hasValidRequiredInput(left, iteration))
			return new PatternRuleLp(left, null, iteration);

		return null;
	}

	/**
	 * Tries to build a pattern rule from the specified base terms,
	 * pattern substitutions and unfolding iteration.
	 *
	 * @param left the base term on the left-hand side of this
	 * pattern rule
	 * @param thetaLeft the pattern substitution on the left-hand
	 * side of this pattern rule
	 * @param right the base term on the right-hand side of this
	 * pattern rule
	 * @param thetaRight the pattern substitution on the right-hand
	 * side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified arguments
	 */
	static PatternRuleLp tryBuild(
			Function left, PatternSubstitution thetaLeft,
			Function right, PatternSubstitution thetaRight,
			int iteration) {

		if (!hasValidRequiredInput(left, iteration))
			return null;

		SimplePatternTerm leftPatternTerm =
				tryBuildSimplePatternTerm(left, thetaLeft);
		SimplePatternTerm rightPatternTerm =
				tryBuildSimplePatternTerm(right, thetaRight);
		if (leftPatternTerm != null && rightPatternTerm != null)
			return new PatternRuleLp(leftPatternTerm, rightPatternTerm, iteration);

		return null;
	}

	/**
	 * Tries to build a pattern fact from the specified base term,
	 * pattern substitution and unfolding iteration. The produced
	 * rule has an empty right-hand side
	 * (i.e., <code>e*</code> in that article).
	 *
	 * @param left the base term on the left-hand side of this
	 * pattern rule
	 * @param thetaLeft the pattern substitution on the left-hand
	 * side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified arguments
	 */
	static PatternRuleLp tryBuildFact(
			Function left, PatternSubstitution thetaLeft,
			int iteration) {

		if (!hasValidRequiredInput(left, iteration))
			return null;

		SimplePatternTerm leftPatternTerm =
				tryBuildSimplePatternTerm(left, thetaLeft);
		if (leftPatternTerm != null)
			return new PatternRuleLp(leftPatternTerm, null, iteration);

		return null;
	}

	/**
	 * Checks whether the required factory arguments are present.
	 *
	 * @param left the required left-hand side
	 * @param iteration the iteration of the unfolding operator
	 * @return <code>true</code> iff the required arguments are valid
	 */
	private static boolean hasValidRequiredInput(Object left, int iteration) {
		return left != null && 0 <= iteration;
	}

	/**
	 * Tries to build a simple pattern term from a base term and a
	 * pattern substitution.
	 *
	 * @param baseTerm the base term
	 * @param patternSubstitution the pattern substitution
	 * @return the built simple pattern term, or <code>null</code>
	 * if the substitution is not simple or the term cannot be built
	 */
	private static SimplePatternTerm tryBuildSimplePatternTerm(
			Term baseTerm,
			PatternSubstitution patternSubstitution) {

		if (patternSubstitution instanceof SimplePatternSubstitution)
			return SimplePatternTerm.tryBuild(baseTerm, patternSubstitution);

		return null;
	}

	/**
	 * Disables construction.
	 */
	private PatternRuleLpFactory() {
	}
}
