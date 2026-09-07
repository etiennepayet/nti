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
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Builds the result of one forward unfolding between two TRS pattern rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleTrsForwardUnfolder {

	/**
	 * Attempts one forward unfolding at the provided position.
	 *
	 * @param source the rule whose right-hand side is unfolded
	 * @param unfoldingRule the rule used for unfolding
	 * @param position the unfolding position in the source right-hand side
	 * @param rightAtPosition the source right-hand-side subterm at the position
	 * @param iteration the unfolding iteration of the resulting rule
	 * @return the unfolded rule, or {@code null} upon failure
	 */
	static PatternRuleTrs tryUnfold(
			PatternRuleTrs source,
			PatternRuleTrs unfoldingRule,
			Position position,
			SimplePatternTerm rightAtPosition,
			int iteration) {

		if (areStructurallyIncompatible(
				rightAtPosition.getUpsilon(),
				unfoldingRule.getLeft().getUpsilon()))
			return null;

		FreshUnfoldingParts freshParts = FreshUnfoldingParts.copyOf(unfoldingRule);
		SimplePatternSubstitution unifier =
				tryUnify(rightAtPosition.getUpsilon(), freshParts.leftUpsilon());
		if (unifier == null) return null;

		SimplePatternSubstitution leftSubstitution =
				source.getLeft().getPatternSubstitution().composeWith(unifier);
		if (leftSubstitution == null) return null;

		SimplePatternSubstitution rightSubstitution =
				source.getRight().getPatternSubstitution().composeWith(unifier);
		if (rightSubstitution == null) return null;

		SimplePatternSubstitution unfoldingRightSubstitution =
				composeFreshRightSubstitution(
						freshParts.rightSubstitution(), unifier);
		if (unfoldingRightSubstitution == null) return null;

		SimplePatternTerm newLeft = SimplePatternTerm.tryBuild(
				source.getLeft().getBaseTerm(), leftSubstitution);
		if (newLeft == null) return null;

		Substitution mergedRightSubstitution =
				rightSubstitution.getHatFunctionSubstitution().unionWith(
						unfoldingRightSubstitution.getHatFunctionSubstitution());
		if (mergedRightSubstitution == null) return null;

		rightSubstitution =
				SimplePatternSubstitution.tryBuildTakingOwnership(
						mergedRightSubstitution);
		if (rightSubstitution == null) return null;

		SimplePatternTerm newRight = source.getRight().tryBuildReplacingBaseTerm(
				position,
				freshParts.rightBase(),
				rightSubstitution);
		if (newRight == null) return null;

		return PatternRuleTrs.tryBuild(newLeft, newRight, iteration);
	}

	/**
	 * Composes the candidate right substitution with the unifier. When the former
	 * is empty, it is only queried and never retained; the freshly computed
	 * unifier is already the exact result and is no longer consumed elsewhere,
	 * so it can be reused directly.
	 *
	 * @param freshRightSubstitution the candidate right substitution, fresh when
	 * non-empty
	 * @param unifier the fresh unifier, relinquished by the caller after this call
	 * @return the composed substitution, or {@code null} upon failure
	 */
	private static SimplePatternSubstitution composeFreshRightSubstitution(
			SimplePatternSubstitution freshRightSubstitution,
			SimplePatternSubstitution unifier) {

		return freshRightSubstitution.getHatFunctionSubstitution().isEmpty() ?
				unifier : freshRightSubstitution.composeWith(unifier);
	}

	/**
	 * Attempts to unify two terms and to represent the result as a simple
	 * pattern substitution.
	 *
	 * @param left the first term
	 * @param right the second term
	 * @return the simple unifier, or {@code null} upon failure
	 */
	private static SimplePatternSubstitution tryUnify(Term left, Term right) {
		Substitution unifier = new Substitution();
		if (left.isUnifiableWith(right, unifier))
			return SimplePatternSubstitution.tryBuildTakingOwnership(unifier);
		return null;
	}

	/**
	 * Checks whether two terms have an ordinary function-symbol conflict which
	 * makes them non-unifiable. The traversal stops at variables and specialized
	 * terms, which retain the complete historical unification path.
	 *
	 * @param left the first term
	 * @param right the second term
	 * @return {@code true} only when the terms cannot be unifiable
	 */
	private static boolean areStructurallyIncompatible(Term left, Term right) {
		if (left instanceof Variable || right instanceof Variable)
			return false;
		if (!(left instanceof Function leftFunction) ||
				!(right instanceof Function rightFunction))
			return false;
		if (leftFunction.getRootSymbol() != rightFunction.getRootSymbol())
			return true;

		int arity = leftFunction.getRootSymbol().getArity();
		for (int index = 0; index < arity; index++)
			if (areStructurallyIncompatible(
					leftFunction.getChild(index),
					rightFunction.getChild(index)))
				return true;
		return false;
	}

	/**
	 * The fresh candidate components consumed by forward unfolding. One copy
	 * map preserves variable sharing between all three components.
	 *
	 * @param leftUpsilon the fresh left upsilon term used for unification
	 * @param rightBase the fresh right base term used for replacement
	 * @param rightSubstitution the right substitution used for composition; a
	 * non-empty value is fresh, while an empty value is borrowed read-only
	 */
	private record FreshUnfoldingParts(
			Term leftUpsilon,
			Term rightBase,
			SimplePatternSubstitution rightSubstitution) {

		/**
		 * Copies only the candidate components consumed by forward unfolding.
		 *
		 * @param rule the candidate rule
		 * @return the fresh candidate components
		 */
		private static FreshUnfoldingParts copyOf(PatternRuleTrs rule) {
			Map<Term, Term> copies = new HashMap<>();
			SimplePatternSubstitution rightSubstitution =
					rule.getRight().getPatternSubstitution();
			return new FreshUnfoldingParts(
					rule.getLeft().getUpsilon().deepCopy(copies),
					rule.getRight().getBaseTerm().deepCopy(copies),
					rightSubstitution.getHatFunctionSubstitution().isEmpty() ?
							rightSubstitution : rightSubstitution.deepCopy(copies));
		}
	}

	/** Prevents instantiation of this utility class. */
	private PatternRuleTrsForwardUnfolder() {
	}
}
