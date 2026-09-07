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

import java.util.Map;

import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternUtils;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Refactors pattern-rule sides into a form suitable for alpha computation.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleRefactorer {

	/**
	 * Attempts to refactor the two sides of a pattern rule.
	 *
	 * @param left the left-hand side
	 * @param right the right-hand side
	 * @return the refactored sides, or {@code null}
	 */
	static RefactoredPatternRule tryRefactor(
			SimplePatternTerm left, SimplePatternTerm right) {

		Term leftBase = left.getBaseTerm();
		Term rightBase = right.getBaseTerm();

		Substitution generalization = new Substitution();
		if (!leftBase.isMoreGeneralThan(rightBase, generalization)) return null;

		RefactoringSubstitutions substitutions =
				RefactoringSubstitutions.from(left, right);

		if (!applyGeneralization(generalization, substitutions))
			return null;

		SimplePatternSubstitution refactoredLeft =
				SimplePatternSubstitution.tryBuildTakingOwnership(
						substitutions.refactoredLeft());
		SimplePatternSubstitution refactoredRight =
				SimplePatternSubstitution.tryBuildTakingOwnership(
						substitutions.refactoredRight());
		if (refactoredLeft == null || refactoredRight == null) return null;

		return new RefactoredPatternRule(
				SimplePatternTerm.tryBuild(leftBase, refactoredLeft),
				SimplePatternTerm.tryBuild(rightBase, refactoredRight));
	}

	/**
	 * Applies the entries of a base-term generalization to both substitutions.
	 *
	 * @return {@code true} iff no generalized variable belongs to a pumping domain
	 */
	private static boolean applyGeneralization(
			Substitution generalization,
			RefactoringSubstitutions substitutions) {

		for (Map.Entry<Variable, Term> entry : generalization) {
			Variable variable = entry.getKey();
			Term image = entry.getValue();

			if (variable == image) continue;

			if (substitutions.isInPumpingDomain(variable))
				return false;

			Term context = PatternUtils.getContext(image, variable, new int[1]);
			if (context != null)
				substitutions.addContextualizedImages(variable, context);
		}

		return true;
	}

	/** Original substitutions and the mutable copies being refactored. */
	private record RefactoringSubstitutions(
			SimplePatternSubstitution originalLeft,
			SimplePatternSubstitution originalRight,
			Substitution refactoredLeft,
			Substitution refactoredRight) {

		/** Creates the substitution state for two pattern-rule sides. */
		private static RefactoringSubstitutions from(
				SimplePatternTerm left, SimplePatternTerm right) {

			SimplePatternSubstitution originalLeft = left.getPatternSubstitution();
			SimplePatternSubstitution originalRight = right.getPatternSubstitution();
			return new RefactoringSubstitutions(
					originalLeft,
					originalRight,
					new Substitution(originalLeft.getHatFunctionSubstitution()),
					new Substitution(originalRight.getHatFunctionSubstitution()));
		}

		/** Returns whether either original substitution pumps a variable. */
		private boolean isInPumpingDomain(Variable variable) {
			return this.originalLeft.inPumpingDomain(variable)
					|| this.originalRight.inPumpingDomain(variable);
		}

		/** Adds equivalent contextualized images to both mutable copies. */
		private void addContextualizedImages(Variable variable, Term context) {
			HatFunctionSymbol symbol = HatFunctionSymbol.intern(context, variable);
			HatFunction leftHatFunction = new HatFunction(
					symbol,
					this.originalLeft.getHatFunctionSubstitution()
							.getOrDefault(variable, variable),
					0, 0);
			HatFunction rightHatFunction = new HatFunction(
					symbol,
					this.originalRight.getHatFunctionSubstitution()
							.getOrDefault(variable, variable),
					0, 0);
			this.refactoredLeft.addReplace(variable, leftHatFunction);
			this.refactoredRight.addReplace(variable, rightHatFunction);
		}
	}

	/** Prevents instantiation of this utility class. */
	private PatternRuleRefactorer() {
	}
}
