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

import java.util.LinkedList;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Analyzes pattern rules for a ground nonterminating term.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternNonTerminationAnalyzer {

	/**
	 * Attempts to produce a ground nonterminating term and compute its
	 * <code>alpha</code> threshold.
	 *
	 * @param left the left-hand side of the rule
	 * @param right the right-hand side of the rule
	 * @return the analysis result
	 */
	static PatternNonTerminationAnalysis analyze(
			SimplePatternTerm left, SimplePatternTerm right) {

		if (right == null) return PatternNonTerminationAnalysis.failure();

		int alpha = computeAlphaWithRefactoring(left, right);
		if (alpha < 0) return PatternNonTerminationAnalysis.failure();

		return new PatternNonTerminationAnalysis(
				buildGroundWitness(left, alpha), alpha);
	}

	/**
	 * Builds a ground nontermination witness from the original left-hand side.
	 *
	 * @param originalLeft the original left-hand side
	 * @param alpha the computed alpha threshold
	 * @return the ground witness
	 */
	private static Function buildGroundWitness(
			SimplePatternTerm originalLeft, int alpha) {

		Term instantiatedLeft = originalLeft.instantiateAt(alpha);
		Function constant = new Function(
				FunctionSymbol.intern("0", 0),
				new LinkedList<>());
		return (Function) instantiatedLeft.replaceVariables(constant);
	}

	/**
	 * Computes alpha directly, then from refactored sides upon failure.
	 *
	 * @param left the original left-hand side
	 * @param right the original right-hand side
	 * @return the threshold, or a negative value upon failure
	 */
	private static int computeAlphaWithRefactoring(
			SimplePatternTerm left, SimplePatternTerm right) {

		int alpha = computeAlpha(left, right);
		if (0 <= alpha) return alpha;

		RefactoredPatternRule refactored =
				PatternRuleRefactorer.tryRefactor(left, right);
		return refactored == null
				? -1
				: computeAlpha(refactored.left(), refactored.right());
	}

	/**
	 * Computes the <code>alpha</code> threshold of a non-fact rule.
	 *
	 * @param left the left-hand side
	 * @param right the right-hand side
	 * @return the threshold, or a negative value upon failure
	 */
	private static int computeAlpha(
			SimplePatternTerm left, SimplePatternTerm right) {

		Term leftBase = left.getBaseTerm();
		Term rightBase = right.getBaseTerm();
		Substitution leftHatFunctionSubstitution =
				left.getPatternSubstitution().getHatFunctionSubstitution();
		Substitution rightHatFunctionSubstitution =
				right.getPatternSubstitution().getHatFunctionSubstitution();

		Substitution renaming = new Substitution();
		if (!leftBase.isVariantOf(rightBase, renaming)) return -1;
		if (!leftHatFunctionSubstitution.getDomain()
				.containsAll(leftBase.getVariables())) return -1;

		Substitution renamedLeftHatFunctionSubstitution =
				leftHatFunctionSubstitution.renameWith(renaming);
		return computeAlphaFromSubstitutions(
				renamedLeftHatFunctionSubstitution,
				rightHatFunctionSubstitution);
	}

	/**
	 * Computes alpha from compatible hat-function substitutions.
	 *
	 * @param renamedLeft the renamed left substitution
	 * @param right the right substitution
	 * @return the threshold, or a negative value upon failure
	 */
	private static int computeAlphaFromSubstitutions(
			Substitution renamedLeft,
			Substitution right) {

		SpecialRuleCoefficients coefficients =
				SpecialRuleCoefficientExtractor.extract(
						renamedLeft,
						right);
		if (coefficients != null) return coefficients.computeAlpha();

		LinearSystem linearSystem = PatternLinearSystemBuilder.tryBuild(
				renamedLeft,
				right);
		return linearSystem != null && linearSystem.solve() ? 0 : -1;
	}

	/** Prevents instantiation of this utility class. */
	private PatternNonTerminationAnalyzer() {
	}
}
