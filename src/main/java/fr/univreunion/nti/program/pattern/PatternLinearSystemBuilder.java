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

package fr.univreunion.nti.program.pattern;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Builds the linear system used by pattern nontermination analysis.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternLinearSystemBuilder {

	/**
	 * Attempts to build the linear system induced by the provided pattern
	 * substitutions.
	 *
	 * @param left the substitution from the left-hand side of the pattern rule
	 * @param right the substitution from the right-hand side of the pattern rule
	 * @return the resulting linear system, or {@code null} if the substitutions
	 * have incompatible contexts or ground terms
	 */
	static LinearSystem tryBuild(Substitution left, Substitution right) {
		Set<Variable> domain = left.getDomain();
		domain.addAll(right.getDomain());

		List<EquationExponents> equations = new ArrayList<>();

		for (Variable variable : domain) {
			PatternTermDetails leftDetails =
					extractDetails(left.getOrDefault(variable, variable), variable);
			PatternTermDetails rightDetails =
					extractDetails(right.getOrDefault(variable, variable), variable);

			if (!haveCompatibleContextAndGroundTerm(leftDetails, rightDetails))
				return null;

			if (leftDetails.exponents().isEmpty() && rightDetails.exponents().isEmpty())
				continue;

			equations.add(new EquationExponents(
					leftDetails.exponents(), rightDetails.exponents()));
		}

		return buildMatrices(equations);
	}

	/**
	 * Checks whether two extracted term details have equal contexts and equal
	 * ground embedded terms.
	 *
	 * @param left the details extracted from the left side
	 * @param right the details extracted from the right side
	 * @return {@code true} if the contexts and embedded terms are compatible
	 */
	private static boolean haveCompatibleContextAndGroundTerm(
			PatternTermDetails left,
			PatternTermDetails right) {

		return left.context().deepEquals(right.context())
				&& left.embeddedTerm().isGround()
				&& right.embeddedTerm().isGround()
				&& left.embeddedTerm().deepEquals(right.embeddedTerm());
	}

	/**
	 * Builds the coefficient matrices from the exponent sequences collected for
	 * each equation.
	 *
	 * @param equations the paired exponent sequences, in equation order
	 * @return the constructed linear system
	 */
	private static LinearSystem buildMatrices(List<EquationExponents> equations) {

		int equationCount = equations.size();
		int variableCount = 0;
		for (EquationExponents equation : equations)
			variableCount = Math.max(variableCount, equation.variableCount());

		int[][] leftMatrix = new int[equationCount][];
		int[][] rightMatrix = new int[equationCount][];

		for (int i = 0; i < equationCount; i++) {
			EquationCoefficients coefficients =
					equations.get(i).toCoefficients(variableCount);
			leftMatrix[i] = coefficients.left();
			rightMatrix[i] = coefficients.right();
		}

		return new LinearSystem(equationCount, variableCount, leftMatrix, rightMatrix);
	}

	/** The paired exponent sequences defining one linear-system equation. */
	private record EquationExponents(
			List<Integer> left,
			List<Integer> right) {

		/** Returns the number of variables required by this equation. */
		private int variableCount() {
			return Math.max(this.left.size() - 1, this.right.size() - 1);
		}

		/** Converts this equation into left- and right-matrix rows. */
		private EquationCoefficients toCoefficients(int variableCount) {
			int[] leftCoefficients = new int[variableCount];
			int[] rightCoefficients = new int[variableCount + 1];
			int leftIndex = this.left.size() - 1;
			int rightIndex = this.right.size() - 1;

			rightCoefficients[variableCount] =
					this.right.get(rightIndex--) - this.left.get(leftIndex--);
			for (int column = variableCount - 1; 0 <= column; column--) {
				leftCoefficients[column] =
						0 <= leftIndex ? this.left.get(leftIndex--) : 0;
				rightCoefficients[column] =
						0 <= rightIndex ? this.right.get(rightIndex--) : 0;
			}

			return new EquationCoefficients(leftCoefficients, rightCoefficients);
		}
	}

	/** The coefficient-matrix rows generated for one equation. */
	private record EquationCoefficients(
			int[] left,
			int[] right) {
	}

	/**
	 * Extracts the exponent sequence, simple context, and embedded term from a
	 * term. A term that is not a hat function is represented with an empty
	 * exponent sequence and the provided empty context.
	 *
	 * @param term the term whose details are extracted
	 * @param emptyContext the context used when {@code term} is not a hat function
	 * @return the extracted context, embedded term, and exponent sequence
	 */
	private static PatternTermDetails extractDetails(
			Term term,
			Variable emptyContext) {

		if (term instanceof HatFunction hatFunction) {
			return new PatternTermDetails(
					hatFunction.getRootSymbol().getSimpleContext(),
					hatFunction.getArgument(),
					new ArrayList<>(hatFunction.getExponents()));
		}

		return new PatternTermDetails(emptyContext, term, List.of());
	}

	/** The details extracted from one side of a pattern equation. */
	private record PatternTermDetails(
			Term context,
			Term embeddedTerm,
			List<Integer> exponents) {
	}

	/**
	 * Prevents instantiation of this utility class.
	 */
	private PatternLinearSystemBuilder() {
	}
}
