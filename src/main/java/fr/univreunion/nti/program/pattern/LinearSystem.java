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

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

/**
 * A class for handling parametric linear systems of the form
 * {@code AX = CX' + d}, where {@code A} and {@code C} are
 * {@code n x m} matrices of naturals, {@code X} and {@code X'} are
 * vectors of {@code m} variables ranging over the naturals, and {@code d}
 * is a vector of {@code n} integers.
 * <p>
 * For compactness, {@code C} and {@code d} are stored together in an
 * {@code n x (m+1)} matrix {@code B = (C | d)}. Thus, the first {@code m}
 * columns of {@code B} contain naturals, whereas its last column may contain
 * negative integers.
 * <p>
 * It is used in the nontermination analysis based
 * on pattern terms. In this technique, we have to
 * decide nontermination from pattern rules
 * <code>(p,q)</code>, where <code>p</code> and
 * <code>q</code> are pattern terms of the form
 * <ul>
 * <li><code>p =
 * c(c_1^{a_{1,1},...,a_{1,m},b_1}(u_1),...,c_n^{a_{n,1},...,a_{n,m},b_n}(u_n))
 * </code></li>
 * <li><code>q =
 * c(c_1^{a'_{1,1},...,a'_{1,m},b'_1}(u_1),...,c_n^{a'_{n,1},...,a'_{n,m},b'_n}(u_n))
 * </code></li>
 * </ul>
 * where <code>c</code> is a ground <code>n</code>-context,
 * the <code>c_i</code>'s are ground 1-contexts,
 * the <code>a_{i,j}</code>'s and <code>b_i</code>'s
 * are naturals and the
 * <code>u_i</code>'s are ground terms.
 * We have to prove that
 * <pre>
 * for all tuples {@code (x'_1,...,x'_m)} of naturals,
 * there exists a tuple {@code (x_1,...,x_m)} of naturals
 * such that {@code q(x'_1,...,x'_m) = p(x_1,...,x_m)}.</pre>
 * Note that
 * <ul>
 *     <li>{@code
 *     p(x_1,...,x_m) =
 *     c(c_1^{a_{1,1}*x_1+...+a_{1,m}*x_m+b_1}(u_1),...,c_n^{a_{n,1}*x_1+...+a_{n,m}*x_m+b_n}(u_n))
 *     }</li>
 *     <li>{@code
 *     q(x'_1,...,x'_m) =
 *     c(c_1^{a'_{1,1}*x'_1+...+a'_{1,m}*x'_m+b'_1}(u_1),...,c_n^{a'_{n,1}*x'_1+...+a'_{n,m}*x'_m+b'_n}(u_n))
 *     }</li>
 * </ul>
 * Hence, {@code q(x'_1,...,x'_m) = p(x_1,...,x_m)} is equivalent to
 * <pre>{@code
 * a_{1,1}*x_1 + ... + a_{1,m}*x_m + b_1 = a'_{1,1}*x'_1 + ... + a'_{1,m}*x'_m + b'_1
 * ...
 * a_{n,1}*x_1 + ... + a_{n,m}*x_m + b_n = a'_{n,1}*x'_1 + ... + a'_{n,m}*x'_m + b'_n
 * }</pre>
 * So, we have to solve the linear system
 * <pre>{@code
 * a_{1,1}*x_1 + ... + a_{1,m}*x_m = a'_{1,1}*x'_1 + ... + a'_{1,m}*x'_m + (b'_1 - b_1)
 * ...
 * a_{n,1}*x_1 + ... + a_{n,m}*x_m = a'_{n,1}*x'_1 + ... + a'_{n,m}*x'_m + (b'_n - b_n)
 * }</pre>
 * whose variables are {@code (x_1,...,x_m)}, and these variables range
 * in the set of naturals.
 * <p>
 * This class attempts to establish the required property by looking for a
 * natural affine solution {@code X = DX' + e}. Equivalently, it looks for a
 * natural {@code m x m} matrix {@code D} and a natural vector {@code e} such
 * that {@code AD = C} and {@code Ae = d}. Such a solution proves the required
 * universally quantified property for matrices of any dimensions and ranks.
 * The converse does not hold in general: solutions may depend on {@code X'}
 * in a non-affine, for instance periodic, way.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LinearSystem {

	/**
	 * The number of equations.
	 */
	private final int equationCount;

	/**
	 * The number of variables.
	 */
	private final int variableCount;

	/**
	 * The {@code n x m} matrix {@code A} of natural coefficients.
	 */
	private final int[][] a;

	/**
	 * The {@code n x (m+1)} matrix {@code B = (C | d)}. Its first {@code m}
	 * columns contain natural coefficients and its last column contains integer
	 * constants.
	 */
	private final int[][] b;

	/**
	 * Builds a linear system. The provided matrices are deeply copied, so later
	 * modifications to them do not affect this system.
	 *
	 * @param equationCount the number of equations
	 * @param variableCount the number of variables
	 * @param a the {@code n x m} matrix {@code A} of natural coefficients
	 * @param b the {@code n x (m+1)} matrix {@code B = (C | d)}, whose first
	 * {@code m} columns contain naturals and whose last column contains integers
	 * @throws IllegalArgumentException if a count is negative, a matrix has an
	 * illegal dimension, or a coefficient required to be natural is negative
	 */
	public LinearSystem(
			int equationCount, int variableCount, int[][] a, int[][] b) {
		if (equationCount < 0 || variableCount < 0)
			throw new IllegalArgumentException(
					"construction of a LinearSystem with a negative dimension");
		if (a.length != equationCount || b.length != equationCount)
			throw new IllegalArgumentException(
					"construction of a LinearSystem with a matrix of illegal dimension");

		for (int row = 0; row < equationCount; row++) {
			if (a[row].length != variableCount
					|| b[row].length != variableCount + 1)
				throw new IllegalArgumentException(
						"construction of a LinearSystem with a matrix of illegal dimension");

			for (int column = 0; column < variableCount; column++)
				if (a[row][column] < 0 || b[row][column] < 0)
					throw new IllegalArgumentException(
							"construction of a LinearSystem with a negative natural coefficient");
		}

		this.a = copyMatrix(a);
		this.b = copyMatrix(b);
		this.equationCount = equationCount;
		this.variableCount = variableCount;
	}

	/**
	 * Returns a deep copy of a matrix.
	 *
	 * @param matrix the matrix to copy
	 * @return a new matrix containing copies of all rows of {@code matrix}
	 */
	private static int[][] copyMatrix(int[][] matrix) {
		int[][] copy = matrix.clone();
		for (int row = 0; row < copy.length; row++)
			copy[row] = copy[row].clone();
		return copy;
	}

	/**
	 * Attempts to prove that this system has a natural solution for every
	 * natural value of its parameters. The proof consists in finding a natural
	 * affine solution {@code X = DX' + e}.
	 * <p>
	 * This amounts to solving, over the naturals, one system {@code Az = b} for
	 * every column {@code b} of {@code B}. Unlike Gaussian elimination, this
	 * works with rectangular and rank-deficient matrices. This method does not
	 * modify the matrices of this system.
	 * <p>
	 * A {@code false} result only means that no natural affine solution exists.
	 * It does not imply that the universally quantified property itself is
	 * false, since it may have non-affine solutions.
	 *
	 * @return {@code true} iff this system has a natural affine solution
	 */
	public boolean solve() {
		for (int rightColumn = 0; rightColumn <= this.variableCount; rightColumn++) {
			int[] rightHandSide = new int[this.equationCount];
			for (int row = 0; row < this.equationCount; row++)
				rightHandSide[row] = this.b[row][rightColumn];

			if (!this.hasNaturalSolution(rightHandSide)) return false;
		}

		return true;
	}

	/**
	 * Checks whether {@code Az = rightHandSide} has a natural solution.
	 *
	 * @param rightHandSide the right-hand side to consider
	 * @return {@code true} iff a natural solution exists
	 */
	private boolean hasNaturalSolution(int[] rightHandSide) {
		for (int coefficient : rightHandSide)
			if (coefficient < 0) return false;

		int[][] columns = this.orderedColumns();
		int[][] suffixGcd = computeSuffixGcd(columns, this.equationCount);
		return hasNaturalSolution(
				0,
				columns,
				suffixGcd,
				rightHandSide,
				new HashSet<>());
	}

	/**
	 * Returns the columns of {@code A}, ordered to constrain the search early.
	 *
	 * @return the ordered columns
	 */
	private int[][] orderedColumns() {
		Integer[] columnIndexes = new Integer[this.variableCount];
		for (int column = 0; column < this.variableCount; column++)
			columnIndexes[column] = column;

		Arrays.sort(columnIndexes, (first, second) -> {
			int comparison = Integer.compare(
					this.nonzeroCount(second), this.nonzeroCount(first));
			return comparison != 0
					? comparison
					: Integer.compare(this.maximum(second), this.maximum(first));
		});

		int[][] columns = new int[this.variableCount][this.equationCount];
		for (int i = 0; i < this.variableCount; i++)
			for (int row = 0; row < this.equationCount; row++)
				columns[i][row] = this.a[row][columnIndexes[i]];

		return columns;
	}

	/**
	 * Returns the number of nonzero coefficients in a column of {@code A}.
	 *
	 * @param column the zero-based index of the column to inspect
	 * @return the number of nonzero coefficients in the selected column
	 */
	private int nonzeroCount(int column) {
		int count = 0;
		for (int row = 0; row < this.equationCount; row++)
			if (this.a[row][column] != 0) count++;
		return count;
	}

	/**
	 * Returns the greatest coefficient in a column of {@code A}.
	 *
	 * @param column the zero-based index of the column to inspect
	 * @return the greatest coefficient in the selected column
	 */
	private int maximum(int column) {
		int maximum = 0;
		for (int row = 0; row < this.equationCount; row++)
			maximum = Math.max(maximum, this.a[row][column]);
		return maximum;
	}

	/**
	 * Computes the row-wise gcd of every suffix of the provided columns.
	 *
	 * @param columns the ordered column vectors whose suffixes are considered
	 * @param equationCount the number of coefficients, one per equation, in
	 * each column vector
	 * @return the row-wise gcd values indexed by suffix start and equation
	 */
	private static int[][] computeSuffixGcd(int[][] columns, int equationCount) {
		int[][] suffixGcd = new int[columns.length + 1][equationCount];
		for (int column = columns.length - 1; 0 <= column; column--)
			for (int row = 0; row < equationCount; row++)
				suffixGcd[column][row] = gcd(
						columns[column][row], suffixGcd[column + 1][row]);
		return suffixGcd;
	}

	/**
	 * Searches the natural combinations of the provided columns recursively.
	 *
	 * @param column the index of the next column whose coefficient is to be
	 * selected
	 * @param columns the ordered column vectors available to the search
	 * @param suffixGcd the row-wise gcd values for all suffixes of
	 * {@code columns}
	 * @param residual the part of the right-hand side that remains to be
	 * expressed
	 * @param failedStates the previously explored states known to have no
	 * solution
	 * @return {@code true} iff the residual is a natural combination of the
	 * columns starting at {@code column}
	 */
	private static boolean hasNaturalSolution(
			int column,
			int[][] columns,
			int[][] suffixGcd,
			int[] residual,
			Set<SearchState> failedStates) {

		if (!isCompatibleWithSuffix(column, suffixGcd, residual)) return false;
		if (column == columns.length) return true;
		if (column == columns.length - 1)
			return isNaturalMultiple(columns[column], residual);

		SearchState state = new SearchState(column, residual);
		if (failedStates.contains(state)) return false;

		int upperBound = upperBound(columns[column], residual);
		if (upperBound < 0) {
			boolean result = hasNaturalSolution(
					column + 1, columns, suffixGcd, residual, failedStates);
			if (!result) failedStates.add(state);
			return result;
		}

		for (int coefficient = upperBound; 0 <= coefficient; coefficient--) {
			int[] nextResidual = residual.clone();
			for (int row = 0; row < residual.length; row++)
				nextResidual[row] -= coefficient * columns[column][row];

			if (hasNaturalSolution(
					column + 1,
					columns,
					suffixGcd,
					nextResidual,
					failedStates))
				return true;
		}

		failedStates.add(state);
		return false;
	}

	/**
	 * Checks the necessary gcd conditions for the remaining columns.
	 *
	 * @param column the index of the first remaining column
	 * @param suffixGcd the row-wise gcd values for all column suffixes
	 * @param residual the right-hand-side coefficients still to be expressed
	 * @return {@code true} iff every residual coefficient is divisible by the
	 * corresponding suffix gcd, with a zero gcd requiring a zero residual
	 */
	private static boolean isCompatibleWithSuffix(
			int column, int[][] suffixGcd, int[] residual) {

		for (int row = 0; row < residual.length; row++) {
			int divisor = suffixGcd[column][row];
			if (divisor == 0) {
				if (residual[row] != 0) return false;
			}
			else if (residual[row] % divisor != 0)
				return false;
		}
		return true;
	}

	/**
	 * Returns the largest possible natural coefficient for one column.
	 *
	 * @param column the column vector whose coefficient is to be bounded
	 * @param residual the right-hand-side coefficients still to be expressed
	 * @return the largest coefficient that does not exceed any residual, or
	 * {@code -1} if {@code column} is the zero vector
	 */
	private static int upperBound(int[] column, int[] residual) {
		int upperBound = Integer.MAX_VALUE;
		for (int row = 0; row < residual.length; row++)
			if (column[row] != 0)
				upperBound = Math.min(upperBound, residual[row] / column[row]);
		return upperBound == Integer.MAX_VALUE ? -1 : upperBound;
	}

	/**
	 * Checks whether the residual is a natural multiple of one column.
	 *
	 * @param column the column vector whose multiples are considered
	 * @param residual the vector to compare with a multiple of {@code column}
	 * @return {@code true} iff one natural multiplier maps {@code column} to
	 * {@code residual}
	 */
	private static boolean isNaturalMultiple(int[] column, int[] residual) {
		int multiplier = -1;
		for (int row = 0; row < residual.length; row++) {
			if (column[row] == 0) {
				if (residual[row] != 0) return false;
			}
			else {
				if (residual[row] % column[row] != 0) return false;
				int rowMultiplier = residual[row] / column[row];
				if (multiplier < 0) multiplier = rowMultiplier;
				else if (multiplier != rowMultiplier) return false;
			}
		}
		return true;
	}

	/**
	 * Returns the greatest common divisor of two nonnegative integers.
	 *
	 * @param first the first nonnegative integer
	 * @param second the second nonnegative integer
	 * @return the greatest common divisor of {@code first} and {@code second}
	 */
	private static int gcd(int first, int second) {
		while (second != 0) {
			int remainder = first % second;
			first = second;
			second = remainder;
		}
		return first;
	}

	/**
	 * A failed recursive-search state, compared using residual contents.
	 *
	 * @param column the index of the next column to explore
	 * @param residual the remaining right-hand side, copied by the canonical
	 * constructor
	 */
	private record SearchState(int column, int[] residual) {

		private SearchState(int column, int[] residual) {
			this.column = column;
			this.residual = residual.clone();
		}

		/**
		 * Checks whether another object represents the same search state.
		 *
		 * @param other the object to compare with this state
		 * @return {@code true} iff the column and residual contents are equal
		 */
		@Override
		public boolean equals(Object other) {
			return this == other
					|| other instanceof SearchState(int otherColumn, int[] otherResidual)
					&& this.column == otherColumn
					&& Arrays.equals(this.residual, otherResidual);
		}

		@Override
		public int hashCode() {
			return 31 * this.column + Arrays.hashCode(this.residual);
		}
	}

	/**
	 * Returns a string representation of this
	 * linear system.
	 */
	@Override
	public String toString() {
		StringBuilder representation = new StringBuilder(
				"n = " + this.equationCount
						+ ", m = " + this.variableCount + "\n");

		for (int i = 0; i < this.equationCount; i++) {
			// We compute the String representation
			// of a[i].
			for (int j = 0; j < this.variableCount; j++) {
				representation.append(this.a[i][j]);
				representation.append(" ");
			}
			representation.append("= ");
			// We compute the String representation
			// of b[i].
			for (int j = 0; j <= this.variableCount; j++) {
				representation.append(this.b[i][j]);
				representation.append(" ");
			}
			representation.append("\n");
		}

		return representation.toString();
	}
}
