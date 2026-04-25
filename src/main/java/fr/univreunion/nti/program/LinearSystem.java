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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program;

/**
 * A class for handling linear systems of <code>n</code>
 * equations with <code>p</code> variables and of the
 * form <code>AX = B</code> where <code>A</code>
 * is a <code>n x p</code> matrix of natural numbers,
 * <code>X</code> is a vector of <code>p</code> variables
 * and <code>B</code> is a vector of <code>n</code>
 * <code>p+1</code>-tuples of natural numbers.
 * 
 * It is used in the nontermination analysis based
 * on pattern terms. In this technique, we have to 
 * decide nontermination from binary rules
 * <code>p :- q</code> where <code>p</code> and
 * <code>q</code> are pattern terms of the form
 * <ul>
 * <li><code>p = 
 * c(c_1^{a_{1,1},...,a_{1,p},b_1}(u_1),...,c_n^{a_{n,1},...,a_{n,p},b_n}(u_n))
 * </code></li>
 * <li><code>q =
 * c(c_1^{a'_{1,1},...,a'_{1,p},b'_1}(u_1),...,c_n^{a'_{n,1},...,a'_{n,p},b'_n}(u_n))
 * </code></li>
 * </ul>
 * where <code>c</code> is a ground <code>n</code>-context,
 * the <code>c_i</code>'s are ground 1-contexts,
 * the <code>a_{i,j}</code>'s and <code>b_i</code>'s
 * are naturals and the
 * <code>u_i</code>'s are ground terms.
 * We have to prove that for all tuples
 * <code>(n'_1,...,n'_p)</code> of naturals
 * there exists a tuple
 * <code>(n_1,...,n_p)</code> of naturals
 * such that
 * <code>q(n'_1,...,n'_p) = p(n_1,...,n_p)</code>.
 * Hence, we solve the linear system
 * <code>
 * a_{1,1}x_1 + ... a_{1,p}x_p = a'_{1,1}x'_1 + ... a'_{1,p}x'_p + (b'_1 - b_1)
 * ...
 * a_{n,1}x_1 + ... a_{n,p}x_p = a'_{n,1}x'_1 + ... a'_{n,p}x'_p + (b'_n - b_n)
 * </code>
 * i.e., we try to express each <code>x_i</code>
 * as a linear combination of <code>x_j</code>'s.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LinearSystem {

	/**
	 * The number of equations.
	 */
	private final int n;

	/**
	 * The number of variables.
	 */
	private final int p;

	/**
	 * A <code>n x p</code> matrix of natural numbers.
	 */
	private final int[][] a;

	/**
	 * A <code>n x p+1</code> matrix of natural numbers.
	 */
	private final int[][] b;

	/**
	 * Builds a linear system.
	 * 
	 * @param n the number of equations
	 * @param p the number of variables
	 * @param a a <code>n x p</code>
	 * matrix of natural numbers
	 * @param b a <code>n x p+1</code>
	 * matrix of natural numbers
	 */
	public LinearSystem(int n, int p, int[][] a, int[][] b) {
		if (a.length != n || b.length != n)
			throw new IllegalArgumentException(
					"construction of a LinearSystem with a matrix of illegal dimension");

		this.a = a;
		this.b = b;
		this.n = n;
		this.p = p;
	}

	/**
	 * Attempts to put this linear system in
	 * solved form using the Gauss-Jordan
	 * elimination algorithm. If the number
	 * of variables is different from the
	 * number of equations then fails and
	 * returns <code>false</code>.
	 * 
	 * BEWARE: this method may modify the
	 * matrices of this system, even if
	 * the transformation fails.
	 * 
	 * @return <code>true</code> iff the
	 * transformation succeeds
	 */
	public boolean solveGauss() {
		// If there are as many variables as equations
		// then we compute the echelon form of the system.
		if (this.p == this.n && this.setInEchelonForm()) {
			// We solve the system from its echelon form.
			// We only consider the first p rows (the
			// next rows contain only zeros, see above).
			for (int i = this.p - 1; 0 <= i; i--) {
				int factor_i = this.a[i][i];
				
				if (factor_i == 0) return false;
				
				for (int j = i + 1; j < this.p; j++) {
					int factor_ij = this.a[i][j];
					if (factor_ij % factor_i != 0)
						// We are only interested in linear
						// combinations with natural coefficients.
						return false;
					factor_ij /= factor_i;
					for (int k = 0; k <= this.p; k++)
						b[i][k] -= factor_ij * b[j][k];
					this.a[i][j] = 0;
				}
				this.a[i][i] = 1;
			}

			return true;
		}

		// Else, we cannot solve the system.
		return false;
	}

	/**
	 * Attempts to set this system in echelon form.
	 * 
	 * @return <code>true</code> upon success
	 * and <code>false</code> upon failure
	 */
	public boolean setInEchelonForm() {
		int pivot_row = 0;
		int pivot_col = 0;

		while (pivot_row < this.n && pivot_col < this.p) {
			// Find the next pivot row, i.e.,
			// max(|A[i,pivot_col]|, pivot_row <= i < n).
			int i_max = pivot_row;
			for (int i = pivot_row + 1; i < this.n; i++)
				if (Math.abs(this.a[i][pivot_col]) > Math.abs(this.a[i_max][pivot_col]))
					i_max = i;

			if (this.a[i_max][pivot_col] == 0)
				// No pivot in this column, pass to 
				// the next column.
				pivot_col += 1;
			else {
				// If necessary, swap rows pivot_row and i_max.
				if (pivot_row != i_max) {
					int[] temp = this.a[pivot_row];
					this.a[pivot_row] = this.a[i_max];
					this.a[i_max] = temp;

					temp = this.b[pivot_row];
					this.b[pivot_row] = this.b[i_max];
					this.b[i_max] = temp;
				}

				// Elimination
				// Do for all rows below pivot_row.
				for (int i = pivot_row + 1; i < this.n; i++) {
					if (this.a[i][pivot_col] % this.a[pivot_row][pivot_col] != 0)
						// We are only interested in linear
						// combinations with natural coefficients.
						return false;
					int factor = this.a[i][pivot_col] / this.a[pivot_row][pivot_col];

					// Fill with zeros the lower part of pivot_col.
					this.a[i][pivot_col] = 0; 
					// Do for all remaining elements in current row.
					for (int j = pivot_col + 1; j < this.p; j++)
						this.a[i][j] -= factor * this.a[pivot_row][j];
					for (int j = 0; j <= this.p; j++)
						this.b[i][j] -= factor * this.b[pivot_row][j];
				}

				// Increase pivot_row and pivot_col.
				pivot_row += 1;
				pivot_col += 1;
			}
		}

		return true;
	}

	/**
	 * Returns a string representation of this
	 * linear system.
	 */
	@Override
	public String toString () {
		StringBuffer s = new StringBuffer("n = " + n + ", p = " + p + "\n");

		for (int i = 0; i < this.n; i++) {
			// We compute the String representation
			// of a[i].
			for (int j = 0; j < this.p; j++) {
				s.append(this.a[i][j]);
				s.append(" ");
			}
			s.append("= ");
			// We compute the String representation
			// of b[i].
			for (int j = 0; j <= this.p; j++) {
				s.append(this.b[i][j]);
				s.append(" ");
			}
			s.append("\n");
		}

		return s.toString();
	}
}
