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

package fr.univreunion.nti.program.recurrentpair;

import fr.univreunion.nti.term.Term;

/**
 * Computes the parameters related to the second finite chain.
 */
final class SecondChainParameterComputer {

	/**
	 * This class cannot be instantiated.
	 */
	private SecondChainParameterComputer() {}

	/**
	 * Tries to compute the parameters related to the second finite chain.
	 * <p>
	 * The ordered cases are semantically significant: if variable
	 * <code>t</code> or ground <code>t</code> applies but cannot compute
	 * <code>m2</code>, later cases must not be tried.
	 *
	 * @param input the input data for computing the parameters
	 * @return the computed parameters, or <code>null</code>
	 */
	static synchronized SecondChainParameters tryCompute(
			SecondChainInput input) {

		int n3 = ContextTower.powerOf(
				input.v2AtSquareIndex(), input.c2(), input.x2());
		if (0 <= n3)
			return tryComputeWithVariableT(input, n3);

		n3 = ContextTower.powerOf(
				input.v2AtSquareIndex(), input.c2(), input.initialS());
		if (0 <= n3)
			return tryComputeWithGroundT(input, n3);

		return tryComputeWithV2AsBase(input);
	}

	/**
	 * Tries to compute second-chain parameters when <code>t</code>
	 * is the variable at the square position in <code>u2</code>.
	 *
	 * @param input the input data for computing the parameters
	 * @param n3 the integer n3
	 * @return the computed parameters, or <code>null</code>
	 */
	private static synchronized SecondChainParameters
			tryComputeWithVariableT(SecondChainInput input, int n3) {

		// Here, t = x2 necessarily
		// and s is a subterm of the
		// square' component of u2.
		if (0 < n3 % input.delta()) return null;
		for (int m2 = input.n2(); m2 <= input.n4(); m2++) {
			// If we don't have s = c2^m2[...]
			// then we won't have s = c2^m[...]
			// for any m >= m2.
			Term candidateS = ContextTower.baseOf(
					input.initialS(), input.c2(), m2);
			if (candidateS == null) break;
			if ((input.n4() - m2) % input.delta() == 0)
				return new SecondChainParameters(
						candidateS, input.x2(), m2, n3);
		}

		return null; // Here, we could not compute m2.
	}

	/**
	 * Tries to compute second-chain parameters when <code>t</code>
	 * is the current ground term <code>s</code>.
	 *
	 * @param input the input data for computing the parameters
	 * @param n3 the integer n3
	 * @return the computed parameters, or <code>null</code>
	 */
	private static synchronized SecondChainParameters
			tryComputeWithGroundT(SecondChainInput input, int n3) {

		// Here, t = s necessarily
		// and s is a subterm of the
		// square' component of u2.
		for (int m2 = input.n2(), adjustedN3 = n3 + input.n2();
				m2 <= input.n4();
				m2++, adjustedN3++) {
			// If we don't have s = c2^m2[...]
			// then we won't have s = c2^m[...]
			// for any m >= m2.
			Term candidateS = ContextTower.baseOf(
					input.initialS(), input.c2(), m2);
			if (candidateS == null) break;
			if (adjustedN3 % input.delta() == 0 &&
					(input.n4() - m2) % input.delta() == 0)
				return new SecondChainParameters(
						candidateS, candidateS, m2, adjustedN3);
		}

		return null; // Here, we could not compute m2.
	}

	/**
	 * Tries to compute second-chain parameters when the term at the
	 * square position in <code>v2</code> is the base of <code>s</code>.
	 *
	 * @param input the input data for computing the parameters
	 * @return the computed parameters, or <code>null</code>
	 */
	private static synchronized SecondChainParameters
			tryComputeWithV2AsBase(SecondChainInput input) {

		int m2 = ContextTower.powerOf(
				input.initialS(), input.c2(), input.v2AtSquareIndex());
		if (0 <= m2 &&
				input.n2() <= m2 &&
				m2 <= input.n4() &&
				(input.n4() - m2) % input.delta() == 0) {
			// Here, s = t = v2AtSquareIndex.
			// Hence, it is useless to proceed as
			// above, i.e., to consider the inner
			// subterms of v2AtSquareIndex.
			int n3 = 0; // consequently, n3 % delta = 0
			return new SecondChainParameters(
					input.v2AtSquareIndex(),
					input.v2AtSquareIndex(),
					m2,
					n3);
		}

		return null;
	}
}
