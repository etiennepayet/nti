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

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;

/**
 * Builds recurrent pairs from finite chains.
 */
final class RecurrentPairBuilder {

	/**
	 * This class cannot be instantiated.
	 */
	private RecurrentPairBuilder() {}

	/**
	 * Tries to build a recurrent pair from the provided elements.
	 * <p>
	 * If a recurrent pair cannot be built then
	 * <code>null</code> is returned.
	 *
	 * @param u1 the lhs of the first  finite chain
	 * @param v1 the rhs of the first  finite chain
	 * @param u2 the lhs of the second finite chain
	 * @param v2 the rhs of the second finite chain
	 * @return a recurrent pair, or <code>null</code>
	 */
	static synchronized RecurrentPair tryBuild(
			Function u1, Term v1, Function u2, Term v2) {

		if (v1.isVariable() || v2.isVariable() ||
				!v1.hasSameStructureAs(u2) ||
				!v2.hasSameStructureAs(u1))
			return null;

		// At this point, v1 and v2 are not variables.
		// Since v1 has the same structure as the function u2,
		// and v2 has the same structure as the function u1,
		// both v1 and v2 must be functions.
		Function functionV1 = (Function) v1;
		Function functionV2 = (Function) v2;

		// Each orientation attempt checks that all terms have
		// the form f(...) for the same function symbol f.

		RecurrentPair result = tryBuildWithOriginalOrientation(
				u1, functionV1, u2, functionV2);
		if (result == null)
			result = tryBuildWithSwappedOrientation(
					u1, functionV1, u2, functionV2);

		return result;
	}

	/**
	 * Tries to build a recurrent pair while preserving the order
	 * of the provided finite chains.
	 *
	 * @param u1 the lhs of the first finite chain
	 * @param v1 the rhs of the first finite chain
	 * @param u2 the lhs of the second finite chain
	 * @param v2 the rhs of the second finite chain
	 * @return a recurrent pair, or <code>null</code>
	 */
	private static synchronized RecurrentPair tryBuildWithOriginalOrientation(
			Function u1, Function v1, Function u2, Function v2) {

		return (v1.hasSameStructureAs(u1) ?
			tryBuildFromOrientedChains(u1, v1, u2, v2) :
			null);
	}

	/**
	 * Tries to build a recurrent pair after swapping the order
	 * of the provided finite chains.
	 *
	 * @param u1 the lhs of the first finite chain
	 * @param v1 the rhs of the first finite chain
	 * @param u2 the lhs of the second finite chain
	 * @param v2 the rhs of the second finite chain
	 * @return a recurrent pair, or <code>null</code>
	 */
	private static synchronized RecurrentPair tryBuildWithSwappedOrientation(
			Function u1, Function v1, Function u2, Function v2) {

		return (v2.hasSameStructureAs(u2) ?
			tryBuildFromOrientedChains(u2, v2, u1, v1) :
			null);
	}

	/**
	 * Tries to build a recurrent pair from the provided oriented finite chains.
	 * <p>
	 * The provided terms necessarily have the
	 * form f(...) for the same function symbol f.
	 *
	 * @param u1 the lhs of the first finite chain
	 * of the built recurrent pair
	 * @param v1 the rhs of the first finite chain
	 * of the built recurrent pair
	 * @param u2 the lhs of the second finite chain
	 * of the built recurrent pair
	 * @param v2 the rhs of the second finite chain
	 * of the built recurrent pair
	 * @return a recurrent pair, or <code>null</code>
	 */
	private static synchronized RecurrentPair tryBuildFromOrientedChains(
			Function u1, Function v1, Function u2, Function v2) {

		FiniteChains chains = FiniteChains.flattenedCopyOf(u1, v1, u2, v2);

		return RecurrentPairSearch.tryBuild(chains);
	}
}
