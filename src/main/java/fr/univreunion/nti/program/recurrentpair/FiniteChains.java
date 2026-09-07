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

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;

/**
 * Finite chains used to build a recurrent pair.
 *
 * @param u1 the lhs of the first finite chain
 * @param v1 the rhs of the first finite chain
 * @param u2 the lhs of the second finite chain
 * @param v2 the rhs of the second finite chain
 */
record FiniteChains(
		Function u1,
		Function v1,
		Function u2,
		Function v2) {

	/**
	 * Flattens both finite chains by deep-copying the terms of each chain
	 * with a dedicated copy map.
	 *
	 * @param u1 the lhs of the first finite chain
	 * @param v1 the rhs of the first finite chain
	 * @param u2 the lhs of the second finite chain
	 * @param v2 the rhs of the second finite chain
	 * @return the flattened chains
	 */
	static FiniteChains flattenedCopyOf(
			Function u1, Function v1, Function u2, Function v2) {

		// We flatten u1 and v1 (i.e., make each subterm the
		// only element of its class and be its own schema).
		Map<Term, Term> firstChainCopies = new HashMap<>();
		u1 = (Function) u1.deepCopy(firstChainCopies);
		v1 = (Function) v1.deepCopy(firstChainCopies);

		// We also flatten u2 and v2.
		Map<Term, Term> secondChainCopies = new HashMap<>();
		u2 = (Function) u2.deepCopy(secondChainCopies);
		v2 = (Function) v2.deepCopy(secondChainCopies);

		return new FiniteChains(u1, v1, u2, v2);
	}
}
