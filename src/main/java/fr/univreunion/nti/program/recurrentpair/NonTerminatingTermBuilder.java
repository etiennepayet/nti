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
 * Builds the nonterminating term associated with a recurrent pair.
 */
final class NonTerminatingTermBuilder {

	/**
	 * This class cannot be instantiated.
	 */
	private NonTerminatingTermBuilder() {}

	/**
	 * Tries to build the nonterminating term associated with the
	 * recurrent pair being built.
	 * <p>
	 * If such a term cannot be built from the provided finite chains
	 * and the selected components of c1, then <code>null</code> is
	 * returned.
	 *
	 * @param input the input data for building the term
	 * @return a nonterminating term, or <code>null</code>
	 */
	static synchronized Function tryBuild(
			NonTerminatingTermInput input, HolePositions holePositions) {

		for (int k = 0; k < input.root().arity(); k++)
			if (k != holePositions.squareIndex() &&
					k != holePositions.squarePrimeIndex()) {
				Term u1ChildAtIndex = input.chains().u1().getChild(k);
				if (!(u1ChildAtIndex.unifyWith(input.chains().v1().getChild(k)) &&
						u1ChildAtIndex.unifyWith(input.chains().u2().getChild(k)) &&
						u1ChildAtIndex.unifyWith(input.chains().v2().getChild(k))))
					// If a nonterminating term cannot be built
					// then we stop because another i or another j
					// will not work. Indeed, at that point, the
					// square' component of u1 has the form
					// c2^m1[y], while the square' component of v1
					// has the form c2^n2[y] with n2 < m1. Hence,
					// these components do not unify. We have
					// something similar at the square index i.
					return null;
			}

		return holePositions.buildFunction(
				input.root(),
				input.s(),
				input.c2PowerM2OfS(),
				input.chains().u1());
	}
}
