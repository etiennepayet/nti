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

import java.util.Set;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Analyzes candidate positions for square and square' in <code>c1</code>.
 */
final class HolePositionAnalyzer {

	/**
	 * This class cannot be instantiated.
	 */
	private HolePositionAnalyzer() {}

	/**
	 * Tries to identify a valid square position.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @param squareIndex the position of square in c1
	 * @param root the leading function symbol of c1 and its arity
	 * @return the validated square position,
	 * or <code>null</code>
	 */
	static synchronized SquarePosition tryBuildSquarePosition(
			FiniteChains chains, int squareIndex, RootSymbol root) {

		Term x1 = chains.u1().getChild(squareIndex);
		Term x2 = chains.u2().getChild(squareIndex);
		if (x1.isVariable() && x2.isVariable() &&
				occursOnlyAt(x1, chains.u1(), squareIndex, root) &&
				occursOnlyAt(x1, chains.v1(), squareIndex, root) &&
				occursOnlyAt(x2, chains.u2(), squareIndex, root))
			return new SquarePosition(squareIndex, x1, x2);

		return null;
	}

	/**
	 * Tries to identify the position of square' in c1.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @param holePositions the selected hole positions
	 * @param root the leading function symbol of c1 and its arity
	 * @return the position data for square', or <code>null</code>
	 */
	static synchronized SquarePrimePosition tryBuildSquarePrimePosition(
			FiniteChains chains, HolePositions holePositions, RootSymbol root) {

		// A starting point for identifying s.
		Term s = chains.u2().getChild(holePositions.squarePrimeIndex());

		// We only consider ground c2's and s's.
		if (!s.isGround()) return null;

		Term u1AtSquarePrimeIndex =
				chains.u1().getChild(holePositions.squarePrimeIndex());
		Term v1AtSquarePrimeIndex =
				chains.v1().getChild(holePositions.squarePrimeIndex());
		Set<Variable> variablesOfU1AtSquarePrimeIndex =
				u1AtSquarePrimeIndex.getVariables();
		Set<Variable> variablesOfV1AtSquarePrimeIndex =
				v1AtSquarePrimeIndex.getVariables();

		if (variablesOfU1AtSquarePrimeIndex.size() != 1 ||
				variablesOfV1AtSquarePrimeIndex.size() != 1)
			return null;

		Variable y1 = variablesOfU1AtSquarePrimeIndex.iterator().next();
		if (holePositions.x1() == y1 ||
				y1 != variablesOfV1AtSquarePrimeIndex.iterator().next() ||
				!occursOnlyAt(y1, chains.u1(),
						holePositions.squarePrimeIndex(), root) ||
				!occursOnlyAt(y1, chains.v1(),
						holePositions.squarePrimeIndex(), root) ||
				!holePositions.occursOnlyAt(
						holePositions.x2(), chains.v2(), root))
			return null;

		return new SquarePrimePosition(
				s,
				u1AtSquarePrimeIndex,
				v1AtSquarePrimeIndex,
				y1);
	}

	/**
	 * Checks whether the given term occurs only at the
	 * allowed position of the given function.
	 *
	 * @param term a term whose presence is to be tested
	 * @param function a function where the check occurs
	 * @param allowedIndex a position at which the presence is allowed
	 * @param root the root function symbol of <code>function</code>
	 * and its arity
	 * @return <code>true</code> iff <code>term</code>
	 * occurs only at position <code>allowedIndex</code>
	 * of <code>function</code>
	 */
	private static synchronized boolean occursOnlyAt(
			Term term, Function function, int allowedIndex, RootSymbol root) {

		for (int k = 0; k < root.arity(); k++)
			if (k != allowedIndex && function.getChild(k).contains(term))
				return false;

		return true;
	}
}
