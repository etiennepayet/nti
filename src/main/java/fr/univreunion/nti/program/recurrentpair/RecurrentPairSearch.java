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

/**
 * Searches for a recurrent pair from oriented finite chains.
 */
final class RecurrentPairSearch {

	/**
	 * This class cannot be instantiated.
	 */
	private RecurrentPairSearch() {}

	/**
	 * Tries to build a recurrent pair by enumerating positions of
	 * square and square' below the common root symbol.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @return a recurrent pair, or <code>null</code>
	 */
	static synchronized RecurrentPair tryBuild(FiniteChains chains) {

		// We try to compute c1, c2, s, t,
		// m1, m2, n1, ..., n4.
		// For the sake of simplicity, we compute
		// a ground s and a ground c2; moreover,
		// we compute a context c1 of the form
		// f(...) where the holes square and square'
		// are direct children of f with exactly
		// one occurrence each. We let i (resp. j)
		// be the index of square (resp. square')
		// in c1, i.e., square (resp. square') is
		// the i-th (resp. j-th) child of f.

		RootSymbol root = RootSymbol.of(chains.u1().getRootSymbol());

		// First, we identify the
		// index i of square.
		for (int i = 0; i < root.arity(); i++) {
			SquarePosition squarePosition =
					HolePositionAnalyzer.tryBuildSquarePosition(
							chains, i, root);
			if (squarePosition == null) continue;

			RecurrentPairSearchAttempt buildAttempt = tryBuildForSquarePosition(
					chains,
					root,
					squarePosition);
			RecurrentPair recurrentPair = buildAttempt.recurrentPair();
			if (recurrentPair != null) return recurrentPair;
			if (buildAttempt.abortsSearch()) return null;
		}

		return null;
	}

	/**
	 * Tries to build a recurrent pair for a selected square position
	 * by enumerating possible positions for square'.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @param root the leading function symbol of c1 and its arity
	 * @param squarePosition the selected position for square
	 * @return the result of the build attempt
	 */
	private static synchronized RecurrentPairSearchAttempt tryBuildForSquarePosition(
			FiniteChains chains,
			RootSymbol root,
			SquarePosition squarePosition) {

		for (int squarePrimeIndex = 0;
				squarePrimeIndex < root.arity();
				squarePrimeIndex++) {
			if (squarePrimeIndex == squarePosition.index()) continue;

			HolePositions holePositions = new HolePositions(
					squarePosition.index(),
					squarePrimeIndex,
					squarePosition.x1(),
					squarePosition.x2());
			RecurrentPairSearchAttempt buildAttempt =
					RecurrentPairCandidateEvaluator.tryBuild(
							chains,
							root,
							holePositions);
			RecurrentPair recurrentPair = buildAttempt.recurrentPair();
			if (recurrentPair != null) return buildAttempt;
			if (buildAttempt.abortsSearch()) return buildAttempt;
		}

		return RecurrentPairSearchAttempt.rejected();
	}
}
