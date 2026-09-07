/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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

/**
 * Evaluates one candidate pair of hole positions during recurrent-pair search.
 */
final class RecurrentPairCandidateEvaluator {

	/**
	 * This class cannot be instantiated.
	 */
	private RecurrentPairCandidateEvaluator() {}

	/**
	 * Tries to build a recurrent pair for the provided hole positions.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @param root the leading function symbol of c1 and its arity
	 * @param holePositions the selected hole positions
	 * @return the result of the build attempt
	 */
	static synchronized RecurrentPairSearchAttempt tryBuild(
			FiniteChains chains,
			RootSymbol root,
			HolePositions holePositions) {

		SquarePrimePosition squarePrimePosition =
				HolePositionAnalyzer.tryBuildSquarePrimePosition(
						chains, holePositions, root);
		if (squarePrimePosition == null)
			return RecurrentPairSearchAttempt.rejected();

		FirstChainParameters firstChainParameters =
				tryComputeFirstChainParameters(
						chains,
						holePositions,
						squarePrimePosition);
		if (firstChainParameters == null)
			return RecurrentPairSearchAttempt.rejected();

		SecondChainParameters secondChainParameters =
				tryComputeSecondChainParameters(
						chains,
						holePositions,
						squarePrimePosition,
						firstChainParameters);
		if (secondChainParameters == null)
			return RecurrentPairSearchAttempt.rejected();

		Function nonTerminatingTerm =
				tryBuildNonTerminatingTerm(
						chains,
						root,
						holePositions,
						squarePrimePosition,
						secondChainParameters);

		if (nonTerminatingTerm == null)
			return RecurrentPairSearchAttempt.abortSearch();

		AcceptedRecurrentPairCandidate candidate =
				new AcceptedRecurrentPairCandidate(
						firstChainParameters,
						secondChainParameters,
						nonTerminatingTerm);

		return RecurrentPairSearchAttempt.found(
				new RecurrentPair(candidate.toData(
						chains,
						root,
						holePositions)));
	}

	/**
	 * Tries to compute the first-chain parameters for the provided
	 * candidate hole positions.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @param holePositions the selected hole positions
	 * @param squarePrimePosition the position data for square'
	 * @return the first-chain parameters, or <code>null</code>
	 */
	private static synchronized FirstChainParameters tryComputeFirstChainParameters(
			FiniteChains chains,
			HolePositions holePositions,
			SquarePrimePosition squarePrimePosition) {

		FirstChainInput firstChainInput = new FirstChainInput(
				chains,
				holePositions,
				squarePrimePosition);

		return FirstChainParameterComputer.tryCompute(firstChainInput);
	}

	/**
	 * Tries to compute the second-chain parameters from the already
	 * accepted first-chain parameters.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @param holePositions the selected hole positions
	 * @param squarePrimePosition the position data for square'
	 * @param firstChainParameters the first-chain parameters
	 * @return the second-chain parameters, or <code>null</code>
	 */
	private static synchronized SecondChainParameters tryComputeSecondChainParameters(
			FiniteChains chains,
			HolePositions holePositions,
			SquarePrimePosition squarePrimePosition,
			FirstChainParameters firstChainParameters) {

		SecondChainInput secondChainInput = new SecondChainInput(
				squarePrimePosition.s(),
				firstChainParameters.c2(),
				holePositions.x2(),
				chains.v2().getChild(holePositions.squareIndex()),
				firstChainParameters.n2(),
				firstChainParameters.n4(),
				firstChainParameters.delta());

		return SecondChainParameterComputer.tryCompute(secondChainInput);
	}

	/**
	 * Tries to build the generated nonterminating term.
	 *
	 * @param chains the finite chains of the built recurrent pair
	 * @param root the leading function symbol of c1 and its arity
	 * @param holePositions the selected hole positions
	 * @param squarePrimePosition the position data for square'
	 * @param secondChainParameters the second-chain parameters
	 * @return the generated nonterminating term, or <code>null</code>
	 */
	private static synchronized Function tryBuildNonTerminatingTerm(
			FiniteChains chains,
			RootSymbol root,
			HolePositions holePositions,
			SquarePrimePosition squarePrimePosition,
			SecondChainParameters secondChainParameters) {

		NonTerminatingTermInput nonTerminatingTermInput =
				new NonTerminatingTermInput(
						chains,
						root,
						secondChainParameters.s(),
						squarePrimePosition.s());

		return NonTerminatingTermBuilder.tryBuild(
				nonTerminatingTermInput,
				holePositions);
	}
}
