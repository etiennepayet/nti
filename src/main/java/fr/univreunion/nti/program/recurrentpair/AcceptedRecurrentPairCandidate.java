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
 * A candidate whose parameters and generated nonterminating term are accepted.
 *
 * @param firstChainParameters the computed first-chain parameters
 * @param secondChainParameters the computed second-chain parameters
 * @param nonTerminatingTerm the generated nonterminating term
 */
record AcceptedRecurrentPairCandidate(
		FirstChainParameters firstChainParameters,
		SecondChainParameters secondChainParameters,
		Function nonTerminatingTerm) {

	/**
	 * Builds the recurrent-pair certificate components from this candidate.
	 *
	 * @param chains the finite chains of this recurrent pair
	 * @param root the leading function symbol of <code>c1</code> and its arity
	 * @param holePositions the selected hole positions
	 * @return the recurrent-pair certificate components
	 */
	RecurrentPairData toData(
			FiniteChains chains,
			RootSymbol root,
			HolePositions holePositions) {

		return RecurrentPairData.from(
				chains,
				root,
				holePositions,
				this.firstChainParameters,
				this.secondChainParameters,
				this.nonTerminatingTerm);
	}
}
