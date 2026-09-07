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
 * Result of trying to build a recurrent pair during search.
 *
 * @param recurrentPair the recurrent pair that was built,
 * or <code>null</code> if the search candidate did not produce one
 * @param abortsSearch whether the caller must stop trying other
 * search candidates
 */
record RecurrentPairSearchAttempt(
		RecurrentPair recurrentPair,
		boolean abortsSearch) {

	static RecurrentPairSearchAttempt found(RecurrentPair recurrentPair) {
		return new RecurrentPairSearchAttempt(recurrentPair, false);
	}

	static RecurrentPairSearchAttempt rejected() {
		return new RecurrentPairSearchAttempt(null, false);
	}

	static RecurrentPairSearchAttempt abortSearch() {
		return new RecurrentPairSearchAttempt(null, true);
	}
}
