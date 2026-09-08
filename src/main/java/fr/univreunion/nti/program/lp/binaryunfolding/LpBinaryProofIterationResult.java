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

package fr.univreunion.nti.program.lp.binaryunfolding;

import fr.univreunion.nti.program.lp.ResultLp;

/**
 * The result of one binary-unfolding proof iteration.
 *
 * @param result the proof result to return, or <code>null</code>
 * when <code>completed</code> is <code>false</code>
 * @param completed whether the iteration completed the proof
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

record LpBinaryProofIterationResult(
		ResultLp result,
		boolean completed) {

	/**
	 * Returns the result for an iteration that did not complete the proof.
	 *
	 * @return a continuation result
	 */
	static LpBinaryProofIterationResult continueProof() {
		return new LpBinaryProofIterationResult(null, false);
	}

	/**
	 * Returns the result for an iteration that completed the proof.
	 *
	 * @param result the proof result to return
	 * @return a completed iteration result
	 */
	static LpBinaryProofIterationResult completedWith(ResultLp result) {
		return new LpBinaryProofIterationResult(result, true);
	}

	/**
	 * Returns whether this iteration completed the proof.
	 *
	 * @return <code>true</code> if this iteration completed the proof
	 */
	boolean completedProof() {
		return this.completed;
	}
}
