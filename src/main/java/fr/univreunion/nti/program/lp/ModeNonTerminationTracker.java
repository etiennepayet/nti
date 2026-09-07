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

package fr.univreunion.nti.program.lp;

import java.util.Collection;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.lp.argument.ArgumentModeLp;
import fr.univreunion.nti.term.Function;

/**
 * Tracks whether the query mode of an LP has been proved nonterminating.
 * <p>
 * This class is shared by the concurrent nontermination provers
 * of a logic program. Its methods are synchronized so that several
 * provers can safely report new nontermination witnesses.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ModeNonTerminationTracker {

	/**
	 * The mode whose nontermination has to be proved.
	 */
	private final Mode mode;

	/**
	 * The accepted nontermination argument, or {@code null} until a witness is
	 * found.
	 */
	private ArgumentModeLp argument;

	/**
	 * The proof that supplied the accepted witness, or {@code null} while no
	 * witness has been accepted.
	 */
	private Proof contributingProof;

	/**
	 * Builds a tracker for the provided mode.
	 *
	 * @param mode the mode whose nontermination has to be proved
	 * @throws IllegalArgumentException if {@code mode} is {@code null}
	 */
	public ModeNonTerminationTracker(Mode mode) {
		if (mode == null)
			throw new IllegalArgumentException(
					"construction of a mode tracker with a null mode");
		this.mode = mode;
	}

	/**
	 * Checks whether the mode still has to be proved nonterminating.
	 *
	 * @return {@code true} iff the mode remains to be proved nonterminating
	 */
	public synchronized boolean hasRemainingMode() {
		return this.argument == null;
	}

	/**
	 * Checks the provided nontermination witnesses against the mode until one
	 * succeeds or the current thread is interrupted.
	 *
	 * @param witnesses a collection of nontermination witnesses
	 * @param proof the nontermination proof in construction
	 */
	public synchronized void checkWitnesses(
			Collection<? extends NonTerminationWitness> witnesses,
			Proof proof) {

		if (this.argument != null)
			return;

		Thread currentThread = Thread.currentThread();
		for (NonTerminationWitness witness : witnesses) {
			if (currentThread.isInterrupted())
				return;

			Function nonterminatingQuery = witness.provesNonTerminationOf(this.mode);
			if (nonterminatingQuery != null) {
				this.contributingProof = proof;
				this.argument = new ArgumentModeLp(
						this.mode, nonterminatingQuery, witness);
				proof.printlnIfVerbose("The mode " + this.mode + " is nonterminating. " +
						"The generated witness is:\n  " + witness + "\n");
				return;
			}
		}
	}

	/**
	 * Completes the specified proof if the mode has been proved nonterminating
	 * by a witness reported to this tracker.
	 *
	 * @param proof the proof to complete
	 * @return <code>true</code> iff the proof was completed
	 */
	public synchronized boolean completeProofIfModeProved(Proof proof) {
		if (this.argument != null)
			return this.completeProof(proof);

		return false;
	}

	/**
	 * Completes the specified final proof from the shared nontermination argument
	 * and the description of the proof that supplied the accepted witness.
	 *
	 * @param proof the final proof to complete
	 * @return <code>true</code> iff the proof was completed
	 */
	synchronized boolean completeAggregatedProofIfModeProved(Proof proof) {
		if (this.argument == null)
			return false;

		proof.merge(this.contributingProof);

		return this.completeProof(proof);
	}

	/**
	 * Checks whether the specified local proof contributed the accepted
	 * nontermination witness.
	 *
	 * @param proof the local proof to inspect
	 * @return <code>true</code> iff the proof contributed an accepted witness
	 */
	synchronized boolean hasContributionFrom(Proof proof) {
		return this.contributingProof == proof;
	}

	/**
	 * Assigns the shared nontermination result and argument to the specified
	 * proof.
	 *
	 * @param proof the proof to complete
	 * @return <code>true</code>
	 */
	private boolean completeProof(Proof proof) {
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(this.argument);
		return true;
	}
}
