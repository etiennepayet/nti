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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.lp;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;

class ModeNonTerminationTrackerTest {

	@Test
	@DisplayName("accept only the first proof that contributes a mode witness")
	void acceptOnlyFirstContributingProof() {
		Mode trackedMode = mode("tracker-mode");
		ModeNonTerminationTracker tracker =
				new ModeNonTerminationTracker(trackedMode);
		Proof firstContribution = verboseProof("first contribution");
		Proof laterContribution = verboseProof("later contribution");
		Proof nonContributingProof = verboseProof("non-contributing work");

		assertTrue(tracker.hasRemainingMode());
		tracker.checkWitnesses(
				List.of(new TestWitness(mode("other-mode"), "unrelated witness")),
				nonContributingProof);
		tracker.checkWitnesses(
				List.of(new TestWitness(trackedMode, "first witness")),
				firstContribution);
		tracker.checkWitnesses(
				List.of(new TestWitness(trackedMode, "later witness")),
				laterContribution);

		assertFalse(tracker.hasRemainingMode());
		assertTrue(tracker.hasContributionFrom(firstContribution));
		assertFalse(tracker.hasContributionFrom(laterContribution));
		assertFalse(tracker.hasContributionFrom(nonContributingProof));
		assertTrue(tracker.completeProofIfModeProved(nonContributingProof));
		assertFalse(nonContributingProof.toString().contains("first contribution"));

		Proof finalProof = new Proof(true);
		assertTrue(tracker.completeAggregatedProofIfModeProved(finalProof));

		String rendering = finalProof.toString();
		assertTrue(rendering.startsWith("NO"));
		assertTrue(rendering.contains("Mode tracker-mode"));
		assertTrue(rendering.contains("first contribution"));
		assertFalse(rendering.contains("later contribution"));
		assertFalse(rendering.contains("non-contributing work"));
	}

	private static Mode mode(String name) {
		return new Mode(FunctionSymbol.intern(name, 0), List.of());
	}

	private static Proof verboseProof(String description) {
		Proof proof = new Proof(true);
		proof.printlnIfVerbose(description);
		return proof;
	}

	private record TestWitness(Mode mode, String description)
			implements NonTerminationWitness {

		@Override
		public NonTerminationWitness add(BinaryRuleLp rule) {
			return this;
		}

		@Override
		public Function provesNonTerminationOf(Mode candidateMode) {
			return candidateMode == this.mode ? new Function(
					this.mode.getPredSymbol(), List.of()) : null;
		}

		@Override
		public String getShortDescription() {
			return "(" + this.description + ")";
		}

		@Override
		public String toString() {
			return this.description;
		}
	}
}
