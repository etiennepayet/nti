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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.Verbosity;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;

class DependencyPairAttemptSummaryFormatterTest {

	@Test
	@DisplayName("format outer and inner attempts in their supplied order")
	void formatOuterAndInnerAttemptsInTheirSuppliedOrder() throws Exception {
		DependencyPairInfinitenessAttempt failedInner = innerAttempt(
				1, 1, "FirstProcessor", false, "first inner trace");
		DependencyPairInfinitenessAttempt successfulInner = innerAttempt(
				1, 2, "SecondProcessor", true, "second inner trace");
		DependencyPairInfinitenessAttempt cancelledInner = innerAttempt(
				2, 1, "CancelledProcessor", true, "cancelled inner trace");
		failedInner.call();
		successfulInner.call();
		Thread.currentThread().interrupt();
		try {
			cancelledInner.call();
		}
		finally {
			assertTrue(Thread.interrupted());
		}

		Proof successfulProof = proof(Proof.ProofResult.NO, true,
				"outer successful trace");
		DependencyPairFrameworkAttempt successfulOuter =
				new DependencyPairFrameworkAttempt(
						"Unfiltered", () -> successfulProof,
						() -> List.of(
								failedInner, successfulInner, cancelledInner));
		successfulOuter.call();

		Proof unsuccessfulProof = proof(Proof.ProofResult.MAYBE, false,
				"outer unsuccessful trace");
		DependencyPairFrameworkAttempt unsuccessfulOuter =
				new DependencyPairFrameworkAttempt(
						"Argument-filtered", () -> unsuccessfulProof);
		unsuccessfulOuter.call();

		String summary = DependencyPairAttemptSummaryFormatter.format(
				List.of(successfulOuter, unsuccessfulOuter));

		assertEquals("""
				* Concurrent TRS proof attempts:
				  - Unfiltered: successful (NO)
				    - problem 1 / processor 1 (FirstProcessor): unsuccessful (FAILED)
				    - problem 1 / processor 2 (SecondProcessor): successful (INFINITE)
				    - problem 2 / processor 1 (CancelledProcessor): cancelled
				  - Argument-filtered: unsuccessful (MAYBE)""", summary);
		assertFalse(summary.contains("trace"));
	}

	@Test
	@DisplayName("render concise failures only in very verbose output")
	void renderConciseOuterAndInnerFailuresOnlyInVeryVerboseOutput() {
		DependencyPairInfinitenessAttempt inner =
				new DependencyPairInfinitenessAttempt(
						1, 1, "FailingProcessor", () -> {
							throw new IllegalArgumentException(
									"processor failure");
						});
		assertThrows(IllegalArgumentException.class, inner::call);
		DependencyPairFrameworkAttempt outer =
				new DependencyPairFrameworkAttempt(
						"Failing variant", () -> {
							throw new IllegalStateException("variant failure");
						}, () -> List.of(inner));
		assertThrows(IllegalStateException.class, outer::call);
		Proof veryVerboseReport = new Proof(Verbosity.VERY_VERBOSE);
		Proof verboseReport = new Proof(Verbosity.VERBOSE);

		DependencyPairAttemptSummaryFormatter.appendTo(
				veryVerboseReport, List.of(outer));
		DependencyPairAttemptSummaryFormatter.appendTo(
				verboseReport, List.of(outer));

		String veryVerboseOutput = veryVerboseReport.toString();
		assertTrue(veryVerboseOutput.contains(
				"[cause: IllegalStateException: variant failure]"));
		assertTrue(veryVerboseOutput.contains(
				"[cause: IllegalArgumentException: processor failure]"));
		assertFalse(verboseReport.toString().contains("[cause:"));
	}

	@Test
	@DisplayName("format attempts without retained results")
	void formatAttemptsWithoutRetainedResults() {
		DependencyPairFrameworkAttempt pending =
				new DependencyPairFrameworkAttempt(
						"Pending", () -> new Proof(true));
		DependencyPairFrameworkAttempt error =
				new DependencyPairFrameworkAttempt("Error", () -> {
					throw new IllegalStateException("failure details");
				});
		try {
			error.call();
		}
		catch (Exception ignored) {
			// The formatter reports the state, not the failure trace.
		}

		String summary = DependencyPairAttemptSummaryFormatter.format(
				List.of(pending, error));

		assertEquals("""
				* Concurrent TRS proof attempts:
				  - Pending: pending
				  - Error: error""", summary);
		assertFalse(summary.contains("failure details"));
	}

	@Test
	@DisplayName("append the summary only to a verbose proof")
	void appendSummaryOnlyToVerboseProof() throws Exception {
		DependencyPairFrameworkAttempt attempt =
				new DependencyPairFrameworkAttempt(
						"Unfiltered", () -> proof(
								Proof.ProofResult.YES, true, "ignored trace"));
		attempt.call();
		Proof verboseProof = new Proof(true);
		Proof conciseProof = new Proof(false);

		DependencyPairAttemptSummaryFormatter.appendTo(
				verboseProof, List.of(attempt));
		DependencyPairAttemptSummaryFormatter.appendTo(
				conciseProof, List.of(attempt));

		assertTrue(verboseProof.toString().contains("""
				* Concurrent TRS proof attempts:
				  - Unfiltered: successful (YES)"""));
		assertFalse(conciseProof.toString().contains(
				"Concurrent TRS proof attempts"));
	}

	@Test
	@DisplayName("format detailed traces and availability markers in supplied order")
	void formatDetailedTracesAndAvailabilityMarkersInSuppliedOrder()
			throws Exception {
		DependencyPairInfinitenessAttempt retainedInner = innerAttempt(
				1, 1, "RetainedProcessor", false, "retained inner trace");
		retainedInner.call();
		DependencyPairInfinitenessAttempt unavailableInner =
				new DependencyPairInfinitenessAttempt(
						1, 2, "UnavailableProcessor", () -> null);

		Proof outerProof = proof(
				Proof.ProofResult.NO, true, "retained outer trace");
		DependencyPairFrameworkAttempt retainedOuter =
				new DependencyPairFrameworkAttempt(
						"Retained", () -> outerProof,
						() -> List.of(retainedInner, unavailableInner));
		retainedOuter.call();
		DependencyPairFrameworkAttempt unavailableOuter =
				new DependencyPairFrameworkAttempt("Unavailable", () -> null);

		String details = DependencyPairAttemptSummaryFormatter.formatDetailed(
				List.of(retainedOuter, unavailableOuter));

		int retainedOuterIndex = details.indexOf("  ** Retained:");
		int retainedInnerIndex = details.indexOf(
				"    ** problem 1 / processor 1 (RetainedProcessor):");
		int unavailableInnerIndex = details.indexOf(
				"    ** problem 1 / processor 2 (UnavailableProcessor):");
		int unavailableOuterIndex = details.indexOf("  ** Unavailable:");
		assertTrue(details.startsWith(
				"* Detailed concurrent TRS proof attempts:"));
		assertTrue(retainedOuterIndex >= 0);
		assertTrue(retainedInnerIndex > retainedOuterIndex);
		assertTrue(unavailableInnerIndex > retainedInnerIndex);
		assertTrue(unavailableOuterIndex > unavailableInnerIndex);
		assertTrue(details.contains("retained outer trace"));
		assertTrue(details.contains("retained inner trace"));
		assertEquals(2, details.split("\\[trace unavailable]", -1).length - 1);
	}

	private static DependencyPairInfinitenessAttempt innerAttempt(
			int problemPosition,
			int processorPosition,
			String processorIdentity,
			boolean infinite,
			String trace) {

		return new DependencyPairInfinitenessAttempt(
				problemPosition, processorPosition, processorIdentity, () -> {
					Proof proof = new Proof(true);
					proof.println(trace);
					return infinite
							? DependencyPairProcessorResult.infinite(proof)
							: DependencyPairProcessorResult.failed(proof);
				});
	}

	private static Proof proof(
			Proof.ProofResult result, boolean successful, String trace) {
		Proof proof = new Proof(true);
		proof.setResult(result);
		if (successful)
			proof.setArgument("successful proof");
		proof.println(trace);
		return proof;
	}
}
