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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.Verbosity;
import fr.univreunion.nti.term.FunctionSymbol;

class LpTerminationProverTest {

	@Test
	@DisplayName("build named proof attempts in stable submission order")
	void buildNamedProofAttemptsInStableSubmissionOrder() {
		Mode mode = new Mode(
				FunctionSymbol.intern("lp-attempt-order", 0), List.of());
		LpTerminationProver prover = new LpTerminationProver(
				new Lp("attempt-order.pl", List.of(), mode));
		AnalysisContext context = new AnalysisContext(false, null);
		ModeNonTerminationTracker tracker =
				new ModeNonTerminationTracker(mode);

		assertEquals(
				List.of("Binary unfolding", "Pattern unfolding"),
				prover.buildProofAttempts(null, context, tracker).stream()
						.map(LpProofAttempt::name)
						.toList());
		assertEquals(
				List.of("cTI", "Binary unfolding", "Pattern unfolding"),
				prover.buildProofAttempts("cti", context, tracker).stream()
						.map(LpProofAttempt::name)
						.toList());
	}

	@Test
	@DisplayName("restore interruption while waiting for concurrent provers")
	void restoreInterruptionWhileWaitingForConcurrentProvers() {
		Mode mode = new Mode(
				FunctionSymbol.intern("lp-termination-interruption", 0),
				List.of());
		Lp lp = new Lp("interrupted.pl", List.of(), mode);
		AnalysisContext context = new AnalysisContext(false, null);

		try {
			Thread.currentThread().interrupt();
			lp.proveTermination(context);

			assertTrue(Thread.currentThread().isInterrupted());
		} finally {
			Thread.interrupted();
		}
	}

	@Test
	@DisplayName("render all LP attempt traces in stable configured order")
	void renderAllLpAttemptTracesInStableConfiguredOrder() throws Exception {
		Mode mode = new Mode(
				FunctionSymbol.intern("lp-detailed-attempt-order", 0), List.of());
		ModeNonTerminationTracker tracker =
				new ModeNonTerminationTracker(mode);
		Proof ctiProof = new Proof(Verbosity.VERY_VERBOSE);
		ctiProof.println("cTI retained trace");
		LpProofAttempt cti = new LpProofAttempt(
				"cTI", ctiProof, () -> ResultLp.yes(ctiProof));
		Proof binaryProof = new Proof(Verbosity.VERY_VERBOSE);
		binaryProof.println("binary retained trace");
		LpProofAttempt binary = new LpProofAttempt(
				"Binary unfolding", binaryProof,
				() -> ResultLp.maybe(binaryProof));
		Proof patternProof = new Proof(Verbosity.VERY_VERBOSE);
		LpProofAttempt pattern = new LpProofAttempt(
				"Pattern unfolding", patternProof,
				() -> ResultLp.maybe(patternProof));
		cti.call();
		binary.call();
		Proof report = new Proof(Verbosity.VERY_VERBOSE);

		LpTerminationProver.appendProofAttemptSummary(
				report, List.of(cti, binary, pattern), tracker);

		String output = report.toString();
		int detailsIndex = output.indexOf(
				"* Detailed concurrent LP proof attempts:");
		int ctiIndex = output.indexOf("  ** cTI:", detailsIndex);
		int binaryIndex = output.indexOf(
				"  ** Binary unfolding:", ctiIndex);
		int patternIndex = output.indexOf(
				"  ** Pattern unfolding:", binaryIndex);
		assertTrue(detailsIndex >= 0);
		assertTrue(ctiIndex > detailsIndex);
		assertTrue(binaryIndex > ctiIndex);
		assertTrue(patternIndex > binaryIndex);
		assertTrue(output.contains("cTI retained trace"));
		assertTrue(output.contains("binary retained trace"));
		assertTrue(output.indexOf("[trace unavailable]", patternIndex)
				> patternIndex);
	}

	@Test
	@DisplayName("render a concise worker failure only in very verbose output")
	void renderConciseWorkerFailureOnlyInVeryVerboseOutput() {
		Mode mode = new Mode(
				FunctionSymbol.intern("lp-detailed-error", 0), List.of());
		ModeNonTerminationTracker tracker =
				new ModeNonTerminationTracker(mode);
		LpProofAttempt attempt = new LpProofAttempt(
				"Failing prover", new Proof(Verbosity.VERY_VERBOSE), () -> {
					throw new IllegalStateException("worker failure");
				});
		assertThrows(IllegalStateException.class, attempt::call);
		Proof veryVerboseReport = new Proof(Verbosity.VERY_VERBOSE);
		Proof verboseReport = new Proof(Verbosity.VERBOSE);

		LpTerminationProver.appendProofAttemptSummary(
				veryVerboseReport, List.of(attempt), tracker);
		LpTerminationProver.appendProofAttemptSummary(
				verboseReport, List.of(attempt), tracker);

		assertTrue(veryVerboseReport.toString().contains(
				"[cause: IllegalStateException: worker failure]"));
		assertFalse(verboseReport.toString().contains("[cause:"));
	}

	@Test
	@DisplayName("isolate arithmetic overflow and accept another conclusive attempt")
	void isolateArithmeticOverflowAndAcceptAnotherConclusiveAttempt() {
		Mode mode = new Mode(
				FunctionSymbol.intern("lp-arithmetic-overflow", 0), List.of());
		Lp lp = new Lp("arithmetic-overflow.pl", List.of(), mode);
		AnalysisContext context = new AnalysisContext(
				Verbosity.VERY_VERBOSE, null);
		ArithmeticException overflow =
				new ArithmeticException("exponent overflow");
		LpProofAttempt overflowingAttempt = new LpProofAttempt(
				"Pattern unfolding", context.createProof(), () -> {
					throw overflow;
				});
		Proof successfulProof = context.createProof();
		successfulProof.setResult(Proof.ProofResult.YES);
		successfulProof.setArgument("independent termination proof");
		LpProofAttempt successfulAttempt = new LpProofAttempt(
				"Independent prover", successfulProof, () -> {
					Thread.sleep(100);
					return ResultLp.yes(successfulProof);
				});
		LpTerminationProver prover = new LpTerminationProver(lp) {
			@Override
			List<LpProofAttempt> buildProofAttempts(
					String cti,
					AnalysisContext analysisContext,
					ModeNonTerminationTracker tracker) {
				return List.of(overflowingAttempt, successfulAttempt);
			}
		};

		Proof proof = prover.prove(context);

		assertEquals(Proof.ProofResult.YES, proof.getResult());
		assertEquals("independent termination proof", proof.getArgument().toString());
		assertEquals(LpProofAttempt.Status.ERROR, overflowingAttempt.status());
		assertSame(overflow, overflowingAttempt.failure());
		assertEquals(LpProofAttempt.Status.CONCLUSIVE, successfulAttempt.status());
		assertTrue(proof.toString().contains(
				"[cause: ArithmeticException: exponent overflow]"));
	}

	@Test
	@DisplayName("propagate a serious worker error through the coordinator")
	void propagateSeriousWorkerErrorThroughCoordinator() {
		Mode mode = new Mode(
				FunctionSymbol.intern("lp-coordinator-error", 0), List.of());
		Lp lp = new Lp("error.pl", List.of(), mode);
		AnalysisContext context = new AnalysisContext(false, null);
		AssertionError failure = new AssertionError("serious worker failure");
		Proof localProof = context.createProof();
		LpProofAttempt attempt = new LpProofAttempt(
				"error", localProof, () -> {
					throw failure;
				});
		LpTerminationProver prover = new LpTerminationProver(lp) {
			@Override
			List<LpProofAttempt> buildProofAttempts(
					String cti,
					AnalysisContext analysisContext,
					ModeNonTerminationTracker tracker) {
				return List.of(attempt);
			}
		};

		AssertionError propagated = assertThrows(
				AssertionError.class, () -> prover.prove(context));

		assertSame(failure, propagated);
		assertEquals(LpProofAttempt.Status.ERROR, attempt.status());
	}
}
