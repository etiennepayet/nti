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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.concurrent.CompletionService;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.Proof;

class LpProofAttemptTest {

	@Test
	@DisplayName("retain a conclusive result and its local proof")
	void retainConclusiveResultAndLocalProof() throws Exception {
		Proof proof = new Proof(true);
		ResultLp result = ResultLp.yes(proof);
		LpProofAttempt attempt =
				new LpProofAttempt("test prover", proof, () -> result);
		ExecutorService executor = Executors.newSingleThreadExecutor();
		CompletionService<ResultLp> completions =
				new ExecutorCompletionService<>(executor);

		assertEquals(LpProofAttempt.Status.PENDING, attempt.status());
		assertEquals("test prover: pending", attempt.summary());
		assertNull(attempt.result());
		Future<ResultLp> future = attempt.submitTo(completions);
		executor.shutdown();

		assertSame(result, future.get(1, TimeUnit.SECONDS));
		executor.close();
		assertEquals(LpProofAttempt.Status.CONCLUSIVE, attempt.status());
		assertSame(result, attempt.result());
		assertSame(proof, attempt.proof());
		assertEquals("test prover", attempt.name());
		assertEquals("test prover: conclusive (YES)", attempt.summary());
	}

	@Test
	@DisplayName("classify inconclusive and error results")
	void classifyInconclusiveAndErrorResults() throws Exception {
		Proof inconclusiveProof = new Proof(false);
		LpProofAttempt inconclusive = new LpProofAttempt(
				"inconclusive", inconclusiveProof,
				() -> ResultLp.maybe(inconclusiveProof));
		Proof errorProof = new Proof(false);
		LpProofAttempt error = new LpProofAttempt(
				"error", errorProof, () -> ResultLp.error(errorProof));

		inconclusive.call();
		error.call();

		assertEquals(LpProofAttempt.Status.INCONCLUSIVE,
				inconclusive.status());
		assertEquals(LpProofAttempt.Status.ERROR, error.status());
		assertEquals("inconclusive: inconclusive (MAYBE)",
				inconclusive.summary());
		assertEquals("error: error", error.summary());
	}

	@Test
	@DisplayName("record an error state while propagating a serious error")
	void recordErrorStateWhilePropagatingSeriousError() {
		AssertionError failure = new AssertionError("serious failure");
		LpProofAttempt attempt = new LpProofAttempt(
				"error", new Proof(false), () -> {
					throw failure;
				});

		AssertionError propagated = assertThrows(
				AssertionError.class, attempt::call);

		assertSame(failure, propagated);
		assertEquals(LpProofAttempt.Status.ERROR, attempt.status());
	}

	@Test
	@DisplayName("finish cancellation before executor termination")
	void finishCancellationBeforeExecutorTermination() throws Exception {
		CountDownLatch started = new CountDownLatch(1);
		CountDownLatch finished = new CountDownLatch(1);
		Proof proof = new Proof(true);
		LpProofAttempt attempt = new LpProofAttempt(
				"cancelled", proof,
				() -> {
					started.countDown();
					try {
						new CountDownLatch(1).await();
						return ResultLp.maybe(proof);
					}
					finally {
						finished.countDown();
					}
				});
		ExecutorService executor = Executors.newSingleThreadExecutor();
		CompletionService<ResultLp> completions =
				new ExecutorCompletionService<>(executor);
		Future<ResultLp> future = attempt.submitTo(completions);
		assertTrue(started.await(1, TimeUnit.SECONDS));
		assertEquals("cancelled: running", attempt.summary());

		LpTerminationProver.cancelAndAwaitProofAttempts(
				List.of(attempt), executor);

		assertTrue(future.isCancelled());
		assertTrue(finished.await(1, TimeUnit.SECONDS));
		assertEquals(LpProofAttempt.Status.CANCELLED, attempt.status());
		assertEquals("cancelled: cancelled", attempt.summary());
		assertNull(attempt.result());
	}

	@Test
	@DisplayName("retain cancellation when the computation absorbs interruption")
	void retainCancellationWhenComputationAbsorbsInterruption() throws Exception {
		CountDownLatch started = new CountDownLatch(1);
		Proof proof = new Proof(true);
		LpProofAttempt attempt = new LpProofAttempt(
				"cancelled", proof, () -> {
					started.countDown();
					try {
						new CountDownLatch(1).await();
					}
					catch (InterruptedException ignored) {
						// Simulates a prover that consumes the interruption.
					}
					return ResultLp.maybe(proof);
				});
		ExecutorService executor = Executors.newSingleThreadExecutor();
		CompletionService<ResultLp> completions =
				new ExecutorCompletionService<>(executor);
		attempt.submitTo(completions);
		assertTrue(started.await(1, TimeUnit.SECONDS));

		LpTerminationProver.cancelAndAwaitProofAttempts(
				List.of(attempt), executor);

		assertEquals(LpProofAttempt.Status.CANCELLED, attempt.status());
		assertEquals("cancelled: cancelled", attempt.summary());
	}
}
