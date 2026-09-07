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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.dependencypair.DependencyGraphLimitException;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;

class ConcurrentDependencyPairFrameworkRunnerTest {

	@Test
	@DisplayName("return the first successful proof and cancel the other variant")
	void returnFirstSuccessfulProofAndCancelOtherVariant() throws Exception {
		CountDownLatch blockingVariantStarted = new CountDownLatch(1);
		CountDownLatch blockingVariantInterrupted = new CountDownLatch(1);
		AnalysisContext context = context();
		Proof successfulProof = successfulProof(context);
		DependencyPairFrameworkAttempt blockingAttempt = attempt(
				"blocking", () -> {
					blockingVariantStarted.countDown();
					try {
						new CountDownLatch(1).await();
					}
					catch (InterruptedException e) {
						blockingVariantInterrupted.countDown();
					}
					return failedProof(context, "cancelled");
				});
		DependencyPairFrameworkAttempt successfulAttempt = attempt(
				"successful", () -> {
					if (!blockingVariantStarted.await(2, TimeUnit.SECONDS))
						return failedProof(context, "not started");
					return successfulProof;
				});

		Proof proof = new ConcurrentDependencyPairFrameworkRunner().run(
				List.of(blockingAttempt, successfulAttempt),
				context.createProof());

		assertSame(successfulProof, proof);
		assertEquals(DependencyPairFrameworkAttempt.Status.SUCCESSFUL,
				successfulAttempt.status());
		assertEquals(DependencyPairFrameworkAttempt.Status.CANCELLED,
				blockingAttempt.status());
		assertSame(successfulProof, successfulAttempt.proof());
		assertTrue(blockingVariantInterrupted.await(2, TimeUnit.SECONDS));
		assertTrue(successfulAttempt.infinitenessAttempts().isEmpty());
	}

	@Test
	@DisplayName("retain the inner report of a completed variant")
	void retainInnerReportOfCompletedVariant() throws Exception {
		AnalysisContext context = context();
		DependencyPairInfinitenessAttempt innerAttempt = innerAttempt(context);
		innerAttempt.call();
		List<DependencyPairInfinitenessAttempt> suppliedReport =
				new LinkedList<>(List.of(innerAttempt));
		DependencyPairFrameworkAttempt outerAttempt = attempt(
				"successful", () -> successfulProof(context),
				() -> suppliedReport);

		new ConcurrentDependencyPairFrameworkRunner().run(
				List.of(outerAttempt), context.createProof());
		suppliedReport.clear();

		assertEquals(List.of(innerAttempt),
				outerAttempt.infinitenessAttempts());
	}

	@Test
	@DisplayName("propagate a serious error and retain the inner report")
	void propagateSeriousErrorAndRetainInnerReport() throws Exception {
		AnalysisContext context = context();
		DependencyPairInfinitenessAttempt innerAttempt = innerAttempt(context);
		innerAttempt.call();
		AssertionError failure = new AssertionError("serious failure");
		DependencyPairFrameworkAttempt outerAttempt = attempt(
				"error", () -> {
					throw failure;
				}, () -> List.of(innerAttempt));

		AssertionError propagated = assertThrows(
				AssertionError.class, outerAttempt::call);

		assertSame(failure, propagated);
		assertEquals(DependencyPairFrameworkAttempt.Status.ERROR,
				outerAttempt.status());
		assertEquals(List.of(innerAttempt),
				outerAttempt.infinitenessAttempts());
	}

	@Test
	@DisplayName("stop other variants when dependency graph construction is bounded")
	void stopOtherVariantsWhenDependencyGraphConstructionIsBounded()
			throws Exception {
		CountDownLatch blockingVariantStarted = new CountDownLatch(1);
		CountDownLatch blockingVariantInterrupted = new CountDownLatch(1);
		AnalysisContext context = context();
		Proof diagnosticProof = context.createProof();
		DependencyPairFrameworkAttempt blockingAttempt = attempt(
				"blocking", () -> {
					blockingVariantStarted.countDown();
					try {
						new CountDownLatch(1).await();
					}
					catch (InterruptedException e) {
						blockingVariantInterrupted.countDown();
						Thread.currentThread().interrupt();
					}
					return failedProof(context, "cancelled");
				});
		DependencyPairFrameworkAttempt limitedAttempt = attempt(
				"limited", () -> {
					blockingVariantStarted.await();
					throw new DependencyGraphLimitException(100_000);
				});

		Proof proof = new ConcurrentDependencyPairFrameworkRunner().run(
				List.of(blockingAttempt, limitedAttempt), diagnosticProof);

		assertSame(diagnosticProof, proof);
		assertTrue(proof.toString().contains(
				"Dependency graph construction exceeded 100000 approximate arcs"));
		assertEquals(DependencyPairFrameworkAttempt.Status.ERROR,
				limitedAttempt.status());
		assertEquals(DependencyPairFrameworkAttempt.Status.CANCELLED,
				blockingAttempt.status());
		assertTrue(blockingVariantInterrupted.await(2, TimeUnit.SECONDS));
	}

	@Test
	@DisplayName("wait for a cancelled variant to terminate before returning")
	void waitForCancelledVariantToTerminateBeforeReturning() throws Exception {
		CountDownLatch blockingVariantStarted = new CountDownLatch(1);
		CountDownLatch blockingVariantInterrupted = new CountDownLatch(1);
		CountDownLatch releaseBlockingVariant = new CountDownLatch(1);
		CountDownLatch blockingVariantFinished = new CountDownLatch(1);
		CountDownLatch runnerReturned = new CountDownLatch(1);
		AnalysisContext context = context();
		AtomicReference<Proof> selectedProof = new AtomicReference<>();
		DependencyPairInfinitenessAttempt retainedInnerAttempt =
				innerAttempt(context);
		retainedInnerAttempt.call();
		AtomicBoolean blockingComputationFinished = new AtomicBoolean();
		AtomicBoolean reportCollectedAfterCompletion = new AtomicBoolean();
		DependencyPairFrameworkAttempt blockingAttempt = attempt(
				"blocking", () -> {
					blockingVariantStarted.countDown();
					try {
						new CountDownLatch(1).await();
					}
					catch (InterruptedException e) {
						blockingVariantInterrupted.countDown();
						try {
							releaseBlockingVariant.await();
						}
						finally {
							blockingVariantFinished.countDown();
							Thread.currentThread().interrupt();
						}
					}
					blockingComputationFinished.set(true);
					return failedProof(context, "cancelled");
				}, () -> {
					reportCollectedAfterCompletion.set(
							blockingComputationFinished.get());
					return List.of(retainedInnerAttempt);
				});
		DependencyPairFrameworkAttempt successfulAttempt = attempt(
				"successful", () -> {
					blockingVariantStarted.await();
					return successfulProof(context);
				});
		Thread runnerThread = new Thread(() -> {
			selectedProof.set(new ConcurrentDependencyPairFrameworkRunner().run(
					List.of(blockingAttempt, successfulAttempt),
					context.createProof()));
			runnerReturned.countDown();
		});

		try {
			runnerThread.start();
			assertTrue(blockingVariantInterrupted.await(2, TimeUnit.SECONDS));
			assertFalse(runnerReturned.await(200, TimeUnit.MILLISECONDS));
		}
		finally {
			releaseBlockingVariant.countDown();
		}
		runnerThread.join(2_000);

		assertFalse(runnerThread.isAlive());
		assertTrue(blockingVariantFinished.await(2, TimeUnit.SECONDS));
		assertEquals(Proof.ProofResult.YES,
				selectedProof.get().getResult());
		assertTrue(reportCollectedAfterCompletion.get());
		assertEquals(List.of(retainedInnerAttempt),
				blockingAttempt.infinitenessAttempts());
	}

	@Test
	@DisplayName("build default variants in stable named order")
	void buildDefaultVariantsInStableNamedOrder() {
		DefaultDependencyPairFrameworkVariantFactory factory =
				new DefaultDependencyPairFrameworkVariantFactory(
						new DefaultDependencyPairProcessorConfig());
		Trs trs = new Trs("variants.trs", new LinkedList<>(), "FULL");

		assertEquals(
				List.of("Unfiltered", "Argument-filtered"),
				factory.buildAttempts(trs, context()).stream()
						.map(DependencyPairFrameworkAttempt::name)
						.toList());
	}

	@Test
	@DisplayName("return a completed proof when all variants fail")
	void returnCompletedProofWhenAllVariantsFail() {
		AnalysisContext context = context();
		Proof firstProof = failedProof(context, "first proof");
		Proof secondProof = failedProof(context, "second proof");
		DependencyPairFrameworkAttempt firstAttempt =
				attempt("first", () -> firstProof);
		DependencyPairFrameworkAttempt secondAttempt =
				attempt("second", () -> secondProof);

		Proof proof = new ConcurrentDependencyPairFrameworkRunner().run(
				List.of(firstAttempt, secondAttempt),
				context.createProof());

		assertTrue(proof == firstProof || proof == secondProof);
		assertEquals(DependencyPairFrameworkAttempt.Status.UNSUCCESSFUL,
				firstAttempt.status());
		assertEquals(DependencyPairFrameworkAttempt.Status.UNSUCCESSFUL,
				secondAttempt.status());
	}

	@Test
	@DisplayName("preserve a non-null proof when another variant returns null")
	void preserveNonNullProofWhenAnotherVariantReturnsNull() {
		AnalysisContext context = context();
		Proof failedProof = failedProof(context, "retained proof");
		DependencyPairFrameworkAttempt failedAttempt =
				attempt("failed", () -> failedProof);
		DependencyPairFrameworkAttempt nullAttempt =
				attempt("null", () -> null);

		Proof proof = new ConcurrentDependencyPairFrameworkRunner().run(
				List.of(failedAttempt, nullAttempt),
				context.createProof());

		assertSame(failedProof, proof);
		assertEquals(DependencyPairFrameworkAttempt.Status.UNSUCCESSFUL,
				failedAttempt.status());
		assertEquals(DependencyPairFrameworkAttempt.Status.UNSUCCESSFUL,
				nullAttempt.status());
	}
	@Test
	@DisplayName("report a variant exception")
	void reportVariantException() {
		AnalysisContext context = context();
		Proof diagnosticProof = context.createProof();

		DependencyPairFrameworkAttempt attempt = attempt("throwing", () -> {
			throw new IllegalStateException("variant failure");
		});
		Proof proof = new ConcurrentDependencyPairFrameworkRunner().run(
				List.of(attempt), diagnosticProof);

		assertNull(proof);
		assertEquals(DependencyPairFrameworkAttempt.Status.ERROR,
				attempt.status());
		assertTrue(diagnosticProof.toString().contains(
				"java.lang.IllegalStateException: variant failure"));
	}

	@Test
	@DisplayName("continue after a variant exception and return another success")
	void continueAfterVariantExceptionAndReturnAnotherSuccess() {
		AnalysisContext context = context();
		Proof successfulProof = successfulProof(context);
		DependencyPairFrameworkAttempt throwingAttempt =
				attempt("throwing", () -> {
					throw new IllegalStateException("variant failure");
				});
		DependencyPairFrameworkAttempt successfulAttempt =
				attempt("successful", () -> {
					Thread.sleep(100);
					return successfulProof;
				});
		Proof diagnosticProof = context.createProof();

		Proof proof = new ConcurrentDependencyPairFrameworkRunner().run(
				List.of(throwingAttempt, successfulAttempt),
				diagnosticProof);

		assertSame(successfulProof, proof);
		assertEquals(DependencyPairFrameworkAttempt.Status.ERROR,
				throwingAttempt.status());
		assertEquals(DependencyPairFrameworkAttempt.Status.SUCCESSFUL,
				successfulAttempt.status());
		assertTrue(diagnosticProof.toString().contains(
				"java.lang.IllegalStateException: variant failure"));
	}

	@Test
	@DisplayName("propagate a serious worker error through the variant runner")
	void propagateSeriousWorkerErrorThroughVariantRunner() {
		AnalysisContext context = context();
		AssertionError failure = new AssertionError("serious variant failure");
		DependencyPairFrameworkAttempt attempt =
				attempt("error", () -> {
					throw failure;
				});

		AssertionError propagated = assertThrows(
				AssertionError.class,
				() -> new ConcurrentDependencyPairFrameworkRunner().run(
						List.of(attempt), context.createProof()));

		assertSame(failure, propagated);
		assertEquals(DependencyPairFrameworkAttempt.Status.ERROR,
				attempt.status());
	}
	@Test
	@DisplayName("restore interruption while waiting for variants")
	void restoreInterruptionWhileWaitingForVariants() throws Exception {
		CountDownLatch variantStarted = new CountDownLatch(1);
		AnalysisContext context = context();
		AtomicReference<Proof> proof = new AtomicReference<>();
		AtomicBoolean interruptionRestored = new AtomicBoolean();
		Thread proofThread = new Thread(() -> {
			proof.set(new ConcurrentDependencyPairFrameworkRunner().run(List.of(
					attempt("interrupted", () -> {
						variantStarted.countDown();
						new CountDownLatch(1).await();
						return failedProof(context, "unreachable");
					})), context.createProof()));
			interruptionRestored.set(Thread.currentThread().isInterrupted());
		});

		proofThread.start();
		assertTrue(variantStarted.await(2, TimeUnit.SECONDS));
		proofThread.interrupt();
		proofThread.join(2_000);

		assertFalse(proofThread.isAlive());
		assertNull(proof.get());
		assertTrue(interruptionRestored.get());
	}

	private static DependencyPairFrameworkAttempt attempt(
			String name, Callable<Proof> computation) {
		return new DependencyPairFrameworkAttempt(name, computation);
	}

	private static DependencyPairFrameworkAttempt attempt(
			String name,
			Callable<Proof> computation,
			Supplier<List<DependencyPairInfinitenessAttempt>> innerAttempts) {

		return new DependencyPairFrameworkAttempt(
				name, computation, innerAttempts);
	}

	private static DependencyPairInfinitenessAttempt innerAttempt(
			AnalysisContext context) {

		return new DependencyPairInfinitenessAttempt(
				1, 1, "test processor",
				() -> DependencyPairProcessorResult.failed(context.createProof()));
	}

	private static Proof successfulProof(AnalysisContext context) {
		Proof proof = context.createProof();
		proof.setResult(Proof.ProofResult.YES);
		proof.setArgument("successful variant");
		return proof;
	}

	private static Proof failedProof(AnalysisContext context, String description) {
		Proof proof = context.createProof();
		proof.println(description);
		return proof;
	}

	private static AnalysisContext context() {
		return new AnalysisContext(true, null);
	}
}
