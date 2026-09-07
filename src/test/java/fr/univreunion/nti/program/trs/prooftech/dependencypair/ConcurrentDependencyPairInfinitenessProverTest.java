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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.term.Variable;

class ConcurrentDependencyPairInfinitenessProverTest {

	@Test
	@DisplayName("run one copied processor on a shallow copy of every problem")
	void runCopiedProcessorsOnShallowCopiesOfEveryProblem() throws IOException {
		DependencyPairProblemCollection problems = twoDistinctProblems();
		List<DependencyPairProblem> originals = streamProblems(problems);
		Set<String> invocations = ConcurrentHashMap.newKeySet();
		AtomicBoolean receivedOriginalProblem = new AtomicBoolean();
		AtomicInteger firstCopyCount = new AtomicInteger();
		AtomicInteger secondCopyCount = new AtomicInteger();
		AnalysisContext context = new AnalysisContext(true, null);

		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(List.of(
						recordingProcessor(
								"first", firstCopyCount, invocations,
								originals, receivedOriginalProblem),
						recordingProcessor(
								"second", secondCopyCount, invocations,
								originals, receivedOriginalProblem)));

		DependencyPairProcessorResult result = prover.prove(problems, context);

		assertTrue(result.isFailed());
		assertEquals(2, firstCopyCount.get());
		assertEquals(2, secondCopyCount.get());
		assertEquals(Set.of("first:1", "second:1", "first:2", "second:2"),
				invocations);
		assertFalse(receivedOriginalProblem.get());
		assertEquals(List.of(1, 1, 2, 2), prover.attempts().stream()
				.map(DependencyPairInfinitenessAttempt::problemPosition)
				.toList());
		assertEquals(List.of(1, 2, 1, 2), prover.attempts().stream()
				.map(DependencyPairInfinitenessAttempt::processorPosition)
				.toList());
		assertTrue(prover.attempts().stream().allMatch(attempt ->
				!attempt.processorIdentity().isBlank()));
		assertTrue(prover.attempts().stream().allMatch(attempt ->
				attempt.status()
						== DependencyPairInfinitenessAttempt.Status.UNSUCCESSFUL));
		assertTrue(prover.attempts().stream().allMatch(attempt ->
				attempt.result() != null && attempt.result().isFailed()));
	}

	@Test
	@DisplayName("return the first infinite result and retain every attempt")
	void returnFirstInfiniteResultAndRetainEveryAttempt() throws Exception {
		DependencyPairProblemCollection problems = oneProblem();
		CountDownLatch blockingProcessorStarted = new CountDownLatch(1);
		CountDownLatch blockingProcessorInterrupted = new CountDownLatch(1);
		CountDownLatch releaseBlockingProcessor = new CountDownLatch(1);
		CountDownLatch blockingProcessorFinished = new CountDownLatch(1);
		CountDownLatch proverReturned = new CountDownLatch(1);
		AnalysisContext context = new AnalysisContext(true, null);
		DependencyPairProcessorResult blockedResult =
				DependencyPairProcessorResult.failed(context.createProof());
		DependencyPairProcessorResult infiniteResult =
				DependencyPairProcessorResult.infinite(context.createProof());
		DependencyPairProcessor blockingProcessor = processor(
				(problem, analysisContext) -> {
					blockingProcessorStarted.countDown();
					try {
						new CountDownLatch(1).await();
					}
					catch (InterruptedException e) {
						blockingProcessorInterrupted.countDown();
						try {
							releaseBlockingProcessor.await();
						}
						catch (InterruptedException repeatedInterruption) {
							Thread.currentThread().interrupt();
						}
						finally {
							blockingProcessorFinished.countDown();
							Thread.currentThread().interrupt();
						}
					}
					return blockedResult;
				});
		DependencyPairProcessor successfulProcessor = processor(
				(problem, analysisContext) -> {
					await(blockingProcessorStarted);
					return infiniteResult;
				});
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(List.of(
						blockingProcessor, successfulProcessor));
		AtomicReference<DependencyPairProcessorResult> selectedResult =
				new AtomicReference<>();
		Thread proverThread = new Thread(() -> {
			selectedResult.set(prover.prove(problems, context));
			proverReturned.countDown();
		});

		try {
			proverThread.start();
			assertTrue(blockingProcessorInterrupted.await(2, TimeUnit.SECONDS));
			assertFalse(proverReturned.await(200, TimeUnit.MILLISECONDS));
		}
		finally {
			releaseBlockingProcessor.countDown();
		}
		proverThread.join(2_000);

		assertFalse(proverThread.isAlive());
		assertTrue(blockingProcessorFinished.await(2, TimeUnit.SECONDS));
		assertSame(infiniteResult, selectedResult.get());
		assertEquals(DependencyPairInfinitenessAttempt.Status.CANCELLED,
				prover.attempts().get(0).status());
		assertEquals(DependencyPairInfinitenessAttempt.Status.SUCCESSFUL,
				prover.attempts().get(1).status());
		assertSame(blockedResult, prover.attempts().get(0).result());
		assertSame(infiniteResult, prover.attempts().get(1).result());
	}

	@Test
	@DisplayName("retain an error and preserve the historical failed result")
	void retainErrorAndPreserveHistoricalFailedResult() throws IOException {
		AnalysisContext context = new AnalysisContext(true, null);
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(List.of(
						processor((problem, analysisContext) -> {
							throw new IllegalStateException("processor failure");
						})));

		DependencyPairProcessorResult result = prover.prove(oneProblem(), context);

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains("processor failure"));
		assertEquals(DependencyPairInfinitenessAttempt.Status.ERROR,
				prover.attempts().get(0).status());
	}

	@Test
	@DisplayName("continue after a processor exception and return another success")
	void continueAfterProcessorExceptionAndReturnAnotherSuccess()
			throws IOException {
		AnalysisContext context = new AnalysisContext(true, null);
		DependencyPairProcessorResult infiniteResult =
				DependencyPairProcessorResult.infinite(context.createProof());
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(List.of(
						processor((problem, analysisContext) -> {
							throw new IllegalStateException("processor failure");
						}),
						processor((problem, analysisContext) -> {
							sleep(100);
							return infiniteResult;
						})));

		DependencyPairProcessorResult result = prover.prove(
				oneProblem(), context);

		assertSame(infiniteResult, result);
		assertEquals(DependencyPairInfinitenessAttempt.Status.ERROR,
				prover.attempts().get(0).status());
		assertEquals(DependencyPairInfinitenessAttempt.Status.SUCCESSFUL,
				prover.attempts().get(1).status());
	}

	@Test
	@DisplayName("propagate a serious worker error through the processor runner")
	void propagateSeriousWorkerErrorThroughProcessorRunner()
			throws IOException {
		AnalysisContext context = new AnalysisContext(true, null);
		AssertionError failure = new AssertionError("serious processor failure");
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(List.of(
						processor((problem, analysisContext) -> {
							throw failure;
						})));

		AssertionError propagated = assertThrows(
				AssertionError.class,
				() -> prover.prove(oneProblem(), context));

		assertSame(failure, propagated);
		assertEquals(DependencyPairInfinitenessAttempt.Status.ERROR,
				prover.attempts().get(0).status());
	}

	@Test
	@DisplayName("continue after a failed processor and return a later success")
	void continueAfterFailedProcessorAndReturnLaterSuccess() throws IOException {
		AnalysisContext context = new AnalysisContext(true, null);
		DependencyPairProcessorResult earlyResult =
				DependencyPairProcessorResult.failed(context.createProof());
		DependencyPairProcessorResult lateResult =
				DependencyPairProcessorResult.infinite(context.createProof());
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(List.of(
						processor((problem, analysisContext) -> {
							sleep(20);
							return earlyResult;
						}),
						processor((problem, analysisContext) -> {
							sleep(100);
							return lateResult;
						})));

		DependencyPairProcessorResult result = prover.prove(
				oneProblem(), context);

		assertSame(lateResult, result);
		assertEquals(DependencyPairInfinitenessAttempt.Status.UNSUCCESSFUL,
				prover.attempts().get(0).status());
		assertEquals(DependencyPairInfinitenessAttempt.Status.SUCCESSFUL,
				prover.attempts().get(1).status());
	}

	@Test
	@DisplayName("limit the number of concurrently running processor attempts")
	void limitConcurrentProcessorAttempts() throws Exception {
		int maximumConcurrency = 2;
		int attemptCount = 4;
		CountDownLatch firstAttemptsStarted =
				new CountDownLatch(maximumConcurrency);
		CountDownLatch releaseAttempts = new CountDownLatch(1);
		AtomicInteger runningAttemptCount = new AtomicInteger();
		AtomicInteger largestRunningAttemptCount = new AtomicInteger();
		AnalysisContext context = new AnalysisContext(true, null);
		List<DependencyPairProcessor> processors = new LinkedList<>();
		for (int index = 0; index < attemptCount; index++) {
			processors.add(processor((problem, analysisContext) -> {
				int running = runningAttemptCount.incrementAndGet();
				largestRunningAttemptCount.accumulateAndGet(running, Math::max);
				firstAttemptsStarted.countDown();
				try {
					releaseAttempts.await();
				}
				catch (InterruptedException e) {
					Thread.currentThread().interrupt();
				}
				finally {
					runningAttemptCount.decrementAndGet();
				}
				return DependencyPairProcessorResult.failed(
						analysisContext.createProof());
			}));
		}
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(
						processors, maximumConcurrency);
		AtomicReference<DependencyPairProcessorResult> result =
				new AtomicReference<>();
		Thread proofThread = new Thread(
				() -> result.set(prover.prove(uncheckedOneProblem(), context)));

		try {
			proofThread.start();
			assertTrue(firstAttemptsStarted.await(2, TimeUnit.SECONDS));
			assertEquals(maximumConcurrency,
					largestRunningAttemptCount.get());
		}
		finally {
			releaseAttempts.countDown();
		}
		proofThread.join(2_000);

		assertFalse(proofThread.isAlive());
		assertNotNull(result.get());
		assertTrue(result.get().isFailed());
		assertEquals(attemptCount, prover.attempts().size());
	}

	@Test
	@DisplayName("propagate a serious error and record its state")
	void propagateSeriousErrorAndRecordItsState() {
		AssertionError failure = new AssertionError("serious failure");
		DependencyPairInfinitenessAttempt attempt =
				new DependencyPairInfinitenessAttempt(
						1, 1, "test processor", () -> {
							throw failure;
						});

		AssertionError propagated = assertThrows(
				AssertionError.class, attempt::call);

		assertSame(failure, propagated);
		assertEquals(DependencyPairInfinitenessAttempt.Status.ERROR,
				attempt.status());
		assertNull(attempt.result());
	}

	@Test
	@DisplayName("restore interruption and terminate the interrupted processor")
	void restoreInterruptionAndTerminateInterruptedProcessor() throws Exception {
		CountDownLatch processorStarted = new CountDownLatch(1);
		CountDownLatch processorInterrupted = new CountDownLatch(1);
		AnalysisContext context = new AnalysisContext(true, null);
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(List.of(
						processor((problem, analysisContext) -> {
							processorStarted.countDown();
							try {
								new CountDownLatch(1).await();
							}
							catch (InterruptedException e) {
								processorInterrupted.countDown();
								Thread.currentThread().interrupt();
							}
							return DependencyPairProcessorResult.failed(
									analysisContext.createProof());
						})));
		AtomicBoolean interruptionRestored = new AtomicBoolean();
		Thread proofThread = new Thread(() -> {
			prover.prove(uncheckedOneProblem(), context);
			interruptionRestored.set(Thread.currentThread().isInterrupted());
		});

		proofThread.start();
		assertTrue(processorStarted.await(2, TimeUnit.SECONDS));
		proofThread.interrupt();
		proofThread.join(2_000);

		assertFalse(proofThread.isAlive());
		assertTrue(processorInterrupted.await(2, TimeUnit.SECONDS));
		assertTrue(interruptionRestored.get());
		assertEquals(DependencyPairInfinitenessAttempt.Status.CANCELLED,
				prover.attempts().get(0).status());
	}

	private static DependencyPairProcessor recordingProcessor(
			String name,
			AtomicInteger copyCount,
			Set<String> invocations,
			List<DependencyPairProblem> originals,
			AtomicBoolean receivedOriginalProblem) {

		return new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessor copy() {
				copyCount.incrementAndGet();
				return new DependencyPairProcessor(false) {
					@Override
					public DependencyPairProcessorResult run(
							DependencyPairProblem problem,
							ArgFiltering filtering,
							int indentation,
							AnalysisContext context) {

						if (containsByIdentity(originals, problem))
							receivedOriginalProblem.set(true);
						invocations.add(name + ":" + problem.nbDependencyPairs());
						return DependencyPairProcessorResult.failed(
								context.createProof());
					}
				};
			}

			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				throw new AssertionError("the original processor must not run");
			}
		};
	}

	private static boolean containsByIdentity(
			List<DependencyPairProblem> problems,
			DependencyPairProblem candidate) {

		for (DependencyPairProblem problem : problems)
			if (problem == candidate)
				return true;
		return false;
	}

	private static DependencyPairProblemCollection twoDistinctProblems()
			throws IOException {

		Trs trs = recursiveTrs();
		DependencyPairProblem first =
				new InitialDependencyPairProblemCollector()
						.collectFrom(trs).iterator().next();
		RuleTrs dependencyPair = first.getDependencyPairs().iterator().next();
		DependencyPairProblem second = new DependencyPairProblem(
				trs, new DependencyPairs(List.of(dependencyPair, dependencyPair)));
		DependencyPairProblemCollection problems =
				new DependencyPairProblemCollection();
		problems.add(first);
		problems.add(second);
		return problems;
	}

	private static DependencyPairProblemCollection oneProblem()
			throws IOException {

		return new InitialDependencyPairProblemCollector().collectFrom(
				recursiveTrs());
	}

	private static DependencyPairProblemCollection uncheckedOneProblem() {
		try {
			return oneProblem();
		}
		catch (IOException e) {
			throw new AssertionError(e);
		}
	}

	private static DependencyPairProcessor processor(
			ProcessorComputation computation) {

		return new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				return computation.run(problem, context);
			}
		};
	}

	private static void await(CountDownLatch latch) {
		try {
			latch.await();
		}
		catch (InterruptedException e) {
			Thread.currentThread().interrupt();
		}
	}

	private static void sleep(long milliseconds) {
		try {
			Thread.sleep(milliseconds);
		}
		catch (InterruptedException e) {
			Thread.currentThread().interrupt();
		}
	}

	@FunctionalInterface
	private interface ProcessorComputation {
		DependencyPairProcessorResult run(
				DependencyPairProblem problem,
				AnalysisContext context);
	}

	private static List<DependencyPairProblem> streamProblems(
			DependencyPairProblemCollection problems) {

		List<DependencyPairProblem> result = new LinkedList<>();
		for (DependencyPairProblem problem : problems)
			result.add(problem);
		return result;
	}

	private static Trs recursiveTrs() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		RuleTrs rule = parser.parseTrsRule("f(X) -> f(X)", variables);
		return new Trs("", new LinkedList<>(List.of(rule)), "FULL");
	}
}
