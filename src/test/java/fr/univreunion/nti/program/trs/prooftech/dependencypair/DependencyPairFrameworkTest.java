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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.term.Variable;

class DependencyPairFrameworkTest {

	@Test
	@DisplayName("prove termination immediately when the dependency graph has no SCC")
	void proveTerminationImmediatelyWhenDependencyGraphHasNoScc() throws IOException {
		List<String> calls = new ArrayList<>();
		DependencyPairProcessor unusedProcessor = processor(
				"unused", calls, (problem, context) -> finite(context));
		DependencyPairFramework framework = new DependencyPairFramework(
				List.of(unusedProcessor), List.of());

		Proof proof = framework.run(nonRecursiveTrs(), context());

		assertEquals(Proof.ProofResult.YES, proof.getResult());
		assertTrue(proof.getArgument().toString().contains(
				"set of SCCs of the estimated dependency graph is empty"));
		assertTrue(calls.isEmpty());
		assertTrue(framework.infinitenessAttempts().isEmpty());
	}

	@Test
	@DisplayName("apply finiteness processors sequentially until the first success")
	void applyFinitenessProcessorsSequentiallyUntilFirstSuccess() throws IOException {
		List<String> calls = new ArrayList<>();
		DependencyPairProcessor first = processor(
				"first", calls, (problem, context) -> failed(context));
		DependencyPairProcessor second = processor(
				"second", calls, (problem, context) -> finite(context));
		DependencyPairProcessor unused = processor(
				"unused", calls, (problem, context) -> failed(context));

		Proof proof = new DependencyPairFramework(
				List.of(first, second, unused), List.of()).run(recursiveTrs(), context());

		assertEquals(Proof.ProofResult.YES, proof.getResult());
		assertEquals(List.of("first", "second"), calls);
	}

	@Test
	@DisplayName("build one argument filtering lazily for successive processors")
	void buildOneArgumentFilteringLazilyForSuccessiveProcessors() throws IOException {
		AtomicReference<ArgFiltering> firstFiltering = new AtomicReference<>();
		AtomicReference<ArgFiltering> secondFiltering = new AtomicReference<>();
		DependencyPairProcessor first = filteringProcessor(
				firstFiltering, false);
		DependencyPairProcessor second = filteringProcessor(
				secondFiltering, true);

		Proof proof = new DependencyPairFramework(
				List.of(first, second), List.of()).run(recursiveTrs(), context());

		assertEquals(Proof.ProofResult.YES, proof.getResult());
		assertNotNull(firstFiltering.get());
		assertSame(firstFiltering.get(), secondFiltering.get());
	}

	@Test
	@DisplayName("prove infiniteness after decomposed problems remain unsolved")
	void proveInfinitenessAfterDecomposedProblemsRemainUnsolved() throws IOException {
		AtomicInteger finitenessRuns = new AtomicInteger();
		DependencyPairProcessor decomposer = new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				if (finitenessRuns.getAndIncrement() == 0) {
					DependencyPairProblemCollection subproblems =
							new DependencyPairProblemCollection();
					subproblems.add(problem);
					return DependencyPairProcessorResult.decomposed(
							context.createProof(), subproblems);
				}
				return failed(context);
			}
		};
		DependencyPairProcessor infinitenessProcessor = processor(
				"infinite", new ArrayList<>(), (problem, context) -> infinite(context));
		DependencyPairFramework framework = new DependencyPairFramework(
				List.of(decomposer), List.of(infinitenessProcessor));

		Proof proof = framework.run(recursiveTrs(), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals(2, finitenessRuns.get());
		assertEquals("infinite dependency pair problem", proof.getArgument().toString());
		assertEquals(1, framework.infinitenessAttempts().size());
		assertEquals(DependencyPairInfinitenessAttempt.Status.SUCCESSFUL,
				framework.infinitenessAttempts().get(0).status());
	}

	@Test
	@DisplayName("return maybe when no processor can solve the problem")
	void returnMaybeWhenNoProcessorCanSolveProblem() throws IOException {
		Proof proof = new DependencyPairFramework(List.of(), List.of())
				.run(recursiveTrs(), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertNull(proof.getArgument());
	}

	@Test
	@DisplayName("cancel remaining concurrent tasks after an infiniteness proof")
	void cancelRemainingConcurrentTasksAfterInfinitenessProof() throws Exception {
		CountDownLatch blockingProcessorStarted = new CountDownLatch(1);
		CountDownLatch blockingProcessorInterrupted = new CountDownLatch(1);
		AtomicBoolean interrupted = new AtomicBoolean();

		DependencyPairProcessor blockingProcessor = new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				blockingProcessorStarted.countDown();
				try {
					new CountDownLatch(1).await();
				}
				catch (InterruptedException e) {
					interrupted.set(true);
					blockingProcessorInterrupted.countDown();
					Thread.currentThread().interrupt();
				}
				return failed(context);
			}
		};
		DependencyPairProcessor successfulProcessor = new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				try {
					if (!blockingProcessorStarted.await(2, TimeUnit.SECONDS))
						return failed(context);
				}
				catch (InterruptedException e) {
					Thread.currentThread().interrupt();
					return failed(context);
				}
				return infinite(context);
			}
		};

		Proof proof = new DependencyPairFramework(
				List.of(), List.of(blockingProcessor, successfulProcessor))
				.run(recursiveTrs(), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertTrue(blockingProcessorInterrupted.await(2, TimeUnit.SECONDS));
		assertTrue(interrupted.get());
	}

	@Test
	@DisplayName("return maybe when an infiniteness processor throws")
	void returnMaybeWhenInfinitenessProcessorThrows() throws IOException {
		DependencyPairProcessor throwingProcessor = new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				throw new IllegalStateException("processor failure");
			}
		};

		Proof proof = new DependencyPairFramework(
				List.of(), List.of(throwingProcessor))
				.run(recursiveTrs(), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertTrue(proof.toString().contains(
				"java.lang.IllegalStateException: processor failure"));
	}

	@Test
	@DisplayName("restore interruption after infiniteness result collection is interrupted")
	void restoreInterruptionAfterResultCollectionIsInterrupted() throws Exception {
		CountDownLatch processorStarted = new CountDownLatch(1);
		DependencyPairProcessor blockingProcessor = new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				processorStarted.countDown();
				try {
					new CountDownLatch(1).await();
				}
				catch (InterruptedException e) {
					Thread.currentThread().interrupt();
				}
				return failed(context);
			}
		};
		ConcurrentDependencyPairInfinitenessProver prover =
				new ConcurrentDependencyPairInfinitenessProver(
						List.of(blockingProcessor));
		DependencyPairProblemCollection problems =
				new InitialDependencyPairProblemCollector().collectFrom(recursiveTrs());
		AtomicReference<DependencyPairProcessorResult> result = new AtomicReference<>();
		AtomicBoolean interruptionRestored = new AtomicBoolean();
		Thread proofThread = new Thread(() -> {
			result.set(prover.prove(problems, context()));
			interruptionRestored.set(Thread.currentThread().isInterrupted());
		});

		proofThread.start();
		assertTrue(processorStarted.await(2, TimeUnit.SECONDS));
		proofThread.interrupt();
		proofThread.join(2_000);

		assertFalse(proofThread.isAlive());
		assertTrue(result.get().isFailed());
		assertTrue(interruptionRestored.get());
	}

	private static DependencyPairProcessor processor(
			String name,
			List<String> calls,
			ResultFactory resultFactory) {

		return new DependencyPairProcessor(false) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				calls.add(name);
				return resultFactory.create(problem, context);
			}

			@Override
			public String toString() {
				return name;
			}
		};
	}

	private static DependencyPairProcessor filteringProcessor(
			AtomicReference<ArgFiltering> receivedFiltering,
			boolean succeeds) {

		return new DependencyPairProcessor(true) {
			@Override
			public DependencyPairProcessorResult run(
					DependencyPairProblem problem,
					ArgFiltering filtering,
					int indentation,
					AnalysisContext context) {

				receivedFiltering.set(filtering);
				return succeeds ? finite(context) : failed(context);
			}
		};
	}

	private static DependencyPairProcessorResult finite(AnalysisContext context) {
		return DependencyPairProcessorResult.finite(context.createProof());
	}

	private static DependencyPairProcessorResult failed(AnalysisContext context) {
		return DependencyPairProcessorResult.failed(context.createProof());
	}

	private static DependencyPairProcessorResult infinite(AnalysisContext context) {
		Proof proof = context.createProof();
		proof.setArgument("infinite dependency pair problem");
		return DependencyPairProcessorResult.infinite(proof);
	}

	private static AnalysisContext context() {
		return new AnalysisContext(true, null);
	}

	private static Trs nonRecursiveTrs() throws IOException {
		return parseTrs("f(a) -> a");
	}

	private static Trs recursiveTrs() throws IOException {
		return parseTrs("f(X) -> f(X)");
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new LinkedList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return new Trs("", rules, "FULL");
	}

	@FunctionalInterface
	private interface ResultFactory {

		DependencyPairProcessorResult create(
				DependencyPairProblem problem,
				AnalysisContext context);
	}
}
