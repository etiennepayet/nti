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

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicReference;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;

/**
 * Runs dependency pair infiniteness processors concurrently and owns their
 * task lifecycle.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class ConcurrentDependencyPairInfinitenessProver {

	/** The default maximum number of processor attempts run concurrently. */
	private static final int DEFAULT_MAXIMUM_CONCURRENCY =
			Math.max(1, Runtime.getRuntime().availableProcessors());

	/**
	 * The outcome of collecting one completed processor result.
	 *
	 * @param terminalResult the result that stops collection, or {@code null}
	 * @param failureDiagnostic whether a recoverable failure was diagnosed
	 */
	private record InfinitenessCollectionStep(
			DependencyPairProcessorResult terminalResult,
			boolean failureDiagnostic) {}

	/** The indentation used for problem-level failure messages. */
	private static final int PROBLEM_INDENTATION = 2;

	/** The indentation passed to infiniteness processors. */
	private static final int PROCESSOR_INDENTATION = 4;

	/** The processors to apply for proving infiniteness. */
	private final List<DependencyPairProcessor> processors = new ArrayList<>();

	/** The maximum number of processor attempts run concurrently. */
	private final int maximumConcurrency;

	/** The attempts built for the latest invocation of {@link #prove}. */
	private final AtomicReference<List<DependencyPairInfinitenessAttempt>>
			attempts = new AtomicReference<>(List.of());

	/**
	 * Builds a concurrent prover using the provided processors.
	 *
	 * @param processors the dependency pair processors to apply
	 */
	ConcurrentDependencyPairInfinitenessProver(
			List<DependencyPairProcessor> processors) {

		this(processors, DEFAULT_MAXIMUM_CONCURRENCY);
	}

	/**
	 * Builds a concurrent prover with the provided concurrency bound.
	 *
	 * @param processors the dependency pair processors to apply
	 * @param maximumConcurrency the maximum number of simultaneous attempts
	 * @throws IllegalArgumentException if {@code maximumConcurrency} is not
	 * positive
	 */
	ConcurrentDependencyPairInfinitenessProver(
			List<DependencyPairProcessor> processors,
			int maximumConcurrency) {

		if (maximumConcurrency <= 0)
			throw new IllegalArgumentException(
					"maximumConcurrency must be positive");
		this.processors.addAll(processors);
		this.maximumConcurrency = maximumConcurrency;
	}

	/**
	 * Tries to prove that one of the provided dependency pair problems is
	 * infinite.
	 *
	 * @param problems the dependency pair problems to process
	 * @param context the context of the analysis
	 * @return the first infinite result, or a failed result
	 */
	DependencyPairProcessorResult prove(
			DependencyPairProblemCollection problems,
			AnalysisContext context) {

		DependencyPairProcessorResult result = null;
		List<DependencyPairInfinitenessAttempt> currentAttempts =
				this.buildAttempts(problems, context);
		this.attempts.set(List.copyOf(currentAttempts));

		int submittedTaskCount = currentAttempts.size();
		if (0 < submittedTaskCount)
			result = this.runAttempts(
					currentAttempts, submittedTaskCount, context);

		return result == null ? failedResult(context) : result;
	}

	/**
	 * Returns the attempts built for the latest invocation of {@link #prove}.
	 *
	 * @return the attempts in problem-then-processor order
	 */
	List<DependencyPairInfinitenessAttempt> attempts() {
		return this.attempts.get();
	}

	/**
	 * Runs the provided attempts and always cancels unfinished work and waits
	 * for complete worker termination after result collection.
	 *
	 * @param attempts the infiniteness attempts to run
	 * @param submittedTaskCount the number of tasks to submit
	 * @param context the context of the analysis
	 * @return the collected infiniteness or failure result
	 */
	private DependencyPairProcessorResult runAttempts(
			List<DependencyPairInfinitenessAttempt> attempts,
			int submittedTaskCount,
			AnalysisContext context) {

		int workerCount = Math.min(submittedTaskCount, this.maximumConcurrency);
		ExecutorService executor = Executors.newFixedThreadPool(workerCount);
		CompletionService<DependencyPairProcessorResult> completionService =
				new ExecutorCompletionService<>(executor);

		try {
			submitAttempts(completionService, attempts);
			executor.shutdown();
			return collectFirstInfinitenessResult(
					completionService, submittedTaskCount, context);
		}
		finally {
			cancelAndAwaitAttempts(attempts, executor);
		}
	}

	/**
	 * Collects the first result proving infiniteness.
	 *
	 * @param completionService the service receiving completed tasks
	 * @param submittedTaskCount the number of submitted tasks
	 * @param context the context of the analysis
	 * @return the first infinite result, or a failed result
	 */
	private static DependencyPairProcessorResult collectFirstInfinitenessResult(
			CompletionService<DependencyPairProcessorResult> completionService,
			int submittedTaskCount,
			AnalysisContext context) {

		Proof failureProof = context.createProof();
		boolean hasFailureDiagnostic = false;

		for (int completedTaskCount = 0;
				completedTaskCount < submittedTaskCount;
				completedTaskCount++) {
			InfinitenessCollectionStep step = collectNextInfinitenessResult(
					completionService,
					failureProof);
			hasFailureDiagnostic |= step.failureDiagnostic();
			if (step.terminalResult() != null)
				return step.terminalResult();
		}

		return hasFailureDiagnostic
				? DependencyPairProcessorResult.failed(failureProof)
				: failedResult(context);
	}

	/**
	 * Waits for and processes one completed processor result.
	 *
	 * @param completionService the service receiving completed tasks
	 * @param failureProof the proof receiving wait failures
	 * @return the outcome of this collection step
	 */
	private static InfinitenessCollectionStep collectNextInfinitenessResult(
			CompletionService<DependencyPairProcessorResult> completionService,
			Proof failureProof) {

		try {
			Future<DependencyPairProcessorResult> future =
					completionService.take();

			DependencyPairProcessorResult result = future.get();
			return new InfinitenessCollectionStep(
					result != null && result.isInfinite() ? result : null,
					false);
		}
		catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			failureProof.printlnIfVerbose(e.getMessage());
			return new InfinitenessCollectionStep(
					DependencyPairProcessorResult.failed(failureProof), false);
		}
		catch (ExecutionException e) {
			Throwable cause = e.getCause();
			if (cause instanceof Error error)
				throw error;
			failureProof.printlnIfVerbose(
					cause == null ? e.getMessage() : cause.toString());
		}
		catch (Exception e) {
			failureProof.printlnIfVerbose(e.getMessage());
		}
		return new InfinitenessCollectionStep(null, true);
	}

	/**
	 * Submits all infiniteness attempts.
	 *
	 * @param completionService the service to submit tasks to
	 * @param attempts the attempts to submit
	 */
	private static void submitAttempts(
			CompletionService<DependencyPairProcessorResult> completionService,
			List<DependencyPairInfinitenessAttempt> attempts) {

		for (DependencyPairInfinitenessAttempt attempt : attempts)
			attempt.submitTo(completionService);
	}

	/**
	 * Cancels all attempts and waits for complete executor termination.
	 *
	 * @param attempts the attempts to cancel
	 * @param executor the executor whose termination to await
	 */
	private static void cancelAndAwaitAttempts(
			List<DependencyPairInfinitenessAttempt> attempts,
			ExecutorService executor) {

		for (DependencyPairInfinitenessAttempt attempt : attempts)
			attempt.cancel();
		executor.close();
	}

	/**
	 * Builds one identified attempt per problem and processor pair.
	 *
	 * @param problems the dependency pair problems to process
	 * @param context the context of the analysis
	 * @return the attempts in problem-then-processor order
	 */
	private List<DependencyPairInfinitenessAttempt> buildAttempts(
			DependencyPairProblemCollection problems,
			AnalysisContext context) {

		List<DependencyPairInfinitenessAttempt> builtAttempts = new ArrayList<>();
		int problemPosition = 0;
		for (DependencyPairProblem problem : problems) {
			problemPosition++;
			int processorPosition = 0;
			// Each task uses shallow problem and processor copies to avoid races
			// without recomputing the copied TRS dependency graph.
			for (DependencyPairProcessor processor : this.processors) {
				processorPosition++;
				builtAttempts.add(new DependencyPairInfinitenessAttempt(
						problemPosition,
						processorPosition,
						processorIdentity(processor),
						() -> processor.copy().run(
								problem.shallowCopy(), null,
								PROCESSOR_INDENTATION, context)));
			}
		}
		return builtAttempts;
	}

	/**
	 * Returns a readable type identity for the provided processor.
	 *
	 * @param processor the processor to identify
	 * @return the simple class name, or the binary name for an anonymous class
	 */
	private static String processorIdentity(
			DependencyPairProcessor processor) {

		String simpleName = processor.getClass().getSimpleName();
		return simpleName.isEmpty()
				? processor.getClass().getName() : simpleName;
	}

	/**
	 * Builds a failed result when no task was submitted.
	 *
	 * @param context the context of the analysis
	 * @return a failed result with the historical problem-level message
	 */
	private static DependencyPairProcessorResult failedResult(
			AnalysisContext context) {

		Proof proof = context.createProof();
		proof.printlnIfVerbose("Failed!", PROBLEM_INDENTATION);
		return DependencyPairProcessorResult.failed(proof);
	}

}
