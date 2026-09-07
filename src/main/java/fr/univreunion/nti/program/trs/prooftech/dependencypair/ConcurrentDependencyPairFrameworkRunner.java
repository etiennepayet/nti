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

import java.util.List;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.dependencypair.DependencyGraphLimitException;

/** Runs dependency pair framework variants concurrently. */
final class ConcurrentDependencyPairFrameworkRunner {

	/** The maximum number of variants run concurrently. */
	private static final int MAX_CONCURRENT_VARIANTS = 2;

	/**
	 * The outcome of collecting one completed framework variant.
	 *
	 * @param latestProof the latest proof collected so far
	 * @param stop whether variant collection must stop
	 */
	private record FrameworkCollectionStep(Proof latestProof, boolean stop) {}

	/**
	 * Runs the variants and returns the first successful proof or the latest
	 * completed proof.
	 *
	 * @param attempts the framework attempts to run
	 * @param diagnosticProof the proof receiving wait failures
	 * @return the first successful proof, the latest completed proof, or
	 * {@code null} if none could be collected
	 */
	Proof run(
			List<DependencyPairFrameworkAttempt> attempts,
			Proof diagnosticProof) {

		ExecutorService executor =
				Executors.newFixedThreadPool(MAX_CONCURRENT_VARIANTS);
		CompletionService<Proof> completionService =
				new ExecutorCompletionService<>(executor);

		try {
			submitAttempts(completionService, attempts);
			executor.shutdown();
			return collectFirstSuccessfulOrLatest(
					completionService,
					attempts.size(),
					diagnosticProof);
		}
		finally {
			cancelAndAwaitAttempts(attempts, executor);
		}
	}

	/**
	 * Collects the first successful proof or the latest completed proof.
	 *
	 * @param completionService the service receiving completed variants
	 * @param submittedVariantCount the number of submitted variants
	 * @param diagnosticProof the proof receiving wait failures
	 * @return the first successful proof, the latest completed proof, or
	 * {@code null} if none could be collected
	 */
	private static Proof collectFirstSuccessfulOrLatest(
			CompletionService<Proof> completionService,
			int submittedVariantCount,
			Proof diagnosticProof) {

		Proof latestCollectedProof = null;

		for (int collectedProofCount = 0;
				collectedProofCount < submittedVariantCount;
				collectedProofCount++) {
			FrameworkCollectionStep step = collectNextFrameworkProof(
					completionService,
					latestCollectedProof,
					diagnosticProof);
			latestCollectedProof = step.latestProof();
			if (step.stop())
				return latestCollectedProof;
		}

		return latestCollectedProof;
	}

	/**
	 * Waits for and processes one completed framework proof.
	 *
	 * @param completionService the service receiving completed variants
	 * @param latestCollectedProof the latest proof collected before this step
	 * @param diagnosticProof the proof receiving wait failures
	 * @return the updated collection state
	 */
	private static FrameworkCollectionStep collectNextFrameworkProof(
			CompletionService<Proof> completionService,
			Proof latestCollectedProof,
			Proof diagnosticProof) {

		Proof collectedProof = latestCollectedProof;
		try {
			Future<Proof> future = completionService.take();
			Proof completedProof = future.get();
			if (completedProof == null)
				return new FrameworkCollectionStep(latestCollectedProof, false);

			collectedProof = completedProof;
			return new FrameworkCollectionStep(
					collectedProof, collectedProof.isSuccess());
		}
		catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			diagnosticProof.printlnIfVerbose(e.getMessage());
			return new FrameworkCollectionStep(latestCollectedProof, true);
		}
		catch (ExecutionException e) {
			Throwable cause = e.getCause();
			if (cause instanceof Error error)
				throw error;
			if (cause instanceof DependencyGraphLimitException) {
				diagnosticProof.printlnIfVerbose(cause.getMessage());
				return new FrameworkCollectionStep(diagnosticProof, true);
			}
			diagnosticProof.printlnIfVerbose(
					cause == null ? e.getMessage() : cause.toString());
		}
		catch (Exception e) {
			diagnosticProof.printlnIfVerbose(e.getMessage());
		}
		return new FrameworkCollectionStep(collectedProof, false);
	}

	/**
	 * Submits all framework attempts.
	 *
	 * @param completionService the service to submit attempts to
	 * @param attempts the framework attempts to submit
	 */
	private static void submitAttempts(
			CompletionService<Proof> completionService,
			List<DependencyPairFrameworkAttempt> attempts) {

		for (DependencyPairFrameworkAttempt attempt : attempts)
			attempt.submitTo(completionService);
	}

	/**
	 * Cancels unfinished framework attempts and waits for every worker thread to
	 * terminate.
	 *
	 * @param attempts the submitted framework attempts
	 * @param executor the executor running the attempts
	 */
	static void cancelAndAwaitAttempts(
			List<DependencyPairFrameworkAttempt> attempts,
			ExecutorService executor) {
		for (DependencyPairFrameworkAttempt attempt : attempts)
			attempt.cancel();
		executor.close();
	}
}
