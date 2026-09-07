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

import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicReference;

import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;

/**
 * One identified attempt to prove a dependency pair problem infinite.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class DependencyPairInfinitenessAttempt
		implements Callable<DependencyPairProcessorResult> {

	/** The execution state of an infiniteness attempt. */
	enum Status {
		PENDING,
		RUNNING,
		SUCCESSFUL,
		UNSUCCESSFUL,
		ERROR,
		CANCELLED
	}

	/** The one-based position of the processed problem. */
	private final int problemPosition;

	/** The one-based position of the applied processor. */
	private final int processorPosition;

	/** The processor type identifying this attempt. */
	private final String processorIdentity;

	/** The computation performed by this attempt. */
	private final Callable<DependencyPairProcessorResult> computation;

	/** The current execution state. */
	private volatile Status status = Status.PENDING;

	/** The result retained after the computation completes normally. */
	private final AtomicReference<DependencyPairProcessorResult> result =
			new AtomicReference<>();

	/** The failure retained when the computation terminates exceptionally. */
	private final AtomicReference<Throwable> failure = new AtomicReference<>();

	/** Whether cancellation has been requested for this attempt. */
	private volatile boolean cancellationRequested;

	/** The future created when this attempt is submitted. */
	private final AtomicReference<Future<DependencyPairProcessorResult>> future =
			new AtomicReference<>();

	/**
	 * Builds an identified infiniteness attempt.
	 *
	 * @param problemPosition the one-based position of the processed problem
	 * @param processorPosition the one-based position of the applied processor
	 * @param processorIdentity the processor type identifying this attempt
	 * @param computation the computation that produces the processor result
	 */
	DependencyPairInfinitenessAttempt(
			int problemPosition,
			int processorPosition,
			String processorIdentity,
			Callable<DependencyPairProcessorResult> computation) {

		this.problemPosition = problemPosition;
		this.processorPosition = processorPosition;
		this.processorIdentity = processorIdentity;
		this.computation = computation;
	}

	/**
	 * Returns the one-based position of the processed problem.
	 *
	 * @return the problem position
	 */
	int problemPosition() {
		return this.problemPosition;
	}

	/**
	 * Returns the one-based position of the applied processor.
	 *
	 * @return the processor position
	 */
	int processorPosition() {
		return this.processorPosition;
	}

	/**
	 * Returns the processor type identifying this attempt.
	 *
	 * @return the processor identity
	 */
	String processorIdentity() {
		return this.processorIdentity;
	}

	/**
	 * Returns the current execution state.
	 *
	 * @return the current execution state
	 */
	Status status() {
		return this.status;
	}

	/**
	 * Returns the retained processor result.
	 *
	 * @return the retained result, or {@code null} if none is available
	 */
	DependencyPairProcessorResult result() {
		return this.result.get();
	}

	/**
	 * Returns the failure retained after an exceptional computation.
	 *
	 * @return the retained failure, or {@code null} if none is available
	 */
	Throwable failure() {
		return this.failure.get();
	}

	/**
	 * Submits this attempt to the specified completion service.
	 *
	 * @param completionService the completion service to use
	 */
	void submitTo(
			CompletionService<DependencyPairProcessorResult> completionService) {

		this.future.set(completionService.submit(this));
	}

	/**
	 * Runs the processor computation and records its final state.
	 *
	 * @return the result produced by the processor
	 * @throws Exception if the processor computation fails
	 */
	@Override
	public DependencyPairProcessorResult call() throws Exception {
		this.status = Status.RUNNING;
		try {
			DependencyPairProcessorResult computedResult = this.computation.call();
			this.result.set(computedResult);
			this.status = this.wasCancelled()
					? Status.CANCELLED : classify(computedResult);
			return computedResult;
		}
		catch (InterruptedException e) {
			this.status = Status.CANCELLED;
			Thread.currentThread().interrupt();
			throw e;
		}
		catch (Exception e) {
			this.status = this.wasCancelled()
					? Status.CANCELLED : Status.ERROR;
			if (this.status == Status.ERROR)
				this.failure.set(e);
			throw e;
		}
		finally {
			if (this.status == Status.RUNNING)
				this.status = Status.ERROR;
		}
	}

	/** Requests cancellation of this attempt. */
	void cancel() {
		this.cancellationRequested = true;
		Future<DependencyPairProcessorResult> submitted = this.future.get();
		if (submitted != null && submitted.cancel(true)
				&& this.status == Status.PENDING)
			this.status = Status.CANCELLED;
	}

	/**
	 * Checks whether this attempt has been cancelled.
	 *
	 * @return {@code true} iff cancellation was requested or the worker was
	 * interrupted
	 */
	private boolean wasCancelled() {
		return this.cancellationRequested
				|| Thread.currentThread().isInterrupted();
	}

	/**
	 * Classifies a normally returned processor result.
	 *
	 * @param result the result to classify
	 * @return the corresponding final state
	 */
	private static Status classify(DependencyPairProcessorResult result) {
		return result != null && result.isInfinite()
				? Status.SUCCESSFUL : Status.UNSUCCESSFUL;
	}
}
