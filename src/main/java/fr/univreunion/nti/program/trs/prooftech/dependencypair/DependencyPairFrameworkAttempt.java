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
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Supplier;

import fr.univreunion.nti.program.Proof;

/**
 * A named dependency-pair framework variant and the state it has reached.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class DependencyPairFrameworkAttempt implements Callable<Proof> {

	/** The execution state of a framework attempt. */
	enum Status {
		PENDING,
		RUNNING,
		SUCCESSFUL,
		UNSUCCESSFUL,
		ERROR,
		CANCELLED
	}

	/** The display name of the framework variant. */
	private final String name;

	/** The computation performed by this attempt. */
	private final Callable<Proof> computation;

	/** Supplies the inner infiniteness attempts associated with this variant. */
	private final Supplier<List<DependencyPairInfinitenessAttempt>>
			infinitenessAttemptSupplier;

	/** The current execution state. */
	private volatile Status status = Status.PENDING;

	/** Whether cancellation of this attempt has been requested. */
	private volatile boolean cancellationRequested;

	/** The proof retained after the computation completes normally. */
	private final AtomicReference<Proof> proof = new AtomicReference<>();

	/** The failure retained when the computation terminates exceptionally. */
	private final AtomicReference<Throwable> failure = new AtomicReference<>();

	/** The retained snapshot of the inner infiniteness attempts. */
	private final AtomicReference<List<DependencyPairInfinitenessAttempt>>
			infinitenessAttempts = new AtomicReference<>(List.of());

	/** The future created when this attempt is submitted. */
	private final AtomicReference<Future<Proof>> future =
			new AtomicReference<>();

	/**
	 * Builds a named framework attempt.
	 *
	 * @param name the display name of the framework variant
	 * @param computation the computation that produces the proof
	 */
	DependencyPairFrameworkAttempt(
			String name, Callable<Proof> computation) {

		this(name, computation, List::of);
	}

	/**
	 * Builds a named framework attempt that retains its inner attempts.
	 *
	 * @param name the display name of the framework variant
	 * @param computation the computation that produces the proof
	 * @param infinitenessAttemptSupplier supplies the inner infiniteness
	 * attempts associated with the framework variant
	 */
	DependencyPairFrameworkAttempt(
			String name,
			Callable<Proof> computation,
			Supplier<List<DependencyPairInfinitenessAttempt>>
					infinitenessAttemptSupplier) {

		this.name = name;
		this.computation = computation;
		this.infinitenessAttemptSupplier = infinitenessAttemptSupplier;
	}

	/**
	 * Returns the display name of this attempt.
	 *
	 * @return the display name of this attempt
	 */
	String name() {
		return this.name;
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
	 * Returns the retained proof, if the computation completed normally.
	 *
	 * @return the retained proof, or <code>null</code> if none is available
	 */
	Proof proof() {
		return this.proof.get();
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
	 * Returns the retained snapshot of the inner infiniteness attempts.
	 *
	 * @return the attempts in problem-then-processor order
	 */
	List<DependencyPairInfinitenessAttempt> infinitenessAttempts() {
		return this.infinitenessAttempts.get();
	}

	/**
	 * Submits this attempt to the specified completion service.
	 *
	 * @param completionService the completion service to use
	 */
	void submitTo(CompletionService<Proof> completionService) {
		this.future.set(completionService.submit(this));
	}

	/**
	 * Runs the framework variant and records its final state.
	 *
	 * @return the proof produced by the framework variant
	 * @throws Exception if the framework variant fails
	 */
	@Override
	public Proof call() throws Exception {
		this.status = Status.RUNNING;
		try {
			Proof computedProof = this.computation.call();
			this.proof.set(computedProof);
			this.status = this.wasCancelled()
					? Status.CANCELLED : classify(computedProof);
			return computedProof;
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
			this.captureInfinitenessAttempts();
		}
	}

	/** Requests cancellation of this attempt. */
	void cancel() {
		this.cancellationRequested = true;
		Future<Proof> submitted = this.future.get();
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
	 * Classifies a normally returned proof.
	 *
	 * @param proof the proof to classify
	 * @return the corresponding final state
	 */
	private static Status classify(Proof proof) {
		return proof != null && proof.isSuccess()
				? Status.SUCCESSFUL : Status.UNSUCCESSFUL;
	}

	/** Retains an immutable snapshot of the associated inner attempts. */
	private void captureInfinitenessAttempts() {
		try {
			this.infinitenessAttempts.set(List.copyOf(
					this.infinitenessAttemptSupplier.get()));
		}
		catch (RuntimeException ignored) {
			// Diagnostic collection must not alter proof selection or execution.
		}
	}
}
