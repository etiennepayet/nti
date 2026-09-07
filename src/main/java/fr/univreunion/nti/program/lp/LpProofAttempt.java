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

package fr.univreunion.nti.program.lp;

import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.Future;
import java.util.concurrent.atomic.AtomicReference;

import fr.univreunion.nti.program.Proof;

/**
 * A named LP proof computation and the state it has reached.
 * <p>
 * Each concurrent prover owns one instance, including its local proof and its
 * eventual result. This keeps the execution metadata available after all the
 * worker threads have terminated.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class LpProofAttempt implements Callable<ResultLp> {

	/**
	 * The execution state of a proof attempt.
	 */
	enum Status {
		PENDING,
		RUNNING,
		CONCLUSIVE,
		INCONCLUSIVE,
		ERROR,
		CANCELLED
	}

	/** The display name of the prover. */
	private final String name;

	/** The proof local to this attempt. */
	private final Proof proof;

	/** The computation performed by this attempt. */
	private final Callable<ResultLp> computation;

	/** The current execution state. */
	private volatile Status status = Status.PENDING;

	/** Whether cancellation of this attempt has been requested. */
	private volatile boolean cancellationRequested;

	/** The result retained after the computation completes. */
	private final AtomicReference<ResultLp> result = new AtomicReference<>();

	/** The failure retained when the computation terminates exceptionally. */
	private final AtomicReference<Throwable> failure = new AtomicReference<>();

	/** The future created when this attempt is submitted. */
	private final AtomicReference<Future<ResultLp>> future =
			new AtomicReference<>();

	/**
	 * Builds a named proof attempt.
	 *
	 * @param name the display name of the prover
	 * @param proof the proof local to this attempt
	 * @param computation the computation that produces the result
	 */
	LpProofAttempt(String name, Proof proof, Callable<ResultLp> computation) {
		this.name = name;
		this.proof = proof;
		this.computation = computation;
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
	 * Returns the proof local to this attempt.
	 *
	 * @return the proof local to this attempt
	 */
	Proof proof() {
		return this.proof;
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
	 * Returns the retained result, if the computation completed normally.
	 *
	 * @return the retained result, or <code>null</code> if none is available
	 */
	ResultLp result() {
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
	 * Returns the concise display summary of this attempt.
	 *
	 * @return the display name and final state of this attempt
	 */
	String summary() {
		String stateSummary = switch (this.status) {
			case PENDING -> "pending";
			case RUNNING -> "running";
			case CONCLUSIVE -> "conclusive" + this.resultSuffix();
			case INCONCLUSIVE -> "inconclusive" + this.resultSuffix();
			case ERROR -> "error";
			case CANCELLED -> "cancelled";
		};
		return this.name + ": " + stateSummary;
	}

	/**
	 * Submits this attempt to the specified completion service.
	 *
	 * @param completions the completion service to use
	 * @return the future representing this attempt
	 */
	Future<ResultLp> submitTo(CompletionService<ResultLp> completions) {
		Future<ResultLp> submitted = completions.submit(this);
		this.future.set(submitted);
		return submitted;
	}

	/**
	 * Runs the proof computation and records its final state.
	 *
	 * @return the result produced by the prover
	 * @throws Exception if the prover fails
	 */
	@Override
	public ResultLp call() throws Exception {
		this.status = Status.RUNNING;
		try {
			ResultLp computedResult = this.computation.call();
			this.result.set(computedResult);
			this.status = this.wasCancelled()
					? Status.CANCELLED : classify(computedResult);
			return computedResult;
		} catch (InterruptedException e) {
			this.status = Status.CANCELLED;
			Thread.currentThread().interrupt();
			throw e;
		} catch (Exception e) {
			this.status = this.wasCancelled()
					? Status.CANCELLED : Status.ERROR;
			if (this.status == Status.ERROR)
				this.failure.set(e);
			throw e;
		} finally {
			if (this.status == Status.RUNNING)
				this.status = Status.ERROR;
		}
	}

	/**
	 * Requests cancellation of this attempt.
	 */
	void cancel() {
		this.cancellationRequested = true;
		Future<ResultLp> submitted = this.future.get();
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
	 * Classifies a normally returned result.
	 *
	 * @param result the result to classify
	 * @return the corresponding execution state
	 */
	private static Status classify(ResultLp result) {
		if (result == null || result.isERROR())
			return Status.ERROR;
		if (result.isYES() || result.isNO())
			return Status.CONCLUSIVE;
		return Status.INCONCLUSIVE;
	}

	/**
	 * Returns the retained logical result formatted as a parenthesized suffix.
	 *
	 * @return the result suffix, or an empty string if no result is available
	 */
	private String resultSuffix() {
		ResultLp retainedResult = this.result.get();
		return retainedResult == null ? "" : " (" + retainedResult + ")";
	}
}
