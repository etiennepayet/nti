/*
 * Copyright 2025 Etienne Payet <etienne.payet at univ-reunion.fr>
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

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.lp.binaryunfolding.LpBinaryNonTerminationProver;
import fr.univreunion.nti.program.lp.patternunfolding.LpPatternNonTerminationProver;

/**
 * Runs the default termination analysis for an LP.
 *
 * <p>The nontermination analyses use the binary unfolding semantics of
 * M. Codish and C. Taboch,
 * <a href="https://doi.org/10.1016/S0743-1066(99)00006-0"><i>A Semantic
 * Basis for the Termination Analysis of Logic Programs</i></a>, Journal of
 * Logic Programming 41(1), pp. 103--123, 1999; the loop criterion of
 * E. Payet and F. Mesnard,
 * <a href="https://doi.org/10.1145/1119479.1119481"><i>Non-Termination
 * Inference of Logic Programs</i></a>, ACM Transactions on Programming
 * Languages and Systems 28(2), pp. 256--289, 2006; the recurrent-pair
 * criterion of E. Payet,
 * <a href="https://doi.org/10.1007/s10817-023-09693-z"><i>Non-Termination
 * in Term Rewriting and Logic Programming</i></a>, Journal of Automated
 * Reasoning 68, article 4, 2024; and the pattern technique of E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LpTerminationProver {

	/**
	 * The LP to analyze.
	 */
	private final Lp lp;

	/**
	 * Builds a prover for the specified LP.
	 *
	 * @param lp the LP to analyze
	 */
	public LpTerminationProver(Lp lp) {
		this.lp = lp;
	}

	/**
	 * Runs a termination proof.
	 *
	 * @param context the context of the analysis
	 * @return the computed proof
	 */
	public Proof prove(AnalysisContext context) {
		// This method runs several threads performing
		// different analyses concurrently.

		// The proof that will be returned.
		// By default, it is a 'MAYBE' proof.
		Proof proof = context.createProof();

		String cTI = context.getPathToCti();
		ModeNonTerminationTracker modeTracker =
				new ModeNonTerminationTracker(this.lp.mode);

		List<LpProofAttempt> attempts =
				this.buildProofAttempts(cTI, context, modeTracker);
		int nbTasks = attempts.size();

		ExecutorService executor = Executors.newFixedThreadPool(nbTasks);
		CompletionService<ResultLp> ecs =
				new ExecutorCompletionService<>(executor);

		try {
			submitProofAttempts(ecs, attempts);
			executor.shutdown();
			this.waitForConclusiveResult(
					ecs, nbTasks, proof, modeTracker);
		} finally {
			cancelAndAwaitProofAttempts(attempts, executor);
		}

		appendProofAttemptSummary(proof, attempts, modeTracker);
		return proof;
	}

	/**
	 * Builds the proof attempts in their stable submission order.
	 *
	 * @param cTI the path to cTI, or <code>null</code> if cTI is disabled
	 * @param context the context of the analysis
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @return the proof attempts to run concurrently
	 */
	List<LpProofAttempt> buildProofAttempts(
			String cTI,
			AnalysisContext context,
			ModeNonTerminationTracker modeTracker) {
		List<LpProofAttempt> attempts = new ArrayList<>(cTI == null ? 2 : 3);

		if (cTI != null) {
			Proof ctiProof = context.createProof();
			attempts.add(new LpProofAttempt(
					"cTI",
					ctiProof,
					() -> this.proveTerminationWithCti(cTI, ctiProof)));
		}

		Proof binaryProof = context.createProof();
		attempts.add(new LpProofAttempt(
				"Binary unfolding",
				binaryProof,
				() -> this.proveNonTerminationWithBinaryUnfolding(
						context, modeTracker, binaryProof)));

		Proof patternProof = context.createProof();
		attempts.add(new LpProofAttempt(
				"Pattern unfolding",
				patternProof,
				() -> this.proveNonTerminationWithPatternUnfolding(
						context, modeTracker, patternProof)));

		return attempts;
	}

	/**
	 * Submits the proof attempts to run concurrently.
	 *
	 * @param ecs the completion service
	 * @param attempts the proof attempts to submit
	 */
	private static void submitProofAttempts(
			CompletionService<ResultLp> ecs,
			List<LpProofAttempt> attempts) {
		for (LpProofAttempt attempt : attempts)
			attempt.submitTo(ecs);
	}

	/**
	 * Cancels unfinished proof attempts and waits for every worker thread to
	 * terminate.
	 *
	 * @param attempts the submitted proof attempts
	 * @param executor the executor running the attempts
	 */
	static void cancelAndAwaitProofAttempts(
			List<LpProofAttempt> attempts, ExecutorService executor) {
		for (LpProofAttempt attempt : attempts)
			attempt.cancel();
		executor.close();
	}

	/**
	 * Appends a concise summary of the concurrent proof attempts in their stable
	 * submission order when verbose output is enabled.
	 *
	 * @param proof the proof receiving the summary
	 * @param attempts the completed or cancelled proof attempts
	 * @param modeTracker the tracker recording accepted witness contributions
	 */
	static void appendProofAttemptSummary(
			Proof proof,
			List<LpProofAttempt> attempts,
			ModeNonTerminationTracker modeTracker) {
		proof.printlnIfVerbose("* Concurrent LP proof attempts:");
		for (LpProofAttempt attempt : attempts) {
			boolean contributed =
					modeTracker.hasContributionFrom(attempt.proof());
			String contribution = contributionSummary(attempt, contributed);
			proof.printlnIfVerbose(
					"  - " + attempt.summary() + contribution);
		}
		proof.printlnIfVerbose();

		if (proof.isInVeryVerboseMode())
			appendDetailedProofAttempts(proof, attempts);
	}

	/**
	 * Appends the retained local work of every LP prover in stable configured
	 * order. This method is called only after all workers have terminated.
	 *
	 * @param proof the proof receiving the detailed report
	 * @param attempts the terminated proof attempts
	 */
	private static void appendDetailedProofAttempts(
			Proof proof, List<LpProofAttempt> attempts) {

		proof.println("* Detailed concurrent LP proof attempts:");
		for (LpProofAttempt attempt : attempts) {
			proof.println("  ** " + attempt.summary() + " **");
			appendRetainedTrace(proof, attempt);
		}
		proof.println();
	}

	/**
	 * Appends one retained LP attempt trace or an explicit availability marker.
	 *
	 * @param target the proof receiving the retained trace
	 * @param attempt the proof attempt whose trace is rendered
	 */
	private static void appendRetainedTrace(
			Proof target, LpProofAttempt attempt) {

		Proof localProof = attempt.proof();
		Throwable failure = attempt.failure();
		if (failure != null)
			target.println("    [cause: " + conciseFailure(failure) + "]");
		boolean incomplete = attempt.status() == LpProofAttempt.Status.CANCELLED
				|| attempt.result() == null;
		if (!localProof.hasDescription() && !localProof.isSuccess()) {
			target.println("    [trace unavailable]");
			return;
		}

		if (incomplete)
			target.println("    [partial trace retained]");
		else
			target.println("    [retained trace]");
		target.println(indent(localProof.toString(), 4));
	}

	/**
	 * Returns a one-line description of an exceptional worker failure.
	 *
	 * @param failure the exceptional worker failure
	 * @return the exception type and its optional single-line message
	 */
	private static String conciseFailure(Throwable failure) {
		String message = failure.getMessage();
		String description = failure.getClass().getSimpleName();
		if (message != null && !message.isBlank())
			description += ": " + message;
		return description.replace('\n', ' ').replace('\r', ' ');
	}

	/**
	 * Returns every line of the provided text with the specified indentation.
	 *
	 * @param text the text to indent
	 * @param indentation the number of spaces prepended to every line
	 * @return the indented text
	 */
	private static String indent(String text, int indentation) {
		String prefix = " ".repeat(Math.max(0, indentation));
		return prefix + text.replace("\n", "\n" + prefix);
	}

	/**
	 * Returns a concise description of an attempt's contribution to the shared
	 * nontermination analysis.
	 *
	 * @param attempt the proof attempt
	 * @param contributed whether the attempt supplied an accepted witness
	 * @return the contribution description, or an empty string when none is
	 * needed
	 */
	private static String contributionSummary(
			LpProofAttempt attempt, boolean contributed) {
		if (contributed)
			return "; contributed an accepted witness";

		ResultLp result = attempt.result();
		return result != null && result.isNO()
				? "; returned the shared result without contributing a witness"
				: "";
	}

	/**
	 * Waits for the first conclusive result.
	 *
	 * @param ecs the completion service
	 * @param nbTasks the number of proof tasks
	 * @param proof the proof to update
	 * @param modeTracker the tracker that owns the shared nontermination
	 * argument and its contributing proofs
	 */
	private void waitForConclusiveResult(
			CompletionService<ResultLp> ecs,
			int nbTasks,
			Proof proof,
			ModeNonTerminationTracker modeTracker) {

		for (int i = 0; i < nbTasks; i++)
			if (waitForNextResult(ecs, proof, modeTracker))
				return;
	}

	/**
	 * Waits for and processes one completed proof result.
	 *
	 * @param ecs the completion service
	 * @param proof the proof to update
	 * @param modeTracker the tracker that owns the shared nontermination
	 * argument and its contributing proofs
	 * @return {@code true} iff result collection must stop
	 */
	private static boolean waitForNextResult(
			CompletionService<ResultLp> ecs,
			Proof proof,
			ModeNonTerminationTracker modeTracker) {

		try {
			Future<ResultLp> future = ecs.take();
			return processCompletedResult(future.get(), proof, modeTracker);
		}
		catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			proof.printlnIfVerbose(e.getMessage());
			return true;
		}
		catch (ExecutionException e) {
			Throwable cause = e.getCause();
			if (cause instanceof Error error)
				throw error;
			proof.printlnIfVerbose(
					cause == null ? e.getMessage() : cause.toString());
		}
		catch (Exception e) {
			proof.printlnIfVerbose(e.getMessage());
		}
		return false;
	}

	/**
	 * Processes one completed concurrent proof result.
	 *
	 * @param result the completed result, assumed to be non-null
	 * @param proof the proof to update
	 * @param modeTracker the tracker that owns the shared nontermination
	 * argument and its contributing proofs
	 * @return {@code true} iff the result is conclusive and waiting must stop
	 */
	private static boolean processCompletedResult(
			ResultLp result,
			Proof proof,
			ModeNonTerminationTracker modeTracker) {

		if (result.isYES()) {
			proof.merge(result.getProof());
			return true;
		}
		if (result.isNO()) {
			// The shared tracker owns the complete argument and the description of
			// the proof that contributed it.
			if (!modeTracker.completeAggregatedProofIfModeProved(proof))
				proof.merge(result.getProof());
			return true;
		}
		if (result.isERROR())
			// Here, result.getProof() is supposed to be non-null.
			proof.printlnIfVerbose(result.getProof().getArgument());
		return false;
	}

	/**
	 * Runs a termination proof for this program using cTI.
	 * <p>
	 * The unique mode is specified in the input file.
	 *
	 * @param cTI the path to cTI
	 * @param proof the proof local to this attempt
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveTerminationWithCti(
			String cTI, Proof proof) {
		return new CtiTerminationProver().prove(
				cTI, this.lp.getName(), proof);
	}

	/**
	 * Runs a nontermination proof for this program
	 * using the binary unfolding operator T^{\beta}_P
	 * of Codish and Taboch (1999), cited in the class documentation.
	 * <p>
	 * This method implements the approach of
	 * Payet and Mesnard (2006) as well as the recurrent-pair approach of
	 * Payet (2024), both cited in the class documentation.
	 * <p>
	 * The unique mode is specified in the input file.
	 *
	 * @param context the context of the analysis
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @param proof the proof local to this attempt
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveNonTerminationWithBinaryUnfolding(
			AnalysisContext context,
			ModeNonTerminationTracker modeTracker,
			Proof proof) {
		return new LpBinaryNonTerminationProver(this.lp).prove(
				context, modeTracker, proof);
	}

	/**
	 * Runs a nontermination proof for this program
	 * using the pattern unfolding operator T^{\pi}_{P,B}
	 * of Payet (2025), cited in the class documentation.
	 * <p>
	 * The unique mode is specified in the input file.
	 *
	 * @param context the context of the analysis
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @param proof the proof local to this attempt
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveNonTerminationWithPatternUnfolding(
			AnalysisContext context,
			ModeNonTerminationTracker modeTracker,
			Proof proof) {
		return new LpPatternNonTerminationProver(this.lp).prove(
				context, modeTracker, proof);
	}
}
