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

package fr.univreunion.nti.program.lp.binaryunfolding;

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.lp.ModeNonTerminationTracker;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.program.lp.ResultLp;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.UnfoldedRuleLp;

/**
 * Proves LP nontermination using the binary unfolding operator
 * T^{\beta}_P introduced by M. Codish and C. Taboch,
 * <a href="https://doi.org/10.1016/S0743-1066(99)00006-0"><i>A Semantic
 * Basis for the Termination Analysis of Logic Programs</i></a>, Journal of
 * Logic Programming 41(1), pp. 103--123, 1999.
 *
 * <p>Loop inference follows E. Payet and F. Mesnard,
 * <a href="https://doi.org/10.1145/1119479.1119481"><i>Non-Termination
 * Inference of Logic Programs</i></a>, ACM Transactions on Programming
 * Languages and Systems 28(2), pp. 256--289, 2006. Recurrent-pair inference
 * follows E. Payet,
 * <a href="https://doi.org/10.1007/s10817-023-09693-z"><i>Non-Termination
 * in Term Rewriting and Logic Programming</i></a>, Journal of Automated
 * Reasoning 68, article 4, 2024, and
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10"><i>Recurrent Pairs
 * Revisited</i></a>, LOPSTR 2025, LNCS 16117, pp. 154--164, 2026.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class LpBinaryNonTerminationProver {

	/**
	 * The rules of the logic program.
	 */
	private final Iterable<RuleLp> rules;

	/**
	 * Builds a prover for the provided logic program rules.
	 *
	 * @param rules the rules of the logic program
	 */
	public LpBinaryNonTerminationProver(Iterable<RuleLp> rules) {
		this.rules = rules;
	}

	/**
	 * Runs the nontermination proof.
	 * <p>
	 * The unique mode is specified in the input file.
	 *
	 * @param context the context of the analysis
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @return the <code>Result</code> of this prover
	 */
	public ResultLp prove(
			AnalysisContext context, ModeNonTerminationTracker modeTracker) {
		return this.prove(context, modeTracker, context.createProof());
	}

	/**
	 * Runs the nontermination proof and writes its trace to the provided proof.
	 *
	 * @param context the context of the analysis
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @param proof the proof local to this attempt
	 * @return the <code>Result</code> of this prover
	 */
	public ResultLp prove(
			AnalysisContext context,
			ModeNonTerminationTracker modeTracker,
			Proof proof) {

		LpBinaryProofState proofState = new LpBinaryProofState(
				context, proof, new LpBinaryUnfolder(this.rules), new ArrayList<>());

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();
		// The current iteration (we start at 1 because
		// iteration 0 produces nothing).
		int iteration = 1;
		for (; !currentThread.isInterrupted() && modeTracker.hasRemainingMode(); iteration++) {
			LpBinaryProofIterationResult iterationResult;
			try {
				iterationResult = runIteration(
						iteration, proofState, modeTracker);
			}
			catch (InterruptedException e) {
				Thread.currentThread().interrupt();
				return ResultLp.maybe(proof);
			}

			if (iterationResult.completedProof())
				return iterationResult.result();
		}

		// If we get here, then either the mode has been proved or the current
		// thread is interrupted. In the former case, the shared tracker contains
		// the complete nontermination argument.
		if (modeTracker.completeProofIfModeProved(proof))
			return ResultLp.no(proof);

		return ResultLp.maybe(proof);
	}

	/**
	 * Runs one iteration of the binary-unfolding nontermination proof.
	 *
	 * @param iteration the current binary-unfolding iteration
	 * @param proofState the current proof state
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @return the result of this iteration
	 * @throws InterruptedException if the current thread is interrupted
	 */
	private static LpBinaryProofIterationResult runIteration(
			int iteration,
			LpBinaryProofState proofState,
			ModeNonTerminationTracker modeTracker) throws InterruptedException {
		Proof proof = proofState.proof();
		proof.printIfVerbose("* [Binary unfolding] Iteration = " + iteration + ": ");

		List<UnfoldedRuleLp> unfolded =
				computeUnfoldingIteration(proofState, iteration);

		if (unfolded.isEmpty()) {
			return LpBinaryProofIterationResult.completedWith(
					buildTerminationResultFromNoGeneratedRules(
							proof, iteration));
		}

		generateWitnessesAndCheckModes(
				unfolded, proofState.loopDictionary(), modeTracker, proof);
		return LpBinaryProofIterationResult.continueProof();
	}

	/**
	 * Computes the current iteration of the binary unfolding operator.
	 *
	 * @param proofState the current proof state
	 * @param iteration the current binary-unfolding iteration
	 * @return the unfolded rules generated during this iteration
	 * @throws InterruptedException if the current thread is interrupted
	 */
	private static List<UnfoldedRuleLp> computeUnfoldingIteration(
			LpBinaryProofState proofState,
			int iteration) throws InterruptedException {
		Proof proof = proofState.proof();
		List<UnfoldedRuleLp> unfolded =
				proofState.unfolder().unfoldNext(iteration);

		int generatedRuleCount = unfolded.size();
		proofState.context().incGeneratedRules(generatedRuleCount);
		proof.printIfVerbose(generatedRuleCount + " new unfolded rule(s) generated, ");

		return unfolded;
	}

	/**
	 * Generates nontermination witnesses from the new unfolded rules and
	 * checks the mode against them.
	 *
	 * @param unfolded the newly generated unfolded rules
	 * @param loopDictionary the loop dictionary to update
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @param proof the current proof
	 */
	private static void generateWitnessesAndCheckModes(
			List<UnfoldedRuleLp> unfolded,
			List<NonTerminationWitness> loopDictionary,
			ModeNonTerminationTracker modeTracker,
			Proof proof) {
		// We generate nontermination witnesses
		// from the new unfolded rules.
		LpBinaryWitnessGeneration generation =
				LpBinaryWitnessGenerator.generateFrom(
						unfolded, loopDictionary);
		List<NonTerminationWitness> newWitnesses =
				generation.newWitnesses();

		proof.printlnIfVerbose(newWitnesses.size() + " new witness(es) generated\n");

		// Then, we use the new witnesses to try proving nontermination of the
		// mode.
		modeTracker.checkWitnesses(newWitnesses, proof);
	}

	/**
	 * Builds the termination result obtained when binary unfolding produces
	 * no new rule.
	 *
	 * @param proof the proof to complete
	 * @param iteration the current binary-unfolding iteration
	 * @return the termination result
	 */
	private static ResultLp buildTerminationResultFromNoGeneratedRules(
			Proof proof,
			int iteration) {
		// If no binary rule has been generated, then we can
		// safely exit because no more will be produced.
		proof.printIfVerbose("aborting!\n");

		// Moreover, here we can safely conclude that the
		// program is always terminating.
		proof.setResult(Proof.ProofResult.YES);
		String terminationArgument =
				"From iteration " + iteration + " of the binary unfolding operator,\n" +
				"no new unfolded rule is generated.\n" +
				"Hence, the program always terminates.\n" +
				"So, the specified mode is terminating.";
		proof.setArgument(terminationArgument);
		return ResultLp.yes(proof);
	}

}
