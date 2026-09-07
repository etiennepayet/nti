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

package fr.univreunion.nti.program.lp.patternunfolding;

import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.lp.ModeNonTerminationTracker;
import fr.univreunion.nti.program.lp.ResultLp;
import fr.univreunion.nti.program.lp.RuleLp;

/**
 * Proves LP nontermination using the pattern unfolding operator
 * T^{\pi}_{P,B} introduced by E. Payet in
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.
 *
 * <p>
 * This prover orchestrates the pattern unfolding iterations,
 * checks generated pattern rules against the mode that still has to be proved
 * nonterminating, and builds the proof result.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class LpPatternNonTerminationProver {

	/**
	 * The rules of the logic program.
	 */
	private final Iterable<RuleLp> rules;

	/**
	 * Builds a prover for the provided logic program rules.
	 *
	 * @param rules the rules of the logic program
	 */
	public LpPatternNonTerminationProver(Iterable<RuleLp> rules) {
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

		LpPatternUnfolder unfolder = new LpPatternUnfolder(this.rules);

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();
		// The current iteration (we start at 1 because
		// iteration 0 produces nothing).
		int iteration = 1;
		for (; !currentThread.isInterrupted() && modeTracker.hasRemainingMode(); iteration++) {
			try {
				if (!runIteration(
						unfolder, iteration, context, modeTracker, proof))
					break;
			}
			catch (InterruptedException e) {
				Thread.currentThread().interrupt();
				return ResultLp.maybe(proof);
			}
		}

		// If we get here, then either the mode has been proved or the current
		// thread is interrupted. In the former case, the shared tracker contains
		// the complete nontermination argument.
		if (modeTracker.completeProofIfModeProved(proof))
			return ResultLp.no(proof);

		return ResultLp.maybe(proof);
	}

	/**
	 * Runs one iteration of the pattern-unfolding nontermination proof.
	 *
	 * @param unfolder the pattern unfolder
	 * @param iteration the current iteration number
	 * @param context the context of the analysis
	 * @param modeTracker the tracker of the mode whose nontermination remains
	 * to be proved
	 * @param proof the proof receiving verbose output
	 * @return <code>true</code> if another iteration may be useful,
	 * <code>false</code> if no more pattern rules can be generated
	 * @throws InterruptedException if the current thread is interrupted
	 */
	private static boolean runIteration(
			LpPatternUnfolder unfolder,
			int iteration,
			AnalysisContext context,
			ModeNonTerminationTracker modeTracker,
			Proof proof) throws InterruptedException {

		List<PatternRuleLp> unfolded = computeAndReportIteration(
				unfolder, iteration, context, proof);

		if (unfolded.isEmpty()) {
			// If no unfolded rule has been generated, then we can
			// safely exit because no more will be produced.
			proof.printlnIfVerbose(", aborting!");
			return false;
		}

		proof.printlnIfVerbose();

		// We use the new unfolded rules to try proving nontermination of the mode.
		modeTracker.checkWitnesses(unfolded, proof);
		return true;
	}

	/**
	 * Computes one pattern-unfolding iteration, records the number of generated
	 * rules, and reports the iteration when verbose output is enabled.
	 *
	 * @param unfolder the pattern unfolder
	 * @param iteration the current iteration number
	 * @param context the context of the analysis
	 * @param proof the proof receiving verbose output
	 * @return the pattern rules generated during the iteration
	 * @throws InterruptedException if the current thread is interrupted
	 */
	private static List<PatternRuleLp> computeAndReportIteration(
			LpPatternUnfolder unfolder,
			int iteration,
			AnalysisContext context,
			Proof proof) throws InterruptedException {

		proof.printIfVerbose(
				"* [Pattern unfolding] Iteration = " + iteration + ": ");

		List<PatternRuleLp> unfolded = unfolder.unfoldNext(iteration);
		int generatedRuleCount = unfolded.size();
		context.incGeneratedRules(generatedRuleCount);
		proof.printlnIfVerbose(
				generatedRuleCount + " new unfolded rule(s) generated");

		return unfolded;
	}
}
