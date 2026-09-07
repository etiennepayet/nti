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

package fr.univreunion.nti.program.trs.prooftech.dependencypair.processor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;
import fr.univreunion.nti.program.trs.patternunfolding.CorrectPatternRuleTrsCollector;
import fr.univreunion.nti.program.trs.patternunfolding.patternproducer.CorrectPatternRuleTrsProducer;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;

/**
 * A complete dependency pair processor for proving that a provided DP problem
 * is infinite using the pattern-unfolding technique of E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025, adapted to term rewriting as
 * described in E. Payet,
 * <a href="https://www.imn.htwk-leipzig.de/~waldmann/WST2025/proceedings/WST2025_paper_2.pdf"><i>Non-Termination
 * of Term Rewrite Systems Using Pattern Unfolding</i></a>, Proceedings of the
 * 20th International Workshop on Termination (WST 2025), 2025.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Iclp25PatternUnfoldingDependencyPairProcessor extends DependencyPairProcessor {

	/**
	 * The maximum number of generated unfolded rules.
	 * Once this number of unfolded rules has been
	 * generated, the proof is aborted before starting
	 * another unfolding call.
	 * <p>
	 * This bound must be non-negative. Unlike the maximum
	 * depth in {@link Parameters}, a negative value does
	 * not mean unlimited.
	 */
	private static final int MAX_UNFOLDED_RULE_COUNT = 2_000;

	/**
	 * The maximum number of iterations of
	 * the unfolding operator.
	 * <p>
	 * This bound must be non-negative.
	 */
	private static final int MAX_ITERATION_COUNT = 100;

	/**
	 * The parameters for running this processor.
	 */
	private final Parameters parameters;

	/**
	 * Builds a dependency pair processor for searching
	 * for nonterminating patterns by pattern unfolding.
	 * <p>
	 * Argument filterings are not used by this
	 * processor.
	 *
	 * @param parameters the parameters for running
	 * this processor
	 */
	public Iclp25PatternUnfoldingDependencyPairProcessor(Parameters parameters) {
		super(false);

		this.parameters = parameters;
	}

	/**
	 * Returns a copy of this processor.
	 *
	 * @return a copy of this processor
	 */
	@Override
	public DependencyPairProcessor copy() {
		// We return a new processor which embeds a copy
		// of the set of parameters of this object.
		return new Iclp25PatternUnfoldingDependencyPairProcessor(this.parameters.copy());
	}

	/**
	 * Runs this processor on the provided DP problem,
	 * without using the provided argument filtering.
	 * <p>
	 * The returned result indicates whether the provided
	 * DP problem could be proved infinite.
	 *
	 * @param problem a DP problem to solve using this processor
	 * @param filtering an argument filtering for solving
	 * <code>problem</code>
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the created proof
	 * @param context the context of the analysis
	 * @return the result of this processor
	 */
	@Override
	public DependencyPairProcessorResult run(DependencyPairProblem problem,
						ArgFiltering filtering,
						int indentation,
						AnalysisContext context) {

		// The proof of the returned result.
		Proof proof = context.createProof();

		// Let us introduce ourselves.
		proof.printlnIfVerbose(this.toString(), indentation);

		// From now, we need to print 2 more single spaces
		// at the beginning of each line of the proof.
		indentation += 2;

		// The TRS of the problem to solve.
		Trs trs = problem.getTRS();
		Collection<PatternRuleTrs> correct = CorrectPatternRuleTrsCollector.collectFrom(trs);
		UnfoldingRuleBudget ruleBudget =
				new UnfoldingRuleBudget(MAX_UNFOLDED_RULE_COUNT);

		// Some data structures used for unfolding.
		List<PatternRuleTrs> rulesToUnfold = new ArrayList<>();
		List<PatternRuleTrs> unfolded = new ArrayList<>();

		// We track the number of iterations of the unfolding operator.
		int i = 0; // The current number of iterations.
		// No iteration has taken place yet, so a non-negative iteration
		// limit cannot have been exceeded.
		boolean iterationLimitExceeded = false;

		boolean unfoldedRuleLimitReached = false;

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();
		// The main loop of the processor.
		while (!currentThread.isInterrupted() &&
				!iterationLimitExceeded && !unfoldedRuleLimitReached &&
				(i == 0 || !unfolded.isEmpty())) {

			proof.printIfVerbose("# Iteration " + i + ": ", indentation);

			UnfoldingIterationResult iterationResult = performIteration(
					i, trs, rulesToUnfold, unfolded, correct, proof,
					ruleBudget);
			int generatedRuleCount = iterationResult.generatedRuleCount();
			context.incGeneratedRules(generatedRuleCount);
			unfoldedRuleLimitReached = iterationResult.limitReached();

			// We build a small message indicating the
			// number of unfolded rules generated during
			// this iteration.
			int unfSize = unfolded.size();
			String msgNbGenerated =
					unfSize + " unfolded " +
							(1 < unfSize ? "rules" : "rule") +
							" generated.";

			if (proof.isSuccess()) {
				proof.printlnIfVerbose("success, nontermination proved, " + msgNbGenerated);
				proof.printlnIfVerbose(proof.getArgument().getDetails(indentation));
				return DependencyPairProcessorResult.infinite(proof);
			}

			proof.printlnIfVerbose("nontermination not proved, " + msgNbGenerated);

			i++;

			iterationLimitExceeded = MAX_ITERATION_COUNT < i;
			if (iterationLimitExceeded)
				proof.printlnIfVerbose(
						"Too many iterations of the unfolding operator! Aborting!", indentation);
			else if (unfoldedRuleLimitReached)
				proof.printlnIfVerbose(
						"Too many unfolded rules (" +
								ruleBudget.getGeneratedRuleCount() + ")! Aborting!",
						indentation);
		}

		// Here, nontermination could not be proved.
		proof.printlnIfVerbose("Could not prove nontermination!", indentation);
		return DependencyPairProcessorResult.failed(proof);
	}

	/**
	 * Performs the specified unfolding iteration.
	 *
	 * @param iteration the current unfolding iteration number
	 * @param trs the TRS whose rules initialize iteration zero
	 * @param rulesToUnfold the work collection receiving the rules to unfold
	 * @param unfolded the collection containing the rules from the preceding
	 * iteration and receiving the newly generated rules
	 * @param correct the correct pattern rules used for unfolding
	 * @param proof the proof receiving a nontermination witness, if one is found
	 * @param ruleBudget the generated-rule budget for this processor run
	 * @return the result of the specified unfolding iteration
	 */
	private static UnfoldingIterationResult performIteration(
			int iteration,
			Trs trs,
			List<PatternRuleTrs> rulesToUnfold,
			List<PatternRuleTrs> unfolded,
			Collection<PatternRuleTrs> correct,
			Proof proof,
			UnfoldingRuleBudget ruleBudget) {

		Thread currentThread = Thread.currentThread();
		if (iteration == 0) {
			int generatedRuleCount = initializeUnfoldedRules(
					trs, unfolded, currentThread, ruleBudget);
			return new UnfoldingIterationResult(
					generatedRuleCount,
					!ruleBudget.hasRemainingCapacity());
		}

		return unfoldRules(
				rulesToUnfold, unfolded, correct, iteration, proof,
				ruleBudget, currentThread);
	}

	/**
	 * Initializes the provided collection of unfolded rules with the trivial
	 * pattern rules built from the provided TRS.
	 *
	 * @param trs the TRS whose rules have to be converted
	 * @param unfolded the collection receiving the trivial pattern rules
	 * @param currentThread the thread running the processor
	 * @param ruleBudget the generated-rule budget for this processor run
	 * @return the number of trivial pattern rules added
	 */
	private static int initializeUnfoldedRules(
			Trs trs, List<PatternRuleTrs> unfolded, Thread currentThread,
			UnfoldingRuleBudget ruleBudget) {

		for (RuleTrs rule : trs) {
			if (currentThread.isInterrupted() ||
					!ruleBudget.hasRemainingCapacity()) break;
			unfolded.add(CorrectPatternRuleTrsProducer.buildTrivialPatternRule(rule));
			ruleBudget.recordGeneratedRules(1);
		}
		return unfolded.size();
	}

	/**
	 * Unfolds the rules generated during the preceding iteration.
	 *
	 * @param rulesToUnfold the work collection receiving the rules to unfold
	 * @param unfolded the collection containing the rules from the preceding
	 * iteration and receiving the newly generated rules
	 * @param correct the correct pattern rules used for unfolding
	 * @param iteration the current unfolding iteration number
	 * @param proof the proof receiving a nontermination witness, if one is found
	 * @param ruleBudget the generated-rule budget for this processor run
	 * @param currentThread the thread running the processor
	 * @return the result of this unfolding iteration
	 */
	private static UnfoldingIterationResult unfoldRules(
			List<PatternRuleTrs> rulesToUnfold,
			List<PatternRuleTrs> unfolded,
			Collection<PatternRuleTrs> correct,
			int iteration,
			Proof proof,
			UnfoldingRuleBudget ruleBudget,
			Thread currentThread) {

		rulesToUnfold.clear();
		rulesToUnfold.addAll(unfolded);
		unfolded.clear();

		int generatedRuleCount = 0;
		Iterator<PatternRuleTrs> ruleIterator = rulesToUnfold.iterator();
		while (!currentThread.isInterrupted() &&
				!proof.isSuccess() && ruleBudget.hasRemainingCapacity() &&
				ruleIterator.hasNext()) {
			PatternRuleTrs rule = ruleIterator.next();
			Collection<PatternRuleTrs> generatedRules =
					rule.unfold(correct, iteration, proof);
			int currentGeneratedRuleCount = generatedRules.size();
			generatedRuleCount += currentGeneratedRuleCount;
			ruleBudget.recordGeneratedRules(currentGeneratedRuleCount);
			unfolded.addAll(generatedRules);
		}

		return new UnfoldingIterationResult(
				generatedRuleCount,
				!ruleBudget.hasRemainingCapacity());
	}

	/**
	 * The accounting result of an unfolding iteration.
	 *
	 * @param generatedRuleCount the number of rules generated by the iteration
	 * @param limitReached whether the local generated-rule limit was reached
	 */
	private record UnfoldingIterationResult(
			int generatedRuleCount, boolean limitReached) {}

	/**
	 * Checks whether the provided filter instantiator
	 * is suitable for this processor.
	 * <p>
	 * For internal use only.
	 * <p>
	 * Always returns <code>false</code> as this processor
	 * does not use argument filterings.
	 *
	 * @param it a filter instantiator
	 * @return always <code>false</code>
	 */
	@Override
	protected boolean isSuitable(FilterInstantiator it) {
		return false;
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		return
				"## DP Processor: [Payet, ICLP'25] (" +
				this.parameters + "). ";
	}
}
