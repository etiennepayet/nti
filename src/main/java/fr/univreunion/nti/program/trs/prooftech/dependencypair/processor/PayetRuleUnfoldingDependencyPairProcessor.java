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
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.program.trs.ruleunfolding.TrsSyntacticLoopCollector;
import fr.univreunion.nti.program.trs.ruleunfolding.comp.UnfoldedRuleTrsComp;

/**
 * A complete dependency pair processor for proving that
 * a provided DP problem is infinite using the rule
 * unfolding techniques of Payet (search for loops and
 * recurrent pairs).
 * <p>
 * It consists in searching for a nontermination witness
 * by unfolding the dependency pairs with the TRS of the
 * provided problem.
 *
 * <p>The loop search is based on E. Payet,
 * <a href="https://doi.org/10.1016/j.tcs.2008.05.013"><i>Loop Detection in
 * Term Rewriting Using the Eliminating Unfoldings</i></a>, Theoretical
 * Computer Science 403(2--3), pp. 307--327, 2008, and
 * <a href="https://doi.org/10.1007/978-3-030-13838-7_2"><i>Guided
 * Unfoldings for Finding Loops in Standard Term Rewriting</i></a>, LOPSTR
 * 2018, LNCS 11408, pp. 22--37, 2019.</p>
 *
 * <p>The recurrent-pair search follows E. Payet,
 * <a href="https://doi.org/10.1007/s10817-023-09693-z"><i>Non-Termination
 * in Term Rewriting and Logic Programming</i></a>, Journal of Automated
 * Reasoning 68, article 4, 2024, and
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10"><i>Recurrent Pairs
 * Revisited</i></a>, LOPSTR 2025, LNCS 16117, pp. 154--164, 2026.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PayetRuleUnfoldingDependencyPairProcessor extends DependencyPairProcessor {

	/**
	 * The maximum number of generated unfolded rules.
	 * Once this number of unfolded rules has been
	 * generated, the proof is aborted before starting
	 * another unfolding call.
	 * <p>
	 * This bound must be non-negative.
	 */
	private static final int MAX_UNFOLDED_RULE_COUNT = 10_000;

	/**
	 * The maximum number of generated rules for an exhaustive
	 * unbounded-depth search. This retains the historical
	 * iteration-six proof of {@code test77.ari}, which needs
	 * 13,743 rules across its successive depth attempts.
	 */
	private static final int MAX_EXHAUSTIVE_UNFOLDED_RULE_COUNT = 14_000;

	/**
	 * The maximum number of iterations of
	 * the unfolding operator.
	 * <p>
	 * This bound must be non-negative.
	 */
	private static final int MAX_ITERATION_COUNT = Integer.MAX_VALUE / 2;


	/**
	 * The parameters for running this processor.
	 */
	private final Parameters parameters;

	/**
	 * Builds a dependency pair processor for searching
	 * for loops and recurrent pairs by rule unfolding.
	 * <p>
	 * Argument filterings are not used by this
	 * processor.
	 *
	 * @param parameters the parameters for running
	 * this processor
	 */
	public PayetRuleUnfoldingDependencyPairProcessor(Parameters parameters) {
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
		return new PayetRuleUnfoldingDependencyPairProcessor(this.parameters.copy());
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

		this.parameters.setVerboseMode(context.isInVerboseMode());

		// The TRS of the problem to solve.
		Trs trs = problem.getTRS();
		UnfoldingRuleBudget ruleBudget =
				new UnfoldingRuleBudget(getUnfoldedRuleCountLimit());

		// The maximum depth of a generated unfolded rule.
		Integer generatedMaxDepth;

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();

		int originallyFixedMaxDepth = this.parameters.getMaxDepth();
		if (originallyFixedMaxDepth < 0) {
			// If the max depth for the unfolded rules is specified
			// as unlimited, then we incrementally increase the max
			// depth, starting from the depth of the TRS.
			int m = trs.depth() - 1;
			do {
				m++;
				this.parameters.setMaxDepth(m);
				generatedMaxDepth = this.runWithFixedDepth(
						problem, proof, indentation + 2, context, ruleBudget);
			}
			while (!currentThread.isInterrupted() &&
					ruleBudget.hasRemainingCapacity() &&
					generatedMaxDepth != null && generatedMaxDepth == m);
			// At the end of the analysis, we reset the max depth
			// to its original value.
			this.parameters.setMaxDepth(originallyFixedMaxDepth);
		}
		else
			// Otherwise, we run the analysis with the specified
			// max depth only.
			generatedMaxDepth = this.runWithFixedDepth(
					problem, proof, indentation + 2, context, ruleBudget);

		return (generatedMaxDepth == null ?
				DependencyPairProcessorResult.infinite(proof) :
					DependencyPairProcessorResult.failed(proof));
	}

	/**
	 * Returns the generated-rule bound for the selected search strategy.
	 *
	 * @return the generated-rule bound
	 */
	private int getUnfoldedRuleCountLimit() {
		return this.parameters.getMaxDepth() < 0 &&
				this.parameters.getStrategy() == StrategyLoop.ALL ?
				MAX_EXHAUSTIVE_UNFOLDED_RULE_COUNT :
				MAX_UNFOLDED_RULE_COUNT;
	}

	/**
	 * Runs this processor on the provided DP problem
	 * using a fixed maximum depth embedded in the
	 * parameters.
	 * <p>
	 * If variable unfolding is disabled and nontermination
	 * has not been detected, then also tries with variable
	 * unfolding enabled.
	 * <p>
	 * Returns either <code>null</code> (meaning that this
	 * processor succeeded in proving that the provided
	 * problem is infinite) or the maximum depth of an
	 * unfolded rule generated by this processor (meaning
	 * that this processor did not succeed in proving
	 * infiniteness).
	 *
	 * @param problem a DP problem to solve using this processor
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @param context the context of the analysis
	 * @param ruleBudget the rule budget shared by all depth attempts
	 * @return <code>null</code> or the maximum depth of an
	 * unfolded rule generated by this processor
	 */
	private Integer runWithFixedDepth(DependencyPairProblem problem,
			Proof proof, int indentation, AnalysisContext context,
			UnfoldingRuleBudget ruleBudget) {

		// We try to prove nontermination by unfolding the
		// dependency pairs of the specified problem.
		Integer generatedMaxDepth =
				this.runWithFixedDepthAndVar(
						problem, proof, indentation, context, ruleBudget);

		// If nontermination was not detected and variable
		// unfolding was OFF, then we try with variable
		// unfolding on.
		if (!Thread.currentThread().isInterrupted() &&
				ruleBudget.hasRemainingCapacity() &&
				generatedMaxDepth != null &&
				!this.parameters.isVariableUnfoldingEnabled()) {

			this.parameters.setVariableUnfolding(true);
			generatedMaxDepth = this.runWithFixedDepthAndVar(
					problem, proof, indentation, context, ruleBudget);
			// At the end of the analysis, we reset the 'variable unfolding'
			// flag to its initial value.
			this.parameters.setVariableUnfolding(false);
		}

		return generatedMaxDepth;
	}

	/**
	 * Runs this processor on the provided DP problem using
	 * a fixed maximum depth and a fixed variable unfolding
	 * behavior, both embedded in the parameters.
	 * <p>
	 * Returns either <code>null</code> (meaning that this
	 * processor succeeded in proving that the provided
	 * problem is infinite) or the maximum depth of an
	 * unfolded rule generated by this processor (meaning
	 * that this processor did not succeed in proving
	 * infiniteness).
	 *
	 * @param problem a DP problem to solve using this processor
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @param context the context of the analysis
	 * @param ruleBudget the rule budget shared by all depth attempts
	 * @return <code>null</code> or the maximum depth of an
	 * unfolded rule generated by this processor
	 */
	private Integer runWithFixedDepthAndVar(DependencyPairProblem problem,
											Proof proof,
											int indentation,
											AnalysisContext context,
											UnfoldingRuleBudget ruleBudget) {

		// The TRS of the problem to solve.
		Trs trs = problem.getTRS();
		SimpleCycleRegistry simpleCycles = new SimpleCycleRegistry();
		RuleUnfoldingContext unfoldingContext =
				new RuleUnfoldingContext(
						trs, simpleCycles, proof, context, ruleBudget);

		proof.printlnIfVerbose("# max_depth=" + this.parameters.getMaxDepth() +
				", unfold_variables=" + this.parameters.isVariableUnfoldingEnabled() +
				":",
				indentation);
		// From now, we need to print 2 more single spaces
		// at the beginning of each line of the proof.
		indentation += 2;

		// The maximum depth of an unfolded rule generated by this
		// processor. This is the value that is returned at the end
		// if this processor fails to prove infiniteness.
		int generatedMaxDepth = -1;

		// Some data structures used for unfolding.
		List<UnfoldedRuleTrs> rulesToUnfold = new ArrayList<>();
		List<UnfoldedRuleTrs> unfolded = new ArrayList<>();

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

			if (i == 0) {
				// At the first iteration, we have to initialize the
				// set of unfolded rules: we initialize it to the
				// syntactic loops occurring in the provided problem.
				// We also check whether a syntactic loop is a
				// nontermination witness.
				unfoldedRuleLimitReached = initializeUnfoldedRules(
						problem, unfoldingContext, unfolded);
			}
			else {
				unfoldedRuleLimitReached = unfoldRules(
						rulesToUnfold, unfolded, unfoldingContext, i);
			}

			// We build a small message indicating the
			// number of unfolded rules generated during
			// this iteration.
			int unfSize = unfolded.size();
			String msgNbGenerated =
					unfSize + " unfolded " +
							(1 < unfSize ? "rules" : "rule") +
							" generated.";

			if (proof.isSuccess()) {
				// Here, we have found a loop or a recurrent pair.
				proof.printlnIfVerbose("success, " + proof.getArgument().getWitnessKind()
						+ " found, " + msgNbGenerated);
				proof.printlnIfVerbose(proof.getArgument().getDetails(indentation));
				return null;
			}

			// Here, we have not found anything.
			proof.printlnIfVerbose("infiniteness not proved, " + msgNbGenerated);

			// We update the maximum depth of a generated rule.
			generatedMaxDepth = getMaxDepth(unfolded, generatedMaxDepth);

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
		proof.printlnIfVerbose("Could not prove infiniteness!", indentation);

		return generatedMaxDepth;
	}

	/**
	 * Collects the syntactic loops of the provided problem, eliminates their
	 * disagreement pairs and checks whether they prove nontermination.
	 *
	 * @param problem the dependency pair problem being processed
	 * @param unfoldingContext the shared state of the unfolding execution
	 * @param unfolded the collection receiving the generated unfolded rules
	 * @return the result of the initialization iteration
	 */
	private boolean initializeUnfoldedRules(
			DependencyPairProblem problem,
			RuleUnfoldingContext unfoldingContext,
			List<UnfoldedRuleTrs> unfolded) {

		TrsSyntacticLoopCollector syntacticLoopCollector =
				new TrsSyntacticLoopCollector();
		Iterator<UnfoldedRuleTrs> ruleIterator = syntacticLoopCollector.collectFrom(
				problem.getDependencyPairs()).iterator();
		Thread currentThread = Thread.currentThread();
		while (!currentThread.isInterrupted() &&
				!unfoldingContext.proof().isSuccess() &&
				unfoldingContext.ruleBudget().hasRemainingCapacity() &&
				ruleIterator.hasNext()) {
			UnfoldedRuleTrs rule = ruleIterator.next();
			Collection<UnfoldedRuleTrs> generatedRules =
					rule.elimAndProve(this.parameters, unfoldingContext.trs(),
							unfoldingContext.simpleCycles(), unfoldingContext.proof());
			int currentGeneratedRuleCount = generatedRules.size();
			unfoldingContext.ruleBudget().recordGeneratedRules(
					currentGeneratedRuleCount);
			unfoldingContext.analysisContext().incGeneratedRules(
					currentGeneratedRuleCount);
			unfolded.addAll(generatedRules);
		}

		return !unfoldingContext.ruleBudget().hasRemainingCapacity();
	}

	/**
	 * Unfolds the rules generated during the preceding iteration.
	 *
	 * @param rulesToUnfold the work collection receiving the rules to unfold
	 * @param unfolded the collection containing the rules from the preceding
	 * iteration and receiving the newly generated rules
	 * @param unfoldingContext the shared state of the unfolding execution
	 * @param iteration the current unfolding iteration number
	 * @return the result of this unfolding iteration
	 */
	private boolean unfoldRules(
			List<UnfoldedRuleTrs> rulesToUnfold,
			List<UnfoldedRuleTrs> unfolded,
			RuleUnfoldingContext unfoldingContext,
			int iteration) {

		rulesToUnfold.clear();
		rulesToUnfold.addAll(unfolded);
		unfolded.clear();

		Iterator<UnfoldedRuleTrs> ruleIterator = rulesToUnfold.iterator();
		Thread currentThread = Thread.currentThread();
		while (!currentThread.isInterrupted() &&
				!unfoldingContext.proof().isSuccess() &&
				unfoldingContext.ruleBudget().hasRemainingCapacity() &&
				ruleIterator.hasNext()) {
			UnfoldedRuleTrs rule = ruleIterator.next();
			Collection<UnfoldedRuleTrs> generatedRules =
					rule.unfold(this.parameters, unfoldingContext.trs(),
							unfoldingContext.simpleCycles(), iteration,
							unfoldingContext.proof());
			int currentGeneratedRuleCount = generatedRules.size();
			unfoldingContext.ruleBudget().recordGeneratedRules(
					currentGeneratedRuleCount);
			unfoldingContext.analysisContext().incGeneratedRules(
					currentGeneratedRuleCount);
			if (iteration == 1 && !unfoldingContext.proof().isSuccess())
				probeRootClosingComposites(generatedRules, unfoldingContext,
						iteration + 1);
			unfolded.addAll(generatedRules);
		}

		return !unfoldingContext.ruleBudget().hasRemainingCapacity();
	}

	/**
	 * Gives one-step lookahead to newly generated composed triples whose
	 * first left root is restored by the second rule. Such a triple is one
	 * unfolding step away from a possible root loop, but a broad frontier can
	 * otherwise postpone that check beyond the generated-rule budget.
	 *
	 * @param generatedRules the newly generated rules to inspect
	 * @param unfoldingContext the shared state of the unfolding execution
	 * @param iteration the iteration assigned to lookahead successors
	 */
	private void probeRootClosingComposites(
			Collection<UnfoldedRuleTrs> generatedRules,
			RuleUnfoldingContext unfoldingContext,
			int iteration) {

		for (UnfoldedRuleTrs generatedRule : generatedRules) {
			if (Thread.currentThread().isInterrupted() ||
					unfoldingContext.proof().isSuccess() ||
					!unfoldingContext.ruleBudget().hasRemainingCapacity())
				return;

			if (generatedRule instanceof UnfoldedRuleTrsComp composed &&
					composed.getFirst().getLeft().getRootSymbol() ==
							composed.getSecond().getRight().getRootSymbol()) {
				Collection<UnfoldedRuleTrs> lookahead = generatedRule.unfold(
						this.parameters, unfoldingContext.trs(),
						new SimpleCycleRegistry(), iteration,
						unfoldingContext.proof());
				int generatedRuleCount = lookahead.size();
				unfoldingContext.ruleBudget().recordGeneratedRules(
						generatedRuleCount);
				unfoldingContext.analysisContext().incGeneratedRules(
						generatedRuleCount);
			}
		}
	}

	/**
	 * The shared state of one rule-unfolding execution.
	 *
	 * @param trs the TRS used for unfolding
	 * @param simpleCycles the registry of simple cycles found during unfolding
	 * @param proof the proof receiving a nontermination witness, if one is found
	 * @param analysisContext the context whose generated-rule counter is updated
	 * @param ruleBudget the generated-rule budget local to this processor run
	 */
	private record RuleUnfoldingContext(
			Trs trs,
			SimpleCycleRegistry simpleCycles,
			Proof proof,
			AnalysisContext analysisContext,
			UnfoldingRuleBudget ruleBudget) {}

	/**
	 * Computes the maximum depth of a rule in
	 * the specified collection. Returns the
	 * max between this value and the provided
	 * <code>maxDepth</code>.
	 *
	 * @param unfolded a collection a rules whose
	 * maximum depth is to be computed
	 * @param maxDepth a value to be compared to
	 * the maximum depth of a rule in the specified
	 * collection
	 * @return the max between the maximum depth
	 * and the provided <code>maxDepth</code>
	 */
	private static int getMaxDepth(Collection<UnfoldedRuleTrs> unfolded, int maxDepth) {
		for (UnfoldedRuleTrs rule : unfolded) {
			int m = rule.depth();
			if (maxDepth < m) maxDepth = m;
		}

		return maxDepth;
	}

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
				"## DP Processor: [Payet, LOPSTR'18 + JAR'24 + LOPSTR'25] (" +
				this.parameters + "). ";
	}
}
