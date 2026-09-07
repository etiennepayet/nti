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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;

/** Applies finiteness processors sequentially over successive problem rounds. */
final class SequentialDependencyPairFinitenessProver {

	/** The indentation for problem-level messages. */
	private static final int PROBLEM_INDENTATION = 2;

	/** The indentation for processor introductions. */
	private static final int PROCESSOR_INDENTATION = 4;

	/** The indentation for processor-result messages. */
	private static final int PROCESSOR_BODY_INDENTATION = 6;

	/** The processors to apply in order. */
	private final List<DependencyPairProcessor> processors = new ArrayList<>();

	/**
	 * Builds a prover using the provided finiteness processors.
	 *
	 * @param processors the processors to apply in order
	 */
	SequentialDependencyPairFinitenessProver(
			List<DependencyPairProcessor> processors) {

		this.processors.addAll(processors);
	}

	/**
	 * Tries to prove all provided dependency pair problems finite.
	 *
	 * <p>This method consumes the provided collection while progressing through
	 * decomposition rounds.</p>
	 *
	 * @param problems the dependency pair problems to process
	 * @param context the context of the analysis
	 * @return a finite result, or a decomposed result containing unsolved problems
	 */
	DependencyPairProcessorResult prove(
			DependencyPairProblemCollection problems,
			AnalysisContext context) {

		Thread currentThread = Thread.currentThread();
		DependencyPairProblemCollection unsolvedProblems =
				new DependencyPairProblemCollection();
		Proof proof = context.createProof();
		DependencyPairProblemCollection nextRoundProblems =
				new DependencyPairProblemCollection();

		int round = 1;
		while (!problems.isEmpty() && !currentThread.isInterrupted()) {
			reportRound(round, problems.size(), proof);
			processRound(
					problems, nextRoundProblems, unsolvedProblems,
					proof, context, currentThread);

			problems.clear();
			problems.addAll(nextRoundProblems);
			nextRoundProblems.clear();
			round++;
		}

		return unsolvedProblems.isEmpty()
				? DependencyPairProcessorResult.finite(proof)
				: DependencyPairProcessorResult.decomposed(proof, unsolvedProblems);
	}

	/**
	 * Processes every non-interrupted problem in one round.
	 *
	 * @param problems the problems in the current round
	 * @param nextRoundProblems the collection receiving decomposed subproblems
	 * @param unsolvedProblems the collection receiving failed problems
	 * @param proof the proof receiving processor output
	 * @param context the context of the analysis
	 * @param currentThread the thread running the proof
	 */
	private void processRound(
			DependencyPairProblemCollection problems,
			DependencyPairProblemCollection nextRoundProblems,
			DependencyPairProblemCollection unsolvedProblems,
			Proof proof,
			AnalysisContext context,
			Thread currentThread) {

		for (DependencyPairProblem problem : problems) {
			if (currentThread.isInterrupted())
				break;

			proof.printlnIfVerbose("## DP problem:", PROBLEM_INDENTATION);
			proof.printlnIfVerbose(problem.toString(2));
			DependencyPairProcessorResult result =
					this.applyProcessors(problem, proof, context);
			recordResult(
					problem, result, nextRoundProblems, unsolvedProblems, proof);
		}
	}

	/**
	 * Records one processor result and reports its effect on the current round.
	 *
	 * @param problem the processed dependency pair problem
	 * @param result the processor result to record
	 * @param nextRoundProblems the collection receiving decomposed subproblems
	 * @param unsolvedProblems the collection receiving the failed problem
	 * @param proof the proof receiving the result report
	 */
	private static void recordResult(
			DependencyPairProblem problem,
			DependencyPairProcessorResult result,
			DependencyPairProblemCollection nextRoundProblems,
			DependencyPairProblemCollection unsolvedProblems,
			Proof proof) {

		if (result.isFailed()) {
			proof.printlnIfVerbose(
					"All the DP processors have failed!", PROBLEM_INDENTATION);
			proof.printlnIfVerbose(
					"Don't know whether this DP problem is finite.",
					PROBLEM_INDENTATION);
			unsolvedProblems.add(problem);
		}
		else if (result.isFinite()) {
			proof.printlnIfVerbose(
					"Success, finiteness proved!", PROCESSOR_BODY_INDENTATION);
			proof.printlnIfVerbose(
					"This DP problem is finite.", PROBLEM_INDENTATION);
		}
		else if (result.isDecomposed()) {
			nextRoundProblems.addAll(result.getSubproblems());
			int nextRoundProblemCount = nextRoundProblems.size();
			proof.printlnIfVerbose("Decomposed the DP problem into "
					+ nextRoundProblemCount + " smaller problem"
					+ (1 < nextRoundProblemCount ? "s " : " ") + "to solve!",
					PROCESSOR_BODY_INDENTATION);
		}
		else
			throw new IllegalStateException("unexpected result");
	}

	/**
	 * Applies processors in order until one succeeds or decomposes the problem.
	 *
	 * @param problem the dependency pair problem to process
	 * @param proof the proof receiving processor output
	 * @param context the context of the analysis
	 * @return the first successful or decomposed result, or a failed result
	 */
	private DependencyPairProcessorResult applyProcessors(
			DependencyPairProblem problem,
			Proof proof,
			AnalysisContext context) {

		ArgFiltering filtering = null;
		for (DependencyPairProcessor processor : this.processors) {
			proof.printlnIfVerbose(processor.toString(), PROCESSOR_INDENTATION);

			if (processor.usesFiltering() && filtering == null)
				filtering = buildFiltering(problem);

			DependencyPairProcessorResult result = processor.run(
					problem, filtering, PROCESSOR_BODY_INDENTATION, context);
			proof.merge(result.getProof());

			if (result.isFinite() || result.isDecomposed())
				return result;

			proof.printlnIfVerbose("Failed!", PROCESSOR_BODY_INDENTATION);
		}

		return DependencyPairProcessorResult.failed(context.createProof());
	}

	/**
	 * Builds the argument filtering for one dependency pair problem.
	 *
	 * @param problem the problem whose symbols define the filtering
	 * @return the constructed argument filtering
	 */
	private static ArgFiltering buildFiltering(DependencyPairProblem problem) {
		ArgFiltering filtering = new ArgFiltering();
		for (RuleTrs rule : problem.getTRS()) {
			rule.getLeft().buildFilters(filtering);
			rule.getRight().buildFilters(filtering);
		}
		for (RuleTrs rule : problem.getDependencyPairs()) {
			rule.getLeft().buildFilters(filtering);
			rule.getRight().buildFilters(filtering);
		}
		return filtering;
	}

	/**
	 * Reports the number of problems processed in one round.
	 *
	 * @param round the current round number
	 * @param problemCount the number of problems in the round
	 * @param proof the proof receiving the report
	 */
	private static void reportRound(int round, int problemCount, Proof proof) {
		proof.printlnIfVerbose(
				"## Round " + round + " [" + problemCount + " DP problem"
				+ (problemCount > 1 ? "s" : "") + "]:");
	}
}
