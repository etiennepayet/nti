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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import java.util.List;
import java.util.Objects;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.prooftech.ProofTechnique;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;

/**
 * A technique for proving termination and nontermination of term
 * rewrite systems. It is an implementation of the dependency pair
 * framework. It consists in applying some specific dependency pair
 * processors in a specific order.
 *
 * <p>The framework is from J. Giesl, R. Thiemann, and P. Schneider-Kamp,
 * <a href="https://doi.org/10.1007/978-3-540-32275-7_21"><i>The Dependency
 * Pair Framework: Combining Techniques for Automated Termination
 * Proofs</i></a>, LPAR 2004, LNCS 3452, pp. 301--331, 2005.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class DependencyPairFramework implements ProofTechnique {

	/**
	 * The indentation for introducing and closing
	 * a dependency pair problem.
	 */
	private static final int PROBLEM_INDENTATION = 2;

	/** The collaborator that applies finiteness processors sequentially. */
	private final SequentialDependencyPairFinitenessProver finitenessProver;

	/**
	 * The collaborator that applies infiniteness processors concurrently.
	 */
	private final ConcurrentDependencyPairInfinitenessProver infinitenessProver;

	/**
	 * Builds a dependency pair framework
	 * which consists in applying the specified dependency
	 * pair processors.
	 *
	 * @param finitenessProcessors the dependency pair processors
	 * to apply for proving finiteness; must not be {@code null}
	 * but may be empty
	 * @param infinitenessProcessors the dependency pair processors
	 * to apply for proving infiniteness; must not be {@code null}
	 * but may be empty
	 */
	DependencyPairFramework(List<DependencyPairProcessor> finitenessProcessors,
			List<DependencyPairProcessor> infinitenessProcessors) {

		this.finitenessProver = new SequentialDependencyPairFinitenessProver(
				Objects.requireNonNull(finitenessProcessors));
		this.infinitenessProver = new ConcurrentDependencyPairInfinitenessProver(
				Objects.requireNonNull(infinitenessProcessors));
	}

	/**
	 * Returns the infiniteness attempts built during the latest framework run.
	 *
	 * @return the attempts in problem-then-processor order, or an empty list if
	 * the infiniteness phase was not reached
	 */
	List<DependencyPairInfinitenessAttempt> infinitenessAttempts() {
		return this.infinitenessProver.attempts();
	}

	/**
	 * Runs this technique on the specified TRS
	 * and builds a proof.
	 *
	 * @param trs a TRS whose termination or
	 * nontermination has to be proved
	 * @param context the context of the analysis
	 * @return the proof that is built by this
	 * technique
	 */
	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		// The proof that will be returned.
		Proof proof = context.createProof();

		proof.printlnIfVerbose("## Applying the DP framework...");

		// We compute the initial dependency pair problems to solve.
		DependencyPairProblemCollection initialProblems =
				new InitialDependencyPairProblemCollector().collectFrom(trs);

		if (initialProblems.isEmpty())
			completeProofWithoutInitialProblems(proof);
		else
			this.proveFromInitialProblems(initialProblems, context, proof);

		return proof;
	}

	/**
	 * Completes a termination proof when the estimated dependency graph has no
	 * strongly connected component.
	 *
	 * @param proof the proof to complete
	 */
	private static void completeProofWithoutInitialProblems(Proof proof) {
		proof.printlnIfVerbose("The TRS under analysis terminates because the set of SCCs");
		proof.printlnIfVerbose("of its estimated dependency graph is empty.");
		proof.setArgument("The set of SCCs of the estimated dependency graph is empty.");
		proof.setResult(Proof.ProofResult.YES);
	}

	/**
	 * First tries to prove all initial dependency pair problems finite, then
	 * tries to prove one remaining problem infinite when necessary.
	 *
	 * @param initialProblems the initial dependency pair problems to solve
	 * @param context the context of the analysis
	 * @param proof the proof receiving the complete framework result
	 */
	private void proveFromInitialProblems(
			DependencyPairProblemCollection initialProblems,
			AnalysisContext context,
			Proof proof) {

		reportInitialProblems(initialProblems.size(), proof);

		DependencyPairProcessorResult result =
				this.finitenessProver.prove(initialProblems, context);
		proof.merge(result.getProof());

		if (result.isFinite())
			completeFinitenessProof(proof);
		else if (result.isDecomposed())
			this.tryProveInfiniteness(result.getSubproblems(), context, proof);
		else
			proof.printlnIfVerbose("## TERMINATION PROVER RETURNED AN UNEXPECTED RESULT!");
	}

	/**
	 * Reports the number of initial dependency pair problems and introduces the
	 * finiteness phase.
	 *
	 * @param initialProblemCount the number of initial problems to solve
	 * @param proof the proof receiving the report
	 */
	private static void reportInitialProblems(int initialProblemCount, Proof proof) {
		proof.printlnIfVerbose("## " + initialProblemCount +
				" initial DP problem" + (initialProblemCount > 1 ? "s" : "") + " to solve.");

		proof.printIfVerbose("## First, we try to decompose ");
		proof.printIfVerbose(initialProblemCount > 1 ? "these problems" : "this problem");
		proof.printlnIfVerbose(" into smaller problems.");
	}

	/**
	 * Completes the proof after all dependency pair problems have been proved
	 * finite.
	 *
	 * @param proof the proof to complete
	 */
	private static void completeFinitenessProof(Proof proof) {
		String successMessage = """
				All the DP problems were proved finite.
				As all the involved DP processors are sound,
				the TRS under analysis terminates.""";

		proof.printlnIfVerbose("## " + successMessage);
		proof.setArgument(successMessage);
		proof.setResult(Proof.ProofResult.YES);
	}

	/**
	 * Tries concurrently to prove one unsolved dependency pair problem infinite
	 * and completes or reports the proof accordingly.
	 *
	 * @param unsolvedProblems the problems not proved finite
	 * @param context the context of the analysis
	 * @param proof the proof receiving the infiniteness phase result
	 */
	private void tryProveInfiniteness(
			DependencyPairProblemCollection unsolvedProblems,
			AnalysisContext context,
			Proof proof) {

		reportInfinitenessAttempt(unsolvedProblems.size(), proof);

		DependencyPairProcessorResult result =
				this.infinitenessProver.prove(unsolvedProblems, context);
		proof.merge(result.getProof());

		if (result.isInfinite()) {
			proof.printlnIfVerbose("This DP problem is infinite.", PROBLEM_INDENTATION);
			proof.setResult(Proof.ProofResult.NO);
		}
		else
			reportUnsolvedProblems(unsolvedProblems, proof);
	}

	/**
	 * Introduces the attempt to prove one unsolved problem infinite.
	 *
	 * @param unsolvedProblemCount the number of problems not proved finite
	 * @param proof the proof receiving the report
	 */
	private static void reportInfinitenessAttempt(
			int unsolvedProblemCount, Proof proof) {

		proof.printlnIfVerbose("## " +
				(unsolvedProblemCount > 1 ? "Some DP problems" : "A DP problem") +
				" could not be proved finite.");
		proof.printlnIfVerbose("## Now, we try to prove that " +
				(unsolvedProblemCount > 1 ? "one of these problems" : "this problem") +
				" is infinite.");
	}

	/**
	 * Reports the dependency pair problems for which neither finiteness nor
	 * infiniteness could be proved.
	 *
	 * @param unsolvedProblems the unsolved dependency pair problems
	 * @param proof the proof receiving the report
	 */
	private static void reportUnsolvedProblems(
			DependencyPairProblemCollection unsolvedProblems,
			Proof proof) {

		proof.printlnIfVerbose("## Could not solve the following DP problems:");
		int index = 1;
		for (DependencyPairProblem problem : unsolvedProblems)
			proof.printlnIfVerbose((index++) + ": " + problem);
		proof.printlnIfVerbose(
				"Hence, could not prove (non)termination of the TRS under analysis.");
	}

}
