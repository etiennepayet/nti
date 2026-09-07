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
import java.util.HashSet;
import java.util.List;
import java.util.Optional;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.reducpair.Lpo;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A sound dependency pair processor for proving that a
 * dependency pair problem is finite using lexicographic
 * path orders.
 *
 * <p>The lexicographic path order is presented in F. Baader and T. Nipkow,
 * <a href="https://doi.org/10.1017/CBO9781139172752"><i>Term Rewriting and
 * All That</i></a>, Cambridge University Press, 1998, Sect. 5.4. Its use as
 * a reduction pair with argument filterings and usable rules follows
 * N. Hirokawa and A. Middeldorp,
 * <a href="https://doi.org/10.1007/978-3-540-25979-4_18"><i>Dependency Pairs
 * Revisited</i></a>, RTA 2004, LNCS 3091, pp. 249--268.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LpoDependencyPairProcessor extends FinitenessDependencyPairProcessor {

	/**
	 * Builds a dependency pair processor for proving
	 * finiteness using lexicographic path orders.
	 *
	 * @param usesFiltering <code>true</code> iff
	 * this processor uses argument filtering
	 */
	public LpoDependencyPairProcessor(boolean usesFiltering) {
		super(usesFiltering);
	}

	/**
	 * First tries the standard usable-rule refinement in the unfiltered
	 * framework variant, then delegates to the ordinary full-TRS search.
	 * The filtered usable-rule attempt is performed for each argument filtering
	 * by the protected {@code run} method below.
	 */
	@Override
	public DependencyPairProcessorResult run(
			DependencyPairProblem problem,
			ArgFiltering filtering,
			int indentation,
			AnalysisContext context) {

		if (!this.usesFiltering()) {
			if (UsableRules.containsGeneralizedRule(problem.getTRS())) {
				Proof proof = context.createProof();
				proof.printlnIfVerbose(
						"Usable rules are not applied to a generalized TRS.",
						indentation);
				return DependencyPairProcessorResult.failed(proof);
			}
			DependencyPairProcessorResult result = this.runWithUsableRules(
					problem, null, problem.getTRS().toPairsOfTerms(),
					problem.getDependencyPairs().toPairsOfTerms(),
					indentation, context);
			if (!result.isFailed())
				return result;
			if (Thread.currentThread().isInterrupted())
				return result;
		}

		return super.run(problem, filtering, indentation, context);
	}

	/**
	 * Runs this processor on the provided collections
	 * <code>trsPairs</code> and <code>dependencyPairs</code> that result
	 * from applying the provided argument filtering
	 * <code>filtering</code> respectively to the TRS and
	 * to the dependency pairs of the provided DP problem
	 * <code>problem</code>.
	 * <p>
	 * The returned result indicates whether the provided
	 * problem could be proved finite or could be decomposed
	 * into a collection of subproblems.
	 *
	 * @param problem a DP problem to solve using this processor
	 * @param filtering an argument filtering for solving
	 * <code>problem</code> (<code>null</code> if only the
	 * full problem has to be considered)
	 * @param trsPairs the result of applying <code>filtering</code>
	 * to the TRS of <code>problem</code>
	 * @param dependencyPairs the result of applying <code>filtering</code>
	 * to the dependency pairs of <code>problem</code>
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the created proof
	 * @param context the context of the analysis
	 * @return the result of this processor
	 */
	@Override
	protected DependencyPairProcessorResult run(DependencyPairProblem problem,
						   ArgFiltering filtering,
						   Collection<PairOfTerms> trsPairs,
						   Collection<PairOfTerms> dependencyPairs,
						   int indentation,
						   AnalysisContext context) {

		if (filtering != null) {
			DependencyPairProcessorResult result = this.runWithUsableRules(
					problem, filtering, trsPairs, dependencyPairs,
					indentation, context);
			if (!result.isFailed() || Thread.currentThread().isInterrupted())
				return result;
		}

		return this.runWithPairs(problem, filtering, trsPairs, dependencyPairs,
				indentation, context, null);
	}

	/**
	 * Runs LPO on the usable-rule restriction of the specified pairs. For an
	 * argument filtering, this is the usable-rule criterion of Theorem 29 in
	 * Hirokawa and Middeldorp, <i>Dependency Pairs Revisited</i>.
	 *
	 * @see <a href="https://doi.org/10.1007/978-3-540-25979-4_18">
	 * Dependency Pairs Revisited, Theorem 29</a>
	 */
	private DependencyPairProcessorResult runWithUsableRules(
			DependencyPairProblem problem,
			ArgFiltering filtering,
			Collection<PairOfTerms> trsPairs,
			Collection<PairOfTerms> dependencyPairs,
			int indentation,
			AnalysisContext context) {

		Proof proof = context.createProof();
		if (UsableRules.containsGeneralizedRule(problem.getTRS())) {
			proof.printlnIfVerbose(
					"Usable rules are not applied to a generalized TRS.",
					indentation);
			return DependencyPairProcessorResult.failed(proof);
		}

		Optional<List<RuleTrs>> usableRules = UsableRules.collect(problem);
		if (usableRules.isEmpty())
			return DependencyPairProcessorResult.failed(proof);

		Collection<PairOfTerms> usablePairs = UsableRules.selectPairs(
				trsPairs, usableRules.get());
		return this.runWithPairs(problem, filtering, usablePairs, dependencyPairs,
				indentation, context, usableRules.get());
	}

	/** Runs the LPO completion on the specified rule and dependency-pair sets. */
	private DependencyPairProcessorResult runWithPairs(
			DependencyPairProblem problem,
			ArgFiltering filtering,
			Collection<PairOfTerms> trsPairs,
			Collection<PairOfTerms> dependencyPairs,
			int indentation,
			AnalysisContext context,
			List<RuleTrs> usableRules) {

		// The proof of the returned result.
		Proof proof = context.createProof();

		// We indicate which argument filtering is used.
		this.printFiltering(filtering, proof, indentation);
		if (usableRules != null)
			proof.printlnIfVerbose("Using usable rules: " + usableRules,
					indentation);

		int nbSymbols = this.nbFunSymbols(trsPairs, dependencyPairs);
		if (20 < nbSymbols) {
			// If, from the data collected so far, we infer that the problem
			// is not suitable for the lexicographic path order technique,
			// then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex (" +
					nbSymbols +
					" symbols to deal with)! Aborting!", indentation);
			return DependencyPairProcessorResult.failed(proof);
		}

		// We try to infer a lexicographic path order
		// satisfying the constraints over the specified
		// DP problem.
		Lpo lpo = new Lpo();

		if (!lpo.complete(trsPairs) || !lpo.complete(dependencyPairs))
			return DependencyPairProcessorResult.failed(proof);

		// Here, we are sure that for each dependency pair
		// l -> r we have l >= r where >= is the current LPO.
		// Let us collect the dependency pairs l -> r such
		// that l > r does not hold.
		List<RuleTrs> nonStrictRules = new ArrayList<>();
		for (PairOfTerms pair : dependencyPairs)
			if (pair.left().deepEquals(pair.right()))
				nonStrictRules.add(pair.rule());

		// Here, for each l -> r in 'nonStrictRules', we have
		// l = r w.r.t. the current LPO.
		DependencyPairProcessorResult result = getResult(
				problem, lpo, nonStrictRules, null, proof, indentation);
		if (result == null)
			return DependencyPairProcessorResult.failed(proof);

		if (result.isDecomposed())
			proof.printlnIfVerbose(lpo.toString(indentation));

		return result;
	}

	/**
	 * Computes the total number of function symbols
	 * occurring in the provided collections.
	 *
	 * @param trsPairs the result of applying an argument
	 * filtering to the TRS of the problem to solve
	 * @param dependencyPairs the result of applying an argument
	 * filtering to the dependency pairs of the problem
	 * to solve
	 * @return the total number of function symbols
	 * occurring in the provided collections
	 */
	private int nbFunSymbols(
			Collection<PairOfTerms> trsPairs,
			Collection<PairOfTerms> dependencyPairs) {

		// We build the set of function symbols occurring
		// in the TRS pairs and the dependency pairs.
		HashSet<FunctionSymbol> symbols = new HashSet<>();

		for (PairOfTerms pair : trsPairs) {
			symbols.addAll(pair.left().getFunSymbols());
			symbols.addAll(pair.right().getFunSymbols());
		}

		for (PairOfTerms pair : dependencyPairs) {
			symbols.addAll(pair.left().getFunSymbols());
			symbols.addAll(pair.right().getFunSymbols());
		}

		// We return the size of the set that we have built.
		return symbols.size();
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		return "## DP Processor: lexicographic path orders. ";
	}
}
