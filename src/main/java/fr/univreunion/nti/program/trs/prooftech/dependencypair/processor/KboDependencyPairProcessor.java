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
import java.util.Optional;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.polynomial.ArithOperator;
import fr.univreunion.nti.program.trs.polynomial.CoefficientInstantiator;
import fr.univreunion.nti.program.trs.polynomial.Constraint;
import fr.univreunion.nti.program.trs.polynomial.Intervals;
import fr.univreunion.nti.program.trs.polynomial.Polynomial;
import fr.univreunion.nti.program.trs.polynomial.PolynomialComp;
import fr.univreunion.nti.program.trs.polynomial.PolynomialConst;
import fr.univreunion.nti.program.trs.reducpair.Kbo;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A sound dependency pair processor for proving that a
 * dependency pair problem is finite using Knuth-Bendix
 * orders.
 *
 * <p>The Knuth--Bendix order is presented in F. Baader and T. Nipkow,
 * <a href="https://doi.org/10.1017/CBO9781139172752"><i>Term Rewriting and
 * All That</i></a>, Cambridge University Press, 1998, Sect. 5.4. Its use as
 * a reduction pair with argument filterings and usable rules follows
 * N. Hirokawa and A. Middeldorp,
 * <a href="https://doi.org/10.1007/978-3-540-25979-4_18"><i>Dependency Pairs
 * Revisited</i></a>, RTA 2004, LNCS 3091, pp. 249--268.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class KboDependencyPairProcessor extends FinitenessDependencyPairProcessor {

	/**
	 * A threshold for choosing the right interval of values
	 * for instantiating the coefficients associated with the
	 * TRS of the problem to solve.
	 */
	private static final int TRS_COEFFICIENT_THRESHOLD = 14;

	/**
	 * A threshold for choosing the right interval of values
	 * for instantiating the coefficients associated with the
	 * dependency pairs of the problem to solve.
	 */
	private static final int DEPENDENCY_PAIR_COEFFICIENT_THRESHOLD = 4;

	/**
	 * The upper limit of the interval of values
	 * used for instantiating the coefficients.
	 * This constant is used if the number of
	 * coefficients to instantiate does not exceed
	 * the threshold.
	 */
	private static final int LARGE_INSTANTIATION_UPPER_BOUND = 2;

	/**
	 * The upper limit of the interval of values
	 * used for instantiating the coefficients.
	 * This constant is used if the number of
	 * coefficients to instantiate exceeds the
	 * threshold.
	 */
	private static final int SMALL_INSTANTIATION_UPPER_BOUND = 1;

	// The small upper bound works for the vast majority of
	// the competition's benchmarks and it speeds up the
	// analysis. But the large upper bound is needed for
	// solving some few competition's
	// benchmarks (e.g., Applicative_05/ReverseLastInit.xml).


	/**
	 * The maximum number of weights that this processor
	 * is able to instantiate. If the number of weights
	 * associated with the TRS under analysis is greater
	 * than this bound, then the termination proof is
	 * aborted.
	 */
	private final int maxNbWeights;

	/**
	 * Builds a dependency pair processor for proving
	 * finiteness using Knuth-Bendix orders.
	 *
	 * @param usesFiltering <code>true</code> iff
	 * this processor uses argument filtering
	 * @param maxNbWeights the maximum number of weights
	 * that this processor is able to instantiate
	 */
	public KboDependencyPairProcessor(boolean usesFiltering, int maxNbWeights) {
		super(usesFiltering);

		this.maxNbWeights = maxNbWeights;
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

		if (!this.usesFiltering() &&
				!UsableRules.containsGeneralizedRule(problem.getTRS())) {
			DependencyPairProcessorResult result = this.runWithUsableRules(
					problem, null, problem.getTRS().toPairsOfTerms(),
					problem.getDependencyPairs().toPairsOfTerms(),
					indentation, context);
			if (!result.isFailed() || Thread.currentThread().isInterrupted())
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

		if (filtering != null &&
				!UsableRules.containsGeneralizedRule(problem.getTRS())) {
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
	 * Runs KBO on the usable-rule restriction of the specified pairs. For an
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
		Optional<List<RuleTrs>> usableRules = UsableRules.collect(problem);
		if (usableRules.isEmpty())
			return DependencyPairProcessorResult.failed(proof);

		Collection<PairOfTerms> usablePairs = UsableRules.selectPairs(
				trsPairs, usableRules.get());
		return this.runWithPairs(problem, filtering, usablePairs, dependencyPairs,
				indentation, context, usableRules.get());
	}

	/** Runs the KBO search on the specified rule and dependency-pair sets. */
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

		KboSearch search = this.prepareSearch(
				trsPairs, dependencyPairs, proof, indentation);
		if (search == null)
			return DependencyPairProcessorResult.failed(proof);

		return this.runSuitable(problem, search, proof, indentation);
	}

	/**
	 * Prepares the constraints, weight function and weight instantiators used
	 * for searching for a suitable Knuth-Bendix order.
	 *
	 * @param trsPairs the pairs obtained from the TRS of the problem
	 * @param dependencyPairs the pairs obtained from the dependency pairs of
	 * the problem
	 * @param proof the proof to complete if preparation has to be aborted
	 * @param indentation the number of single spaces to print at the beginning
	 * of each line in the specified proof
	 * @return the prepared KBO search, or <code>null</code> if preparation fails
	 */
	private KboSearch prepareSearch(
			Collection<PairOfTerms> trsPairs,
			Collection<PairOfTerms> dependencyPairs,
			Proof proof,
			int indentation) {

		// We reset the ID counter for constant polynomials.
		PolynomialConst.resetIDs();

		// The weights of the symbols occurring in the TRS pairs and the
		// dependency pairs.
		WeightFunction wf = new WeightFunction();

		// The intervals of values used for instantiating
		// constant polynomials.
		Intervals intervals = new Intervals();

		// We generate the weights and constraints associated
		// with the TRS pairs. The constraints ensure that the weight
		// function is admissible (see p. 124 of
		// [Baader & Nipkow, 1998]).
		Collection<Constraint> trsConstraints =
				this.buildConstraints(trsPairs, intervals, wf);

		// If a constraint generated from the TRS pairs is unsatisfiable,
		// then we stop everything.
		if (trsConstraints == null) return null;

		// The weight associated with all the variables
		// must not be zero.
		trsConstraints.add(new Constraint(wf.getVariableWeight(), true));

		// We need to record the weights associated with
		// the variables and the weights associated with
		// the symbols of the TRS pairs. They will be needed for
		// computing instantiators later.
		Collection<PolynomialConst> trsAndVariableWeights = wf.getAllCoefficients();
		trsAndVariableWeights.add(wf.getVariableWeight());

		// We generate the weights and constraints associated
		// with the dependency pairs. The constraints ensure that the weight
		// function is admissible (see p. 124 of
		// [Baader & Nipkow, 1998]).
		Collection<Constraint> dependencyPairConstraints =
				this.buildConstraints(dependencyPairs, intervals, wf);

		// If a constraint generated from the dependency pairs is unsatisfiable,
		// then we stop everything.
		if (dependencyPairConstraints == null) return null;

		int weightCount = wf.getNbFunctionCoefficients();
		if (this.maxNbWeights < weightCount) {
			// If the problem to solve has to many weights,
			// then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex (" + weightCount +
					" weights to instantiate)! Aborting!", indentation);
			return null;
		}

		// We build instantiators for the weights.
		// First, an instantiator for the weight associated with
		// the variables and the weights associated with the
		// symbols of the TRS pairs.
		CoefficientInstantiator trsAndVariableWeightInstantiator =
				new CoefficientInstantiator(trsAndVariableWeights, intervals,
						(trsAndVariableWeights.size() <= TRS_COEFFICIENT_THRESHOLD ?
								LARGE_INSTANTIATION_UPPER_BOUND : SMALL_INSTANTIATION_UPPER_BOUND));
		// Then, an instantiator for the weights associated with
		// the symbols of the dependency pairs.
		Collection<PolynomialConst> dependencyPairWeights = wf.getAllCoefficients();
		dependencyPairWeights.removeAll(trsAndVariableWeights);
		CoefficientInstantiator dependencyPairWeightInstantiator =
				new CoefficientInstantiator(dependencyPairWeights, intervals,
						(dependencyPairWeights.size() <= DEPENDENCY_PAIR_COEFFICIENT_THRESHOLD ?
								LARGE_INSTANTIATION_UPPER_BOUND : SMALL_INSTANTIATION_UPPER_BOUND));
		return new KboSearch(
				trsPairs, dependencyPairs,
				trsConstraints, dependencyPairConstraints,
				trsAndVariableWeightInstantiator, dependencyPairWeightInstantiator,
				wf);
	}

	/**
	 * Runs this processor on the provided DP problem, which
	 * is supposed to be suitable for this processor.
	 *
	 * @param problem a DP problem to solve using this processor
	 * @param search the prepared KBO search
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return the result of this processor
	 */
	private DependencyPairProcessorResult runSuitable(DependencyPairProblem problem,
			KboSearch search, Proof proof, int indentation) {

		// The best evaluation found so far.
		KboEvaluation bestEvaluation = null;

		// We try to infer a suitable Knuth-Bendix order
		// based on the weight function.
		Kbo kbo = new Kbo(search.weightFunction());

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();

		// The main loop of the processor.
		while (!currentThread.isInterrupted() &&
				search.trsAndVariableWeightInstantiator().hasNext()) {
			// Let us consider the next instantiation of
			// the weight associated with the variables
			// and the weights associated with the symbols
			// of the TRS pairs.
			search.trsAndVariableWeightInstantiator().next();

			kbo.clear();

			// Let us check whether the constraints associated with
			// the TRS pairs are satisfied by the current instantiation.
			// Let us also try to complete 'kbo'.
			if (allSatisfied(search.trsConstraints()) && kbo.complete(search.trsPairs())) {
				bestEvaluation = this.evaluateDependencyPairWeights(
						problem, search, kbo, bestEvaluation, proof, indentation);
				if (bestEvaluation != null && bestEvaluation.result().isFinite())
					return bestEvaluation.result();
			}
		}

		// Here, 'problem' could not be proved finite.
		// Either the proof has failed or 'problem' has
		// been decomposed into more than one smaller
		// problems.

		if (bestEvaluation == null)
			// Here, the proof has failed.
			return DependencyPairProcessorResult.failed(proof);

		// Here, the problem has been decomposed.
		proof.printlnIfVerbose(bestEvaluation.kbo().toString(indentation));
		return bestEvaluation.result();
	}

	/**
	 * Evaluates the dependency-pair weight instantiations for the current
	 * instantiation of the TRS and variable weights.
	 *
	 * @param problem the dependency pair problem being solved
	 * @param search the prepared KBO search
	 * @param trsKbo the KBO completed for the current TRS-weight instantiation
	 * @param bestEvaluation the best evaluation found previously, or
	 * <code>null</code> if none has been found
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print at the beginning
	 * of each line in the specified proof
	 * @return the best evaluation found so far, or <code>null</code> if no
	 * instantiation yields a result
	 */
	private KboEvaluation evaluateDependencyPairWeights(
			DependencyPairProblem problem,
			KboSearch search,
			Kbo trsKbo,
			KboEvaluation bestEvaluation,
			Proof proof,
			int indentation) {

		search.dependencyPairWeightInstantiator().reset();
		Thread currentThread = Thread.currentThread();
		while (!currentThread.isInterrupted() &&
				search.dependencyPairWeightInstantiator().hasNext()) {
			search.dependencyPairWeightInstantiator().next();
			DependencyPairProcessorResult bestResult = bestEvaluation == null
					? null : bestEvaluation.result();
			KboEvaluation evaluation = this.evaluateDependencyPairWeightInstantiation(
					problem, search, trsKbo, bestResult, proof, indentation);
			if (evaluation != null) {
				bestEvaluation = evaluation;
				if (evaluation.result().isFinite()) break;
			}
		}

		return bestEvaluation;
	}

	/**
	 * Evaluates the current dependency-pair weight instantiation.
	 *
	 * @param problem the dependency pair problem being solved
	 * @param search the prepared KBO search
	 * @param trsKbo the KBO completed for the current TRS-weight instantiation
	 * @param bestResult the best result found by previous instantiations, or
	 * <code>null</code> if none has been found
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print at the beginning
	 * of each line in the specified proof
	 * @return the result and completed KBO obtained for this instantiation, or
	 * <code>null</code> if it yields no result
	 */
	private KboEvaluation evaluateDependencyPairWeightInstantiation(
			DependencyPairProblem problem,
			KboSearch search,
			Kbo trsKbo,
			DependencyPairProcessorResult bestResult,
			Proof proof,
			int indentation) {

		// We work on a copy so that the TRS KBO remains unchanged if the
		// current dependency-pair weights do not yield a result.
		Kbo kbo = new Kbo(trsKbo);
		if (!allSatisfied(search.dependencyPairConstraints()) ||
				!kbo.complete(search.dependencyPairs()) ||
				!kbo.completeAdmissible2())
			return null;

		List<RuleTrs> nonStrictRules = new ArrayList<>();
		for (PairOfTerms pair : search.dependencyPairs())
			if (pair.left().deepEquals(pair.right()))
				nonStrictRules.add(pair.rule());

		DependencyPairProcessorResult result = getResult(
				problem, kbo, nonStrictRules, bestResult, proof, indentation);
		return result == null ? null : new KboEvaluation(result, kbo);
	}

	/**
	 * The result of evaluating one dependency-pair weight instantiation.
	 *
	 * @param result the finite result or best decomposition after evaluation
	 * @param kbo the completed KBO used for this evaluation
	 */
	private record KboEvaluation(DependencyPairProcessorResult result, Kbo kbo) {
	}

	/**
	 * The elements prepared for searching for a suitable Knuth-Bendix order.
	 *
	 * @param trsPairs the TRS pairs to consider
	 * @param dependencyPairs the dependency pairs to consider
	 * @param trsConstraints the constraints associated with the TRS pairs
	 * @param dependencyPairConstraints the constraints associated with the
	 * dependency pairs
	 * @param trsAndVariableWeightInstantiator the instantiator for the variable
	 * weight and the weights associated with the TRS pairs
	 * @param dependencyPairWeightInstantiator the instantiator for the weights
	 * associated only with the dependency pairs
	 * @param weightFunction the weight function shared by the instantiators and
	 * the Knuth-Bendix order
	 */
	private record KboSearch(
			Collection<PairOfTerms> trsPairs,
			Collection<PairOfTerms> dependencyPairs,
			Collection<Constraint> trsConstraints,
			Collection<Constraint> dependencyPairConstraints,
			CoefficientInstantiator trsAndVariableWeightInstantiator,
			CoefficientInstantiator dependencyPairWeightInstantiator,
			WeightFunction weightFunction) {
	}

	/**
	 * Generates the weights associated with the symbols of the specified pairs
	 * of terms and inserts them into the provided weight function. Also
	 * generates and returns the polynomial constraints ensuring that the
	 * provided weight function is admissible (see p. 124 of Baader & Nipkow
	 * 'Term Rewriting and All That', 2000).
	 * <p>
	 * If unsatisfiability is detected, then <code>null</code>
	 * is returned.
	 * <p>
	 * If some generated constraints yield minimal or maximal
	 * values for some constant polynomials, then the specified
	 * intervals are completed accordingly.
	 *
	 * @param pairs a collection of pairs of terms
	 * @param intervals intervals of values that have to be
	 * used for instantiating some constant polynomials
	 * @param wf the weight function to fill with the
	 * generated weights
	 * @return the constraints ensuring that the provided weight
	 * function is admissible, or <code>null</code> if a generated
	 * constraint is unsatisfiable
	 */
	private Collection<Constraint> buildConstraints(
			Collection<PairOfTerms> pairs, Intervals intervals, WeightFunction wf) {

		// The collection to return at the end.
		Collection<Constraint> constraints = new ArrayList<>();

		// First, we generate the weight of each function symbol.
		for (PairOfTerms pair : pairs) {
			pair.left().generateKBOWeights(wf);
			pair.right().generateKBOWeights(wf);
		}

		// The weight associated with all the variables.
		PolynomialConst w = wf.getVariableWeight();

		// The weight of each constant symbol must be greater
		// than or equal to the weight of the variables.
		Iterator<FunctionSymbol> it = wf.symbolsIterator();
		while (it.hasNext()) {
			FunctionSymbol f = it.next();

			if (f.getArity() == 0) {
				// f is a constant: we generate a constraint c
				// of the form 0 <= w(f) - w, where w(f) is the
				// weight of f.
				Polynomial polynomial = PolynomialComp.simplified(ArithOperator.MINUS,
						wf.get(f)[0],
						w);
				// We try to update the previously generated collection
				// of constraints and the intervals using c.
				// If unsatisfiability is detected, then we stop everything
				// and return null.
				if (!(new Constraint(polynomial, false)).update(constraints, intervals))
					return null;
			}
		}

		return constraints;
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		return "## DP Processor: Knuth-Bendix orders. ";
	}

	/**
	 * Checks whether all the constraints in the
	 * specified collection are satisfied.
	 *
	 * @param constraints a collection of constraints
	 * @return <code>true</code> iff all the constraints
	 * in the specified collection are satisfied
	 */
	private static boolean allSatisfied(Collection<Constraint> constraints) {

		for (Constraint c : constraints)
			if (c.isUnsatisfied(null)) return false;

		return true;
	}
}
