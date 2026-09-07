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

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

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
import fr.univreunion.nti.program.trs.polynomial.PolynomialVar;
import fr.univreunion.nti.program.trs.reducpair.PolyInterpretation;
import fr.univreunion.nti.program.trs.reducpair.PolyOrder;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A sound dependency pair processor for proving that a
 * dependency pair problem is finite. It consists in
 * searching for a suitable polynomial interpretation
 * of the function and tuple symbols.
 *
 * <p>The polynomial-ordering synthesis follows J. Giesl,
 * <a href="https://doi.org/10.1007/3-540-59200-8_77"><i>Generating
 * Polynomial Orderings for Termination Proofs</i></a>, RTA 1995, LNCS 914,
 * pp. 426--431. Its use as a reduction pair with argument filterings and
 * usable rules follows N. Hirokawa and A. Middeldorp,
 * <a href="https://doi.org/10.1007/978-3-540-25979-4_18"><i>Dependency Pairs
 * Revisited</i></a>, RTA 2004, LNCS 3091, pp. 249--268.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PolynomialInterpretationDependencyPairProcessor extends FinitenessDependencyPairProcessor {

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

	/**
	 * The maximum arity allowed for a symbol. Deep terms
	 * yield very intricate constraints which are difficult
	 * to solve.
	 */
	private static final int MAX_ARITY = 6;

	/**
	 * The maximum number of coefficient instantiations inspected by one
	 * usable-rule attempt. The ordinary full-TRS search is not bounded by this
	 * constant.
	 */
	private static final int MAX_USABLE_RULE_INSTANTIATION_COUNT = 10_000;


	/**
	 * The maximum number of coefficients that this processor
	 * is able to instantiate. If the number of coefficients
	 * associated with the TRS under analysis is greater than
	 * this bound, then the termination proof is aborted.
	 */
	private final int maxNbCoef;

	/**
	 * The maximum depth allowed for a TRS rule. If the depth
	 * of a rule of the TRS under analysis is greater than
	 * this bound, then the termination proof is aborted.
	 */
	private final int maxDepth;

	/**
	 * Builds a dependency pair processor for proving
	 * finiteness using polynomial interpretations.
	 *
	 * @param usesFiltering <code>true</code> iff this
	 * processor uses argument filtering
	 * @param maxNbCoef the maximum number of coefficients
	 * that this processor is able to instantiate
	 * @param maxDepth the maximum depth allowed for a
	 * TRS rule
	 */
	public PolynomialInterpretationDependencyPairProcessor(boolean usesFiltering,
			int maxNbCoef, int maxDepth) {

		super(usesFiltering);

		this.maxNbCoef = maxNbCoef;
		this.maxDepth = maxDepth;
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
	 * Runs the polynomial search on the usable-rule restriction of the
	 * specified pairs. The auxiliary projection rules of Theorem 29 are
	 * implicit: the generated constraints give every ordinary symbol the
	 * subterm property, and the interpretation can be extended with
	 * {@code c(x,y) = x + y}.
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

	/** Runs the polynomial search on the specified rule and DP sets. */
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

		if (this.isNotSuitable(trsPairs) ||
				(usableRules != null && this.isNotSuitable(dependencyPairs))) {
			// If 'trsPairs' is not suitable for the polynomial
			// interpretation technique, then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex! Aborting!", indentation);
			return DependencyPairProcessorResult.failed(proof);
		}

		PolynomialInterpretationSearch search = this.prepareSearch(
				trsPairs, dependencyPairs, usableRules != null,
				proof, indentation);
		if (search == null)
			return DependencyPairProcessorResult.failed(proof);

		CoefficientInstantiationBudget budget = usableRules == null
				? null
				: new CoefficientInstantiationBudget(
						MAX_USABLE_RULE_INSTANTIATION_COUNT);
		return this.runSuitable(problem, search, budget, proof, indentation);
	}

	/**
	 * Prepares the constraints, polynomial order and coefficient instantiators
	 * used for searching for a suitable polynomial interpretation.
	 *
	 * @param trsPairs the pairs obtained from the TRS of the problem
	 * @param dependencyPairs the pairs obtained from the dependency pairs
	 * of the problem
	 * @param usesUsableRules whether {@code trsPairs} is restricted to usable
	 * rules
	 * @param proof the proof to complete if preparation has to be aborted
	 * @param indentation the number of single spaces to print at the beginning
	 * of each line in the specified proof
	 * @return the prepared polynomial interpretation search, or
	 * <code>null</code> if preparation fails
	 */
	private PolynomialInterpretationSearch prepareSearch(
			Collection<PairOfTerms> trsPairs,
			Collection<PairOfTerms> dependencyPairs,
			boolean usesUsableRules,
			Proof proof,
			int indentation) {

		// We reset the ID counter for constant polynomials.
		PolynomialConst.resetIDs();

		// The variable used in [Giesl, RTA'95] for solving
		// polynomial constraints.
		PolynomialConst mu = new PolynomialConst();

		// The polynomial interpretation for the symbols
		// occurring in 'trsPairs' and 'dependencyPairs'.
		PolyInterpretation interpretation = new PolyInterpretation();

		// The intervals of values used for instantiating
		// constant polynomials.
		Intervals intervals = new Intervals();

		// We generate the coefficients and the polynomial
		// constraints associated with 'trsPairs', with no rule
		// variables. Unlike Theorem 1 in [Giesl, RTA'95],
		// we create non-strict constraints, as we use the
		// DP framework (strict constraints are generated
		// only for the dependency pairs, see
		// [Giesl, Thiemann, Schneider-Kamp, LPAR'04]).
		Collection<Constraint> trsConstraints =
				this.buildConstraints(trsPairs, false, intervals, interpretation, mu);

		// If a constraint generated from 'trsPairs' is unsatisfiable,
		// then we stop everything.
		if (trsConstraints == null) return null;

		// We need to record the coefficients associated
		// with the symbols of 'trsPairs'. They will be needed
		// for computing instantiators later.
		Collection<PolynomialConst> trsAndMuCoefficients =
				interpretation.getAllCoefficients();
		trsAndMuCoefficients.add(mu);

		// We generate the coefficients and the polynomial
		// constraints associated with 'dependencyPairs', with no rule
		// variables.
		Collection<Constraint> dependencyPairConstraints =
				this.buildConstraints(dependencyPairs, true, intervals, interpretation, mu);

		// If a constraint generated from 'dependencyPairs' is unsatisfiable,
		// then we stop everything.
		if (dependencyPairConstraints == null) return null;

		if (usesUsableRules)
			addOrdinarySymbolCoefficients(
					interpretation, trsAndMuCoefficients);

		int coefficientCount = interpretation.getNbFunctionCoefficients();
		if (this.maxNbCoef < coefficientCount) {
			// If the problem to solve has to many coefficients,
			// then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex (" + coefficientCount +
					" coefficients to instantiate)! Aborting!", indentation);
			return null;
		}

		// We complete the polynomial constraints associated
		// with 'trsPairs': we add the constraints corresponding
		// to the subterm, monotonicity and constants properties
		// (see Theorem 1 in [Giesl, RTA'95]).
		if (!this.completeConstraints(trsConstraints, intervals, interpretation, mu))
			// If a generated constraint is unsatisfiable,
			// then we stop everything.
			return null;

		// We build instantiators for the coefficients.
		// First, an instantiator for mu and the coefficients
		// associated with the symbols of 'trsPairs'.
		CoefficientInstantiator trsAndMuCoefficientInstantiator =
				new CoefficientInstantiator(trsAndMuCoefficients, intervals,
						(trsAndMuCoefficients.size() <= TRS_COEFFICIENT_THRESHOLD ?
								LARGE_INSTANTIATION_UPPER_BOUND : SMALL_INSTANTIATION_UPPER_BOUND));

		// Then, an instantiator for the coefficients
		// associated with the symbols of 'dependencyPairs'.
		Collection<PolynomialConst> dependencyPairCoefficients =
				interpretation.getAllCoefficients();
		dependencyPairCoefficients.removeAll(trsAndMuCoefficients);
		CoefficientInstantiator dependencyPairCoefficientInstantiator =
				new CoefficientInstantiator(dependencyPairCoefficients, intervals,
						(dependencyPairCoefficients.size() <= DEPENDENCY_PAIR_COEFFICIENT_THRESHOLD ?
								LARGE_INSTANTIATION_UPPER_BOUND : SMALL_INSTANTIATION_UPPER_BOUND));

		return new PolynomialInterpretationSearch(
				trsAndMuCoefficientInstantiator, trsConstraints,
				dependencyPairCoefficientInstantiator, dependencyPairConstraints,
				new PolyOrder(interpretation, mu));
	}

	/**
	 * Adds the coefficients of ordinary symbols occurring only in dependency
	 * pairs to the coefficients instantiated with the usable-rule constraints.
	 *
	 * @param interpretation the polynomial interpretation being prepared
	 * @param trsAndMuCoefficients the coefficients instantiated by the outer
	 * search
	 */
	private static void addOrdinarySymbolCoefficients(
			PolyInterpretation interpretation,
			Collection<PolynomialConst> trsAndMuCoefficients) {

		// Constructors may occur in dependency pairs without occurring in usable
		// rules. Their subterm and monotonicity constraints belong to the outer
		// constraint set, so their coefficients must be instantiated by the
		// corresponding outer instantiator as well.
		Iterator<FunctionSymbol> symbols = interpretation.symbolsIterator();
		while (symbols.hasNext()) {
			FunctionSymbol symbol = symbols.next();
			if (!symbol.isTupleSymbol())
				for (PolynomialConst coefficient : interpretation.get(symbol))
					if (!trsAndMuCoefficients.contains(coefficient))
						trsAndMuCoefficients.add(coefficient);
		}
	}

	/**
	 * Runs this processor on the provided DP problem, which
	 * is supposed to be suitable for this processor.
	 *
	 * @param problem a DP problem to solve using this processor
	 * @param search the prepared polynomial interpretation search
	 * @param budget the usable-rule search budget, or <code>null</code> for an
	 * unbounded full-TRS search
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return the result of this processor
	 */
	private DependencyPairProcessorResult runSuitable(DependencyPairProblem problem,
			PolynomialInterpretationSearch search,
			CoefficientInstantiationBudget budget,
			Proof proof, int indentation) {

		// The best evaluation found so far.
		PolynomialEvaluation bestEvaluation = null;

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();

		// The main loop of the processor.
		while (!currentThread.isInterrupted() &&
				search.trsAndMuCoefficientInstantiator().hasNext() &&
				canInspect(budget)) {
			// Let us consider the next instantiation provided
			// by the outer iterator.
			search.trsAndMuCoefficientInstantiator().next();

			// Let us check whether the non-strict form
			// of each outer constraint is satisfied.
			if (allSatisfiedIfNotStrict(search.trsConstraints())) {
				bestEvaluation = this.evaluateDependencyPairCoefficients(
						problem, search, bestEvaluation, budget,
						proof, indentation);
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
		proof.printlnIfVerbose(bestEvaluation.certificate());
		return bestEvaluation.result();
	}

	/**
	 * Evaluates the dependency-pair coefficient instantiations for the current
	 * instantiation of the TRS and {@code mu} coefficients.
	 *
	 * @param problem the dependency pair problem being solved
	 * @param search the prepared polynomial interpretation search
	 * @param bestEvaluation the best evaluation found previously, or
	 * <code>null</code> if none has been found
	 * @param budget the usable-rule search budget, or <code>null</code> for an
	 * unbounded full-TRS search
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print at the beginning
	 * of each line in the specified proof
	 * @return the best evaluation found so far, or <code>null</code> if no
	 * instantiation yields a result
	 */
	private PolynomialEvaluation evaluateDependencyPairCoefficients(
			DependencyPairProblem problem,
			PolynomialInterpretationSearch search,
			PolynomialEvaluation bestEvaluation,
			CoefficientInstantiationBudget budget,
			Proof proof,
			int indentation) {

		search.dependencyPairCoefficientInstantiator().reset();
		Thread currentThread = Thread.currentThread();
		while (!currentThread.isInterrupted() &&
				search.dependencyPairCoefficientInstantiator().hasNext() &&
				canInspect(budget)) {
			search.dependencyPairCoefficientInstantiator().next();
			DependencyPairProcessorResult bestResult = bestEvaluation == null
					? null : bestEvaluation.result();
			DependencyPairProcessorResult evaluatedResult =
					this.evaluateDependencyPairInstantiation(
							problem, search, bestResult, proof, indentation);
			if (evaluatedResult != null) {
				bestEvaluation = new PolynomialEvaluation(
						evaluatedResult, search.polyOrder().toString(indentation));
				if (evaluatedResult.isFinite()) break;
			}
		}

		return bestEvaluation;
	}

	/**
	 * Evaluates the current dependency-pair coefficient instantiation.
	 *
	 * @param problem the dependency pair problem being solved
	 * @param search the prepared polynomial interpretation search
	 * @param bestResult the best result found by previous instantiations, or
	 * <code>null</code> if none has been found
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print at the beginning
	 * of each line in the specified proof
	 * @return the finite result or best decomposition obtained after evaluating
	 * this instantiation, or <code>null</code> if it yields no result
	 */
	private DependencyPairProcessorResult evaluateDependencyPairInstantiation(
			DependencyPairProblem problem,
			PolynomialInterpretationSearch search,
			DependencyPairProcessorResult bestResult,
			Proof proof,
			int indentation) {

		if (!allSatisfiedIfNotStrict(search.dependencyPairConstraints()))
			return null;

		Set<RuleTrs> nonStrictRules = new HashSet<>();
		for (Constraint constraint : search.dependencyPairConstraints())
			if (constraint.isUnsatisfied(null))
				nonStrictRules.add(constraint.getRule());

		return getResult(problem, search.polyOrder(), nonStrictRules,
				bestResult, proof, indentation);
	}

	/**
	 * The result of evaluating one dependency-pair coefficient instantiation.
	 *
	 * @param result the finite result or best decomposition after evaluation
	 * @param certificate the polynomial-order certificate for this evaluation
	 */
	private record PolynomialEvaluation(
			DependencyPairProcessorResult result, String certificate) {
	}

	/** Mutable coefficient-instantiation budget for a usable-rule attempt. */
	private static final class CoefficientInstantiationBudget {

		/** The remaining number of coefficient instantiations. */
		private int remaining;

		/** Builds a budget with the specified maximum number of instantiations. */
		private CoefficientInstantiationBudget(int maximum) {
			this.remaining = maximum;
		}

		/** Consumes and reports one available instantiation. */
		private boolean tryInspect() {
			if (this.remaining == 0) return false;
			this.remaining--;
			return true;
		}
	}

	/**
	 * The elements prepared for searching for a suitable polynomial
	 * interpretation.
	 *
	 * @param trsAndMuCoefficientInstantiator the instantiator for mu and the
	 * coefficients associated with the TRS
	 * @param trsConstraints the constraints associated with the TRS
	 * @param dependencyPairCoefficientInstantiator the instantiator for the
	 * coefficients associated only with the dependency pairs
	 * @param dependencyPairConstraints the constraints associated with the
	 * dependency pairs
	 * @param polyOrder the polynomial order induced by the interpretation
	 */
	private record PolynomialInterpretationSearch(
			CoefficientInstantiator trsAndMuCoefficientInstantiator,
			Collection<Constraint> trsConstraints,
			CoefficientInstantiator dependencyPairCoefficientInstantiator,
			Collection<Constraint> dependencyPairConstraints,
			PolyOrder polyOrder) {
	}

	/**
	 * Generates the polynomials associated with the symbols
	 * of <code>pairs</code> and inserts them into the provided
	 * interpretation. Also generates and returns the
	 * polynomial constraints associated with <code>pairs</code>
	 * (see Theorem 1 in [Giesl, RTA'95]).
	 * The returned constraints do not contain rule variables
	 * (operations <code>diff1</code> and <code>diff2</code>
	 * of [Giesl, RTA'95] are applied repeatedly).
	 * <p>
	 * If unsatisfiability is detected, then <code>null</code>
	 * is returned.
	 * <p>
	 * If some generated constraints yield minimal or maximal
	 * values for some constant polynomials, then the specified
	 * intervals are completed accordingly.
	 *
	 * @param pairs a collection of pairs of terms
	 * @param strict a boolean indicating whether, before
	 * applying <code>diff1</code> and <code>diff2</code>,
	 * the constraints have to be strict, i.e., of the form
	 * ... &gt; 0
	 * @param intervals intervals of values that have to be
	 * used for instantiating some constant polynomials
	 * @param interpretation a polynomial interpretation for
	 * the symbols occurring in <code>pairs</code>
	 * @param mu the variable used in [Giesl, RTA'95] for solving
	 * polynomial constraints
	 * @return the polynomial constraints associated with
	 * <code>pairs</code>, with no rule variables, or
	 * <code>null</code> if a generated constraint is unsatisfiable
	 */
	private Collection<Constraint> buildConstraints(
			Collection<PairOfTerms> pairs, boolean strict,
			Intervals intervals, PolyInterpretation interpretation,
			PolynomialConst mu) {

		// The collection to return at the end.
		Collection<Constraint> result = new ArrayList<>();

		// For each pair (l,r) in pairs, we create the constraint
		// 0 < poly(l) - poly(r) (if strict = true) or
		// 0 <= poly(l) - poly(r) (if strict = false), where
		// poly(l) and poly(r) are the polynomials associated
		// with l and r respectively. Then, we remove all the
		// rule variables from it.
		for (PairOfTerms pair : pairs) {
			Polynomial differencePolynomial = PolynomialComp.simplified(ArithOperator.MINUS,
					pair.left().toPolynomial(interpretation),
					pair.right().toPolynomial(interpretation));
			List<Constraint> diff = new Constraint(
					differencePolynomial, strict, pair.rule()).diffRepeated(mu, intervals);
			if (diff == null) return null;
			result.addAll(diff);
		}

		return result;
	}

	/**
	 * Completes the specified collection of constraints, i.e.,
	 * adds the constraints corresponding to the subterm,
	 * monotonicity and constants properties (see Theorem 1
	 * in [Giesl, RTA'95]). The added constraints do not
	 * contain rule variables (operations <code>diff1</code>
	 * and <code>diff2</code> of [Giesl, RTA'95] are applied
	 * repeatedly).
	 * <p>
	 * If some generated constraints yield minimal or maximal
	 * values for some constant polynomials, then the specified
	 * intervals are completed accordingly.
	 *
	 * @param constraints a collection of constraints to be
	 * completed
	 * @param intervals intervals of values that have to be
	 * used for instantiating some constant polynomials
	 * @param interpretation a polynomial interpretation
	 * @param mu the variable used in [Giesl, RTA'95] for
	 * solving polynomial constraints
	 * @return <code>false</code> if a generated constraint
	 * has been detected as unsatisfiable
	 */
	private boolean completeConstraints(
			Collection<Constraint> constraints, Intervals intervals,
			PolyInterpretation interpretation, PolynomialConst mu) {

		Iterator<FunctionSymbol> it = interpretation.symbolsIterator();

		while (it.hasNext()) {
			FunctionSymbol f = it.next();

			// We do not consider the tuple symbols.
			if (f.isTupleSymbol()) continue;

			boolean completed = f.getArity() == 0
					? this.addConstantConstraints(
							constraints, intervals, interpretation, mu, f)
					: this.addNonConstantConstraints(
							constraints, intervals, interpretation, mu, f);
			if (!completed) return false;
		}

		return true;
	}

	/**
	 * Adds the constraints associated with a constant symbol.
	 *
	 * @param constraints the collection to complete
	 * @param intervals the intervals completed by generated constraints
	 * @param interpretation the polynomial interpretation containing the symbol
	 * @param mu the variable used for solving polynomial constraints
	 * @param symbol the constant symbol whose constraints have to be added
	 * @return <code>false</code> if the generated constraint is unsatisfiable
	 */
	private boolean addConstantConstraints(
			Collection<Constraint> constraints,
			Intervals intervals,
			PolyInterpretation interpretation,
			PolynomialConst mu,
			FunctionSymbol symbol) {

		// We generate a constraint of the form 0 <= poly(c) - \mu.
		Function constant = new Function(symbol, new ArrayList<>());
		Polynomial differencePolynomial = PolynomialComp.simplified(
				ArithOperator.MINUS, constant.toPolynomial(interpretation), mu);
		List<Constraint> diff = new Constraint(differencePolynomial, false)
				.diffRepeated(mu, intervals);
		if (diff == null) return false;
		constraints.addAll(diff);
		return true;
	}

	/**
	 * Adds the subterm and monotonicity constraints associated with a
	 * non-constant symbol.
	 *
	 * @param constraints the collection to complete
	 * @param intervals the intervals completed by generated constraints
	 * @param interpretation the polynomial interpretation containing the symbol
	 * @param mu the variable used for solving polynomial constraints
	 * @param symbol the non-constant symbol whose constraints have to be added
	 * @return <code>false</code> if a generated constraint is unsatisfiable
	 */
	private boolean addNonConstantConstraints(
			Collection<Constraint> constraints,
			Intervals intervals,
			PolyInterpretation interpretation,
			PolynomialConst mu,
			FunctionSymbol symbol) {

		List<Variable> arguments = new ArrayList<>();
		for (int i = 0; i < symbol.getArity(); i++)
			arguments.add(new Variable());
		Polynomial functionPolynomial =
				new Function(symbol, arguments).toPolynomial(interpretation);

		for (Variable variable : arguments) {
			// Subterm property.
			PolynomialVar variablePolynomial = new PolynomialVar(variable);
			Polynomial differencePolynomial = PolynomialComp.simplified(
					ArithOperator.MINUS, functionPolynomial, variablePolynomial);
			List<Constraint> diff = new Constraint(differencePolynomial, false)
					.diffRepeated(mu, intervals);
			if (diff == null) return false;
			constraints.addAll(diff);

			// Monotonicity.
			diff = new Constraint(functionPolynomial.partialDerivative(variable), false)
					.diffRepeated(mu, intervals);
			if (diff == null) return false;
			constraints.addAll(diff);
		}

		return true;
	}

	/**
	 * Checks whether the provided list of pairs of
	 * terms is not suitable for the polynomial
	 * interpretation technique.
	 *
	 * @param trsPairs a list of pairs of terms
	 * @return <code>true</code> iff the provided list
	 * is not suitable for the polynomial interpretation
	 * technique
	 */
	private boolean isNotSuitable(Collection<PairOfTerms> trsPairs) {

		// We compute the depth of 'trsPairs', i.e., the
		// maximal depth of the pairs of 'trsPairs'. We
		// also compute the maximum arity of a
		// function symbol in 'trsPairs'.
		int observedMaxDepth = -1;
		int maxArity = -1;
		for (PairOfTerms pair : trsPairs) {
			Term left = pair.left();
			Term right = pair.right();
			int depth = Math.max(left.depth(), right.depth());
			int arity = Math.max(left.maxArity(), right.maxArity());
			if (depth > observedMaxDepth) observedMaxDepth = depth;
			if (arity > maxArity) maxArity = arity;
		}

		return (this.maxDepth < observedMaxDepth || MAX_ARITY < maxArity);
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		return "## DP Processor: polynomial interpretations. ";
	}

	/**
	 * Checks whether the non-strict form of each
	 * constraint in the specified collection is
	 * satisfied.
	 *
	 * @param constraints a collection of constraints
	 * @return <code>true</code> iff the non-strict
	 * form of each constraint is satisfied
	 */
	private static boolean allSatisfiedIfNotStrict(Collection<Constraint> constraints) {

		for (Constraint c : constraints)
			if (!c.isTrueIfNotStrict(null)) return false;

		return true;
	}

	/** Consumes one bounded instantiation, or accepts an unbounded search. */
	private static boolean canInspect(CoefficientInstantiationBudget budget) {
		return budget == null || budget.tryInspect();
	}

}
