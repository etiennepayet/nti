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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech.dpproc;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.DpProblem;
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
 * A sound DP processor for proving that a provided
 * DP problem is finite. It consists in searching
 * for a suitable polynomial interpretation of the
 * function and tuple symbols.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ProcPolyInterpretation extends ProcForFiniteness {

	/**
	 * A threshold for choosing the right interval of values
	 * for instantiating the coefficients associated with the
	 * TRS of the problem to solve.
	 */
	private final static int THRESHOLD_IR = 14;

	/**
	 * A threshold for choosing the right interval of values
	 * for instantiating the coefficients associated with the
	 * dependency pairs of the problem to solve.
	 */
	private final static int THRESHOLD_DP = 4;

	/**
	 * The upper limit of the interval of values
	 * used for instantiating the coefficients.
	 * This constant is used if the number of
	 * coefficients to instantiate does not exceed
	 * the threshold.
	 */
	private final static int UPPER_MAX = 2;

	/**
	 * The upper limit of the interval of values
	 * used for instantiating the coefficients.
	 * This constant is used if the number of
	 * coefficients to instantiate exceeds the
	 * threshold.
	 */
	private final static int UPPER_MIN = 1;

	// UPPER = 1 works for the vast majority of the
	// competition's benchmarks and it speeds up the
	// analysis. But, unfortunately, UPPER = 2 is
	// needed for solving some few competition's
	// benchmarks (e.g., Applicative_05/ReverseLastInit.xml).

	/**
	 * The maximum depth allowed for a TRS rule. Deep terms
	 * yield very intricate constraints which are difficult
	 * to solve.
	 */
	// private final static int MAX_DEPTH = 5;

	/**
	 * The maximum arity allowed for a symbol. Deep terms
	 * yield very intricate constraints which are difficult
	 * to solve.
	 */
	private final static int MAX_ARITY = 6;


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
	 * Builds a DP processor for proving finiteness of
	 * DP problems using polynomial interpretations.
	 * 
	 * @param usesFiltering <code>true</code> iff this
	 * processor uses argument filtering
	 * @param maxNbCoef the maximum number of coefficients
	 * that this processor is able to instantiate
	 * @param maxDepth the maximum depth allowed for a
	 * TRS rule
	 */
	public ProcPolyInterpretation(boolean usesFiltering,
			int maxNbCoef, int maxDepth) {

		super(usesFiltering);

		this.maxNbCoef = maxNbCoef;
		this.maxDepth = maxDepth;
	}

	/**
	 * Runs this processor on the provided collections
	 * <code>L_IR</code> and <code>L_DP</code> that result
	 * from applying the provided argument filtering
	 * <code>filtering</code> respectively to the TRS and
	 * to the dependency pairs of the provided DP problem
	 * <code>prob</code>.
	 * 
	 * The returned result indicates whether the provided
	 * problem could be proved finite or could be decomposed
	 * into a collection of subproblems.
	 * 
	 * @param prob a DP problem to solve using this processor
	 * @param filtering an argument filtering for solving
	 * <code>prob</code> (<code>null</code> if only the
	 * full problem has to be considered)
	 * @param L_IR the result of applying <code>filtering</code>
	 * to the TRS of <code>prob</code>
	 * @param L_DP the result of applying <code>filtering</code>
	 * to the dependency pairs of <code>prob</code>
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return the <code>Result</code> of this processor
	 */
	@Override
	protected ResultDp run(DpProblem prob, ArgFiltering filtering, 
			Collection<PairOfTerms> L_IR, Collection<PairOfTerms> L_DP,
			int indentation) {

		// The proof of the returned result.
		Proof proof = new Proof();

		// We indicate which argument filtering is used. 
		this.printFiltering(filtering, proof, indentation);

		if (this.isNotSuitable(L_IR)) {
			// If 'L_IR' is not suitable for the polynomial
			// interpretation technique, then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex! Aborting!", indentation);
			return ResultDp.getFailedInstance(proof);
		}

		// We reset the ID counter for constant polynomials.
		PolynomialConst.resetIDs();

		// The variable used in [Giesl, RTA'95] for solving
		// polynomial constraints.
		PolynomialConst mu = new PolynomialConst();

		// The polynomial interpretation for the symbols
		// occurring in 'L_IR' and 'L_DP'.
		PolyInterpretation interpretation = new PolyInterpretation();

		// The intervals of values used for instantiating
		// constant polynomials.
		Intervals intervals = new Intervals();

		// We generate the coefficients and the polynomial
		// constraints associated with 'L_IR', with no rule
		// variables. Unlike Theorem 1 in [Giesl, RTA'95],
		// we create non-strict constraints, as we use the
		// DP framework (strict constraints are generated
		// only for the dependency pairs, see
		// [Giesl, Thiemann, Schneider-Kamp, LPAR'04]).
		Collection<Constraint> constraintsIR =
				this.buildConstraints(L_IR, false, intervals, interpretation, mu);

		// If a constraint generated from 'L_IR' is unsatisfiable,
		// then we stop everything.
		if (constraintsIR == null)
			return ResultDp.getFailedInstance(proof);

		// We need to record the coefficients associated
		// with the symbols of 'L_IR'. They will be needed
		// for computing instantiators later. 
		Collection<PolynomialConst> coefficientsIRAndMu =
				interpretation.getAllCoefficients();
		coefficientsIRAndMu.add(mu);

		// We generate the coefficients and the polynomial
		// constraints associated with 'L_DP', with no rule
		// variables.
		Collection<Constraint> constraintsDP =
				this.buildConstraints(L_DP, true, intervals, interpretation, mu);

		// If a constraint generated from 'L_DP' is unsatisfiable,
		// then we stop everything.
		if (constraintsDP == null)
			return ResultDp.getFailedInstance(proof);

		int nbCoef = interpretation.getNbFunctionCoefficients();
		if (this.maxNbCoef < nbCoef) {
			// If the problem to solve has to many coefficients,
			// then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex (" + nbCoef +
					" coefficients to instantiate)! Aborting!", indentation);
			return ResultDp.getFailedInstance(proof);
		}

		// We complete the polynomial constraints associated
		// with 'L_IR': we add the constraints corresponding
		// to the subterm, monotonicity and constants properties
		// (see Theorem 1 in [Giesl, RTA'95]).
		if (!this.completeConstraints(constraintsIR, intervals, interpretation, mu))
			// If a generated constraint is unsatisfiable,
			// then we stop everything.
			return ResultDp.getFailedInstance(proof);

		// We build instantiators for the coefficients.
		// First, an instantiator for mu and the coefficients
		// associated with the symbols of 'L_IR'.
		CoefficientInstantiator itIRAndMu =
				new CoefficientInstantiator(coefficientsIRAndMu, intervals, 
						(coefficientsIRAndMu.size() <= THRESHOLD_IR ?
								UPPER_MAX : UPPER_MIN));

		// Then, an instantiator for the coefficients
		// associated with the symbols of 'L_DP'.
		Collection<PolynomialConst> coefficientsDP =
				interpretation.getAllCoefficients();
		coefficientsDP.removeAll(coefficientsIRAndMu);
		CoefficientInstantiator itDP =
				new CoefficientInstantiator(coefficientsDP, intervals,
						(coefficientsDP.size() <= THRESHOLD_DP ?
								UPPER_MAX : UPPER_MIN));

		// We garbage-collect coefficientsIRAndMu and coefficientsDP.
		coefficientsIRAndMu = null;
		coefficientsDP = null;

		return this.runSuitable(prob,
				itIRAndMu, constraintsIR,
				itDP, constraintsDP,
				new PolyOrder(interpretation, mu),
				proof, indentation);
	}

	/**
	 * Runs this processor on the provided DP problem, which
	 * is supposed to be suitable for this processor.
	 * 
	 * @param prob a DP problem to solve using this processor
	 * @param itIRAndMu an instantiator for mu and for the
	 * coefficients associated with the TRS of
	 * <code>prob</code> 
	 * @param constraintsIR the polynomial constraints
	 * associated with the TRS of <code>prob</code>
	 * @param itDP an instantiator for the coefficients
	 * associated with the dependency pairs of
	 * <code>prob</code>
	 * @param constraintsDP the polynomial constraints
	 * associated with the dependency pairs of
	 * <code>prob</code>
	 * @param polyOrder a polynomial order
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return the <code>Result</code> of this processor
	 */
	private ResultDp runSuitable(DpProblem prob,
			CoefficientInstantiator itIRAndMu,
			Collection<Constraint> constraintsIR,
			CoefficientInstantiator itDP,
			Collection<Constraint> constraintsDP,
			PolyOrder polyOrder,
			Proof proof, int indentation) {

		// The result that will be returned at the end.
		ResultDp result = null;
		// A message that goes with the result;
		String msg = null;

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();

		// The main loop of the processor.
		while (!currentThread.isInterrupted() && itIRAndMu.hasNext()) {
			// Let us consider the next instantiation provided
			// by the outer iterator.
			itIRAndMu.next();

			// Let us check whether the non-strict form
			// of each outer constraint is satisfied.
			if (allSatisfiedIfNotStrict(constraintsIR)) {
				itDP.reset();
				while (!currentThread.isInterrupted() && itDP.hasNext()) {
					// Let us consider the next instantiation provided
					// by the inner iterator.
					itDP.next();

					// Let us check whether the non-strict form
					// of each inner constraint is satisfied.
					if (allSatisfiedIfNotStrict(constraintsDP)) {
						// Let us collect the dependency pairs l -> r
						// whose corresponding strict constraint is
						// not satisfied.
						Set<RuleTrs> nonstrict = new HashSet<RuleTrs>();
						for (Constraint c : constraintsDP)
							if (!c.isTrue(null)) nonstrict.add(c.getRule());

						if ((result = getResult(prob, polyOrder,
								nonstrict, result, proof, indentation)) != null) {

							if (result.isFinite()) return result;

							// Here, 'result' is necessarily decomposed
							// (method 'getResult' returns either null,
							// or a finite result or a decomposed result).
							msg = polyOrder.toString(indentation);
						}
					}
				}
			}

		}

		// Here, 'prob' could not be proved finite.
		// Either the proof has failed or 'prob' has
		// been decomposed into more than one smaller
		// problems.

		if (result == null)
			// Here, the proof has failed.
			result = ResultDp.getFailedInstance(proof);
		else
			// Here, the problem has been decomposed.
			proof.printlnIfVerbose(msg);

		return result;
	}

	/**
	 * Generates the polynomials associated with the symbols
	 * of <code>L</code> and inserts them into the provided
	 * interpretation. Also generates and returns the
	 * polynomial constraints associated with <code>L</code>
	 * (see Theorem 1 in [Giesl, RTA'95]).
	 * The returned constraints do not contain rule variables
	 * (operations <code>diff1</code> and <code>diff2</code>
	 * of [Giesl, RTA'95] are applied repeatedly).
	 * 
	 * If unsatisfiability is detected, then <code>null</code>
	 * is returned.
	 * 
	 * If some generated constraints yield minimal or maximal
	 * values for some constant polynomials, then the specified
	 * intervals are completed accordingly.
	 * 
	 * @param L a collection of pairs of terms
	 * @param strict a boolean indicating whether, before
	 * applying <code>diff1</code> and <code>diff2</code>,
	 * the constraints have to be strict, i.e., of the form
	 * ... &gt; 0
	 * @param intervals intervals of values that have to be
	 * used for instantiating some constant polynomials
	 * @param interpretation a polynomial interpretation for
	 * the symbols occurring in <code>L</code>
	 * @param mu the variable used in [Giesl, RTA'95] for solving
	 * polynomial constraints
	 * @return the polynomial constraints associated with
	 * <code>L</code>, with no rule variables, or
	 * <code>null</code> if a generated constraint is unsatisfiable
	 */
	private Collection<Constraint> buildConstraints(
			Collection<PairOfTerms> L, boolean strict,
			Intervals intervals, PolyInterpretation interpretation,
			PolynomialConst mu) {

		// The collection to return at the end.
		Collection<Constraint> result = new LinkedList<Constraint>();

		// For each pair (l,r) in L, we create the constraint
		// 0 < poly(l) - poly(r) (if strict = true) or
		// 0 <= poly(l) - poly(r) (if strict = false), where
		// poly(l) and poly(r) are the polynomials associated
		// with l and r respectively. Then, we remove all the
		// rule variables from it. 
		for (PairOfTerms pair : L) {
			Polynomial P = PolynomialComp.getInstance(ArithOperator.MINUS,
					pair.getLeft().toPolynomial(interpretation),
					pair.getRight().toPolynomial(interpretation));
			List<Constraint> diff = new Constraint(P, strict, pair.getRule()).
					diffRepeated(mu, intervals);
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
	 * 
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

			if (f.getArity() == 0) {
				// f is a constant: we generate a constraint
				// of the form 0 <= poly(c) - \mu.
				Function c = new Function(f, new LinkedList<Term>());
				Polynomial P = PolynomialComp.getInstance(ArithOperator.MINUS,
						c.toPolynomial(interpretation), mu);
				List<Constraint> diff = new Constraint(P, false).diffRepeated(mu, intervals);
				if (diff == null) return false;
				constraints.addAll(diff);
			}
			else {
				// Subterm property + monotonicity.
				List<Variable> Args = new LinkedList<Variable>();
				for (int i = 0; i < f.getArity(); i++)
					Args.add(new Variable());
				Polynomial P_f = new Function(f, Args).toPolynomial(interpretation);
				for (Variable V : Args) {
					// Subterm property.
					PolynomialVar P_V = new PolynomialVar(V);
					Polynomial P = PolynomialComp.getInstance(ArithOperator.MINUS, P_f, P_V);
					List<Constraint> diff = new Constraint(P, false).diffRepeated(mu, intervals);
					if (diff == null) return false;
					constraints.addAll(diff);
					// Monotonicity.
					diff = new Constraint(P_f.partialDerivative(V), false).diffRepeated(mu, intervals);
					if (diff == null) return false;
					constraints.addAll(diff);
				}
			}
		}

		return true;
	}

	/**
	 * Checks whether the provided list of pairs of
	 * terms is not suitable for the polynomial
	 * interpretation technique.
	 * 
	 * @param L_IR a list of pairs of terms
	 * @return <code>true</code> iff the provided list
	 * is not suitable for the polynomial interpretation
	 * technique
	 */
	private boolean isNotSuitable(Collection<PairOfTerms> L_IR) {

		// We compute the depth of 'L_IR', i.e., the
		// maximal depth of the pairs of 'L_IR'. We 
		// also compute the maximum arity of a
		// function symbol in 'L_IR'.
		int maxDepth = -1, maxArity = -1;
		for (PairOfTerms pair : L_IR) {
			Term left = pair.getLeft(), right = pair.getRight();
			int depth = Math.max(left.depth(), right.depth());
			int arity = Math.max(left.maxArity(), right.maxArity());
			if (depth > maxDepth) maxDepth = depth;
			if (arity > maxArity) maxArity = arity;
		}

		return (this.maxDepth < maxDepth || MAX_ARITY < maxArity);
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

	/**
	 * Applies the DP processor based on rule removal
	 * (Theorem 30 of [Giesl, Thiemann, Schneider-Kamp,
	 * LPAR'04]). This processor removes rules from
	 * the specified TRS if the specified polynomial
	 * interpretation <code>coefficients</code> is
	 * strictly monotonic.
	 * 
	 * @param IR the TRS from which rules have to be removed
	 * @param coefficients the coefficients of the polynomials
	 * associated with the function and tuple symbols
	 * @param mu the variable used in [Giesl, RTA'95] for solving
	 * polynomial constraints
	 * @return the specified TRS if the specified polynomial
	 * interpretation is not monotonic, otherwise the TRS
	 * obtained from removing the strictly decreasing rules
	 * from the specified TRS
	 */
	/*
	private TRS removeRules(TRS IR,
			Coefficients coefficients, Polynomial_Const mu) {

		// The value to return at the end.
		TRS simplifiedTRS = IR;

		if (coefficients.isMonotone()) {
			// We compute the strict constraints associated
			// with the specified TRS.
			Collection<Constraint> constraints =
					this.simplifiedStrictPolyConstraints(IR.iterator(), coefficients, mu);
			// We collect the strict constraints which are
			// not satisfied by the current instantiation
			// of the coefficients.
			Collection<RuleTRS> unsatisfied = new HashSet<RuleTRS>();
			for (Constraint c : constraints)
				if (!c.isTrue(null))
					unsatisfied.add(c.getRule());
			// If there exist some constraints that are satisfied
			// by the current instantiation, then we remove the
			// corresponding rules from the TRS.
			if (unsatisfied.size() < IR.size()) {
				simplifiedTRS = TRS.getInstance(
						IR.getName(),
						(ParametersTRS) IR.getParameters(),
						unsatisfied,
						IR.getStrategy());
			}
		}

		return simplifiedTRS;
	}
	 */

	/**
	 * Converts the specified set of rules (dependency pairs)
	 * to dependency pairs of the specified TRS.
	 * 
	 * @param IR a TRS
	 * @param unsatisfied a set of rules to convert 
	 * @return the resulting set of converted rules
	 */
	/*
	private Set<RuleTRS> convert(TRS IR, Set<RuleTRS> unsatisfied) {
		// The set to return at the end.
		Set<RuleTRS> convertedUnsatisfied = new HashSet<RuleTRS>();

		DPairs dpairs = IR.dependencyPairs();
		for (RuleTRS R : unsatisfied)
			for (RuleTRS pair : dpairs) {
				Term l1 = R.getLeft(), r1 = R.getRight();
				Term l2 = pair.getLeft(), r2 = pair.getRight();

				if (l1.deepEquals(l2) && r1.deepEquals(r2)) {
					convertedUnsatisfied.add(pair);
					break;
				}
			}

		return convertedUnsatisfied;
	}
	 */
}
