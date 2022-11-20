/*
 * Copyright 2022 Etienne Payet <etienne.payet at univ-reunion.fr>
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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

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
import fr.univreunion.nti.program.trs.reducpair.Kbo;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A sound DP processor for proving that a provided
 * DP problem is finite using Knuth-Bendix orders.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ProcKbo extends ProcForFiniteness {

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
	 * The maximum number of weights that this processor
	 * is able to instantiate. If the number of weights
	 * associated with the TRS under analysis is greater
	 * than this bound, then the termination proof is
	 * aborted.
	 */
	private final int maxNbWeights;

	/**
	 * Builds a DP processor for proving finiteness
	 * of DP problems using Knuth-Bendix orders.
	 * 
	 * @param usesFiltering <code>true</code> iff
	 * this processor uses argument filtering
	 * @param maxNbWeights the maximum number of weights
	 * that this processor is able to instantiate
	 */
	public ProcKbo(boolean usesFiltering, int maxNbWeights) {
		super(usesFiltering);

		this.maxNbWeights = maxNbWeights;
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

		// We reset the ID counter for constant polynomials.
		PolynomialConst.resetIDs();

		// The weights of the symbols occurring in 'L_IR' and 'L_DP'.
		WeightFunction wf = new WeightFunction();

		// The intervals of values used for instantiating
		// constant polynomials.
		Intervals intervals = new Intervals();

		// We generate the weights and constraints associated
		// with 'L_IR'. The constraints ensure that the weight
		// function is admissible (see p. 124 of
		// [Baader & Nipkow, 1998]).
		Collection<Constraint> constraintsIR = this.buildConstraints(L_IR, intervals, wf);

		// If a constraint generated from 'L_IR' is unsatisfiable,
		// then we stop everything.
		if (constraintsIR == null)
			return ResultDp.getFailedInstance(proof);

		// The weight associated with all the variables
		// must not be zero.
		constraintsIR.add(new Constraint(wf.getVariableWeight(), true));

		// We need to record the weights associated with
		// the variables and the weights associated with
		// the symbols of 'L_IR'. They will be needed for
		// computing instantiators later. 
		Collection<PolynomialConst> weightsIRAndVar = wf.getAllCoefficients();
		weightsIRAndVar.add(wf.getVariableWeight());

		// We generate the weights and constraints associated
		// with 'L_DP'. The constraints ensure that the weight
		// function is admissible (see p. 124 of
		// [Baader & Nipkow, 1998]).
		Collection<Constraint> constraintsDP = this.buildConstraints(L_DP, intervals, wf);

		// If a constraint generated from 'L_DP' is unsatisfiable,
		// then we stop everything.
		if (constraintsDP == null)
			return ResultDp.getFailedInstance(proof);

		int nbWeights = wf.getNbFunctionCoefficients();
		if (this.maxNbWeights < nbWeights) {
			// If the problem to solve has to many weights,
			// then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex (" + nbWeights +
					" weights to instantiate)! Aborting!", indentation);
			return ResultDp.getFailedInstance(proof);
		}

		// We build instantiators for the weights.
		// First, an instantiator for the weight associated with
		// the variables and the weights associated with the
		// symbols of 'L_IR'.
		CoefficientInstantiator itIRAndVar =
				new CoefficientInstantiator(weightsIRAndVar, intervals,
						(weightsIRAndVar.size() <= THRESHOLD_IR ?
								UPPER_MAX : UPPER_MIN));
		// Then, an instantiator for the weights associated with
		// the symbols of 'L_DP'.
		Collection<PolynomialConst> weightsDP = wf.getAllCoefficients();
		weightsDP.removeAll(weightsIRAndVar);
		CoefficientInstantiator itDP =
				new CoefficientInstantiator(weightsDP, intervals,
						(weightsDP.size() <= THRESHOLD_DP ?
								UPPER_MAX : UPPER_MIN));
		// We garbage-collect weightsIRAndVar and weightsDP.
		weightsIRAndVar = null;
		weightsDP = null;

		return this.runSuitable(prob,
				L_IR, L_DP,
				constraintsIR, constraintsDP,
				itIRAndVar, itDP,
				wf, proof, indentation);
	}

	/**
	 * Runs this processor on the provided DP problem, which
	 * is supposed to be suitable for this processor.
	 * 
	 * @param prob a DP problem to solve using this processor
	 * @param L_IR the result of applying <code>filtering</code>
	 * to the TRS of <code>prob</code>
	 * @param L_DP the result of applying <code>filtering</code>
	 * to the dependency pairs of <code>prob</code>
	 * @param constraintsIR the polynomial constraints
	 * associated with <code>L_IR</code> 
	 * @param constraintsDP the polynomial constraints
	 * associated with <code>L_DP</code>
	 * @param itIRAndVar an instantiator for the weight
	 * associated with the variables and the weights
	 * associated with the symbols of <code>L_IR</code> 
	 * @param itDP an instantiator for the weights associated
	 * with the symbols of <code>L_DP</code>
	 * @param wf the weight function associated with
	 * the symbols occurring in <code>L_IR</code> and
	 * <code>L_DP</code>
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return the <code>Result</code> of this processor
	 */
	private ResultDp runSuitable(DpProblem prob,
			Collection<PairOfTerms> L_IR, Collection<PairOfTerms> L_DP,
			Collection<Constraint> constraintsIR, Collection<Constraint> constraintsDP,
			CoefficientInstantiator itIRAndVar, CoefficientInstantiator itDP,
			WeightFunction wf, Proof proof, int indentation) {

		// The result that will be returned at the end.
		ResultDp result = null;
		// A message that goes with the result;
		String msg = null;

		// We try to infer a suitable Knuth-Bendix order
		// based on the weight function.
		Kbo kbo = new Kbo(wf);

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();

		// The main loop of the processor.
		while (!currentThread.isInterrupted() && itIRAndVar.hasNext()) {
			// Let us consider the next instantiation of
			// the weight associated with the variables
			// and the weights associated with the symbols
			// of 'L_IR'.
			itIRAndVar.next();

			kbo.clear();

			// Let us check whether the constraints associated with
			// 'L_IR' are satisfied by the current instantiation.
			// Let us also try to complete 'kbo'.
			if (allSatisfied(constraintsIR) && kbo.complete(L_IR)) {
				itDP.reset();
				while (!currentThread.isInterrupted() && itDP.hasNext()) {
					// Let us consider the next instantiation of the
					// weights associated with the symbols of the
					// dependency pairs.
					itDP.next();

					// We work on a copy of 'kbo', so that 'kbo'
					// remains unchanged in case the current weights
					// do not solve anything and the next instantiation
					// has to be considered.
					Kbo kboCopy = new Kbo(kbo);

					// Let us check whether the constraints associated with
					// 'L_DP' are satisfied by the current instantiation.
					// Let us also try to complete 'kbo'.
					// We require that the weight function is admissible
					// for the partial order.
					if (allSatisfied(constraintsDP) &&
							kboCopy.complete(L_DP) &&
							kboCopy.completeAdmissible2()) {

						// Here, we are sure that for each dependency pair
						// l -> r we have l >= r where >= is the current KBO.
						// Let us collect the dependency pairs l -> r such
						// that l > r does not hold.
						List<RuleTrs> nonstrict = new LinkedList<RuleTrs>();
						for (PairOfTerms pair : L_DP)
							if (pair.getLeft().deepEquals(pair.getRight()))
								nonstrict.add(pair.getRule());

						// Here, for each l -> r in 'nonstrict', we have
						// l = r w.r.t. the current KBO.

						if ((result = getResult(prob, kboCopy,
								nonstrict, result, proof, indentation)) != null) {

							if (result.isFinite()) return result;

							// Here, result is necessarily decomposed (method 
							// 'getResult' returns either null, or a finite
							// result or a decomposed result).
							msg = kboCopy.toString(indentation);
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
	 * Generates the weights associated with the symbols of
	 * <code>L</code> and inserts them into the provided
	 * weight function. Also generates and returns the
	 * polynomial constraints ensuring that the provided
	 * weight function is admissible (see p. 124 of
	 * Baader & Nipkow 'Term Rewriting and All That', 2000).
	 *
	 * If unsatisfiability is detected, then <code>null</code>
	 * is returned.
	 * 
	 * If some generated constraints yield minimal or maximal
	 * values for some constant polynomials, then the specified
	 * intervals are completed accordingly.
	 * 
	 * @param L a collection of pairs of terms
	 * @param intervals intervals of values that have to be
	 * used for instantiating some constant polynomials
	 * @param wf the weight function to fill with the
	 * generated weights
	 * @return the constraints ensuring that the provided weight
	 * function is admissible, or <code>null</code> if a generated
	 * constraint is unsatisfiable
	 */
	private Collection<Constraint> buildConstraints(
			Collection<PairOfTerms> L, Intervals intervals, WeightFunction wf) {

		// The collection to return at the end.
		Collection<Constraint> constraints = new LinkedList<Constraint>();

		// First, we generate the weight of each function symbol.
		for (PairOfTerms pair : L) {
			pair.getLeft().generateKBOWeights(wf);
			pair.getRight().generateKBOWeights(wf);
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
				Polynomial P = PolynomialComp.getInstance(ArithOperator.MINUS,
						wf.get(f)[0],
						w);
				// We try to update the previously generated collection
				// of constraints and the intervals using c.
				// If unsatisfiability is detected, then we stop everything
				// and return null.
				if (!(new Constraint(P, false)).update(constraints, intervals))
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
			if (!c.isTrue(null)) return false;

		return true;
	}
}
