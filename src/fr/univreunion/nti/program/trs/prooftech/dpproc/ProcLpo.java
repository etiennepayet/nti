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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.DpProblem;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.reducpair.Lpo;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A sound DP processor for proving that a provided
 * DP problem is finite using lexicographic path
 * orders.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ProcLpo extends ProcForFiniteness {

	/**
	 * Builds a DP processor for proving finiteness
	 * of DP problems using lexicographic path orders.
	 * 
	 * @param usesFiltering <code>true</code> iff
	 * this processor uses argument filtering
	 */
	public ProcLpo(boolean usesFiltering) {
		super(usesFiltering);
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

		int nbSymbols = this.nbFunSymbols(L_IR, L_DP);
		if (20 < nbSymbols) {
			// If, from the data collected so far, we infer that the problem
			// is not suitable for the lexicographic path order technique,
			// then we stop everything.
			proof.printlnIfVerbose("This DP problem is too complex (" +
					nbSymbols +
					" symbols to deal with)! Aborting!", indentation);
			return ResultDp.getFailedInstance(proof);
		}

		// The result that will be returned at the end.
		ResultDp result = null;
		// A message that goes with the result;
		String msg = null;

		// We try to infer a lexicographic path order
		// satisfying the constraints over the specified
		// DP problem.
		Lpo lpo = new Lpo();

		if (lpo.complete(L_IR) && lpo.complete(L_DP)) {
			
			// Here, we are sure that for each dependency pair
			// l -> r we have l >= r where >= is the current LPO.
			// Let us collect the dependency pairs l -> r such
			// that l > r does not hold.
			List<RuleTrs> nonstrict = new LinkedList<RuleTrs>();
			for (PairOfTerms pair : L_DP)
				if (pair.getLeft().deepEquals(pair.getRight()))
					nonstrict.add(pair.getRule());

			// Here, for each l -> r in 'nonstrict', we have
			// l = r w.r.t. the current LPO.

			if ((result = getResult(prob, lpo,
					nonstrict, result, proof, indentation)) != null) {

				if (result.isFinite()) return result;

				// Here, result is necessarily decomposed (method 
				// 'getResult' returns either null, or a finite
				// result or a decomposed result).
				msg = lpo.toString(indentation);
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
	 * Computes the total number of function symbols
	 * occurring in the provided collections.
	 * 
	 * @param L_IR the result of applying an argument
	 * filtering to the TRS of the problem to solve
	 * @param L_DP the result of applying an argument
	 * filtering to the dependency pairs of the problem
	 * to solve
	 * @return the total number of function symbols
	 * occurring in the provided collections
	 */
	private int nbFunSymbols(
			Collection<PairOfTerms> L_IR,
			Collection<PairOfTerms> L_DP) {

		// We build the set of function symbols occurring
		// in L_IR and L_DP.
		HashSet<FunctionSymbol> symbols = new HashSet<FunctionSymbol>();

		for (PairOfTerms pair : L_IR) {
			symbols.addAll(pair.getLeft().getFunSymbols());
			symbols.addAll(pair.getRight().getFunSymbols());
		}

		for (PairOfTerms pair : L_DP) {
			symbols.addAll(pair.getLeft().getFunSymbols());
			symbols.addAll(pair.getRight().getFunSymbols());
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
