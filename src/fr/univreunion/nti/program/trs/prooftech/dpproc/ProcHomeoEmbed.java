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


import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.DpProblem;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;
import fr.univreunion.nti.term.Term;

/**
 * A sound DP processor for proving that a provided
 * DP problem is finite using homeomorphic embeddings.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ProcHomeoEmbed extends Processor {

	/**
	 * Builds a DP processor for proving finiteness
	 * of DP problems using homeomorphic embeddings.
	 * 
	 * Argument filterings are not used by this
	 * processor.
	 */
	public ProcHomeoEmbed() {
		super(false);
	}

	/**
	 * Runs this processor on the provided DP problem
	 * without using the provided argument filtering.
	 * 
	 * The returned result indicates whether the provided
	 * DP problem could be proved finite or infinite or
	 * whether it could be decomposed into a collection
	 * of subproblems.
	 * 
	 * @param prob a DP problem to solve using this processor
	 * @param filtering an argument filtering for solving
	 * <code>prob</code>
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return the <code>Result</code> of this processor
	 */
	@Override
	public ResultDp run(DpProblem prob,
			ArgFiltering filtering, int indentation) {

		// The proof of the returned result.
		Proof proof = new Proof();
				
		// We indicate which argument filtering is used. 
		this.printFiltering(filtering, proof, indentation);

		// We check whether the set of dependency pairs of 'prob'
		// only consists of pairs l -> r where l embeds r.
		for (RuleTrs R : prob.getDependencyPairs()) {
			Term left = R.getLeft(), right = R.getRight(); 
			if (left.deepEquals(right) || !left.embeds(right))
				return ResultDp.getFailedInstance(proof);
		}

		// Here, every dependency pair has the form l -> r
		// where l embeds r.
		return ResultDp.getFiniteInstance(proof);
	}

	/**
	 * Checks whether the provided filter instantiator
	 * is suitable for this processor.
	 * 
	 * For internal use only.
	 * 
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
		return "## DP Processor: homeomorphic embeddings. ";
	}
}
