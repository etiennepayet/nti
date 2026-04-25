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

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.DpProblem;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;

/**
 * A dependency pair (DP) processor.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class Processor {

	/**
	 * The maximum number of filter instantiation
	 * possibilities. If the number instantiation
	 * possibilities is greater than this bound,
	 * then the termination proof is aborted.
	 */
	private final static int NB_FILTERS = 5000;
	
	
	/**
	 * <code>true</code> iff this processor uses
	 * argument filtering.
	 */
	private final boolean usesFiltering;

	/**
	 * Builds a DP pair processor.
	 * 
	 * @param usesFiltering <code>true</code> iff
	 * this processor uses argument filtering
	 */
	public Processor(boolean usesFiltering) {
		this.usesFiltering = usesFiltering;
	}

	/**
	 * Runs this processor on the provided DP problem,
	 * possibly using the provided argument filtering.
	 * 
	 * The provided argument filtering is used iff this
	 * processor has been built with <code>true</code>
	 * as parameter of the constructor.
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
	public abstract ResultDp run(DpProblem prob,
			ArgFiltering filtering, int indentation);
	
	/**
	 * Returns <code>true</code> iff this processor
	 * uses argument filtering
	 * 
	 * @return <code>true</code> iff this processor
	 * uses argument filtering
	 */
	public boolean usesFiltering() {
		return this.usesFiltering;
	}

	/**
	 * Returns a copy of this processor.
	 * 
	 * @return a copy of this processor
	 */
	public Processor copy() {
		// By default, we return this processor.
		return this;
	}

	/**
	 * Checks whether the provided filter instantiator
	 * is suitable for this processor.
	 *  
	 * @param it a filter instantiator
	 * @return <code>true</code> iff the specified
	 * instantiator is suitable for this processor
	 * @throws NullPointerException if the provided
	 * instantiator is <code>null</code>
	 */
	protected boolean isSuitable(FilterInstantiator it) {
		return it.getNbInstantiationPossibilities() <= NB_FILTERS;
	}

	/**
	 * Prints the provided <code>filtering</code> on the 
	 * provided <code>proof</code> using the provided
	 * <code>indentation</code>.
	 * 
	 * For internal use only.
	 * 
	 * @param filtering an argument filtering to print
	 * @param proof the proof to build 
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 */
	protected void printFiltering(ArgFiltering filtering, Proof proof, int indentation) {

		String s = (filtering == null ?
				"Using no argument filtering, i.e., applying the processor to the full problem only." :
					"Using argument filtering: " + filtering + ".");

		proof.printlnIfVerbose(s, indentation);
	}
}
