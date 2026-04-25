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

package fr.univreunion.nti.program.lp;

import fr.univreunion.nti.program.Proof;

/**
 * A result provided by a termination prover for logic programs.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ResultLp {

	/**
	 * A value indicating whether termination or
	 * non-termination of all the specified modes
	 * could be proved.
	 * 
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	private enum ResultType {
		YES,
		NO,
		MAYBE,
		ERROR
	}
	
	/**
	 * Returns a result indicating that all the specified
	 * modes could be proved terminating.
	 * 
	 * @param proof the proof of the returned result
s	 */
	public static ResultLp get_YES_Instance(Proof proof) {
		return new ResultLp(ResultType.YES, proof);
	}
	
	/**
	 * Returns a result indicating that all the specified modes
	 * could be proved non-terminating.
	 * 
	 * @param proof the proof of the returned result
s	 */
	public static ResultLp get_NO_Instance(Proof proof) {
		return new ResultLp(ResultType.NO, proof);
	}
	
	/**
	 * Returns a result indicating that some specified modes
	 * could not be proved terminating or non-terminating.
	 * 
	 * @param proof the proof of the returned result
s	 */
	public static ResultLp get_MAYBE_Instance(Proof proof) {
		return new ResultLp(ResultType.MAYBE, proof);
	}
	
	/**
	 * Returns a result indicating that an error occurred
	 * while proving termination or nontermination.
	 * 
	 * @param proof the proof of the returned result
s	 */
	public static ResultLp get_ERROR_Instance(Proof proof) {
		return new ResultLp(ResultType.ERROR, proof);
	}
	
	/**
	 * A value indicating whether termination or
	 * non-termination of all the specified modes
	 * could be proved.
	 */
	private final ResultType type;
		
	/**
	 * The proof that provided the <code>type</code>
	 * of this result.
	 */
	private final Proof proof;

	/**
	 * Builds a result provided by a termination prover
	 * for logic programs.
	 * 
	 * @param type the type of this result, indicating
	 * whether the prover could prove termination or 
	 * non-termination of all the specified modes
	 * @param proof the proof of this result
	 */
	private ResultLp(ResultType type, Proof proof) {
		this.type = type;
		this.proof = proof;
	}

	/**
	 * Returns the proof of this result.
	 * 
	 * @return the proof of this result
	 */
	public Proof getProof() {
		return this.proof;
	}
	
	/**
	 * Checks whether all the specified modes could
	 * be proved terminating.
	 * 
	 * @return <code>true</code> iff all the specified
	 * modes could be proved terminating
	 */
	public boolean isYES() {
		return this.type == ResultType.YES;
	}
	
	/**
	 * Checks whether all the specified modes could
	 * be proved non-terminating.
	 * 
	 * @return <code>true</code> iff all the specified
	 * modes could be proved non-terminating
	 */
	public boolean isNO() {
		return this.type == ResultType.NO;
	}
	
	/**
	 * Checks whether some specified modes could not
	 * be proved terminating or non-terminating.
	 * 
	 * @return <code>true</code> iff this result
	 * indicates that some specified modes could not
	 * be proved terminating or non-terminating
	 */
	public boolean isMAYBE() {
		return this.type == ResultType.MAYBE;
	}
	
	/**
	 * Checks whether an error occurred while
	 * proving termination or nontermination.
	 * 
	 * @return <code>true</code> iff an error
	 * occurred while proving termination or
	 * nontermination
	 */
	public boolean isERROR() {
		return this.type == ResultType.ERROR;
	}
	
	/**
	 * Returns a String representation of this result.
	 */
	@Override
	public String toString() {
		return this.type.toString();
	}
}
