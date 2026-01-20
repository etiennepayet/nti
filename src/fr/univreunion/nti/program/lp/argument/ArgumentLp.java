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

package fr.univreunion.nti.program.lp.argument;

import java.util.LinkedList;
import java.util.List;

import fr.univreunion.nti.program.Argument;

/**
 * A non-termination proof argument in LP. It is a collection 
 * of proof arguments for specific modes.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentLp implements Argument {

	/**
	 * The proof arguments.
	 */
	private final List<Argument> proofArguments = new LinkedList<>();

	/**
	 * Appends the specified argument to this argument.
	 *  
	 * @param A argument to be appended to this argument
	 * @return <code>true</code>
	 */
	public boolean add(Argument A) {
		return this.proofArguments.add(A);
	}

	/**
	 * Checks whether this argument is empty.
	 * 
	 * @return <code>true</code> iff this
	 * argument is empty
	 */
	public boolean isEmpty() {
		return this.proofArguments.isEmpty();
	} 

	/**
	 * Returns a detailed String representation of
	 * this argument (usually used while printing
	 * proofs in verbose mode).
	 * 
	 * The empty string is always returned for objects
	 * of this class.
	 * 
	 * @param indentation the number of single spaces
	 * to print at the beginning of each line of the
	 * detailed representation
	 * @return the empty string
	 */
	@Override
	public String getDetails(int indentation) {
		return "";
	}

	/**
	 * Returns a String representation of the kind
	 * of witness provided by this argument.
	 * 
	 * @return a String representation of the kind
	 * of witness provided by this argument
	 */
	@Override
	public String getWitnessKind() {
		return "collection of arguments for specific modes";
	}

	/**
	 * Returns a String representation of this proof argument.
	 * 
	 * @return a String representation of this proof argument
	 */
	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		boolean first = true;
		for (Argument A : this.proofArguments) {
			if (first) first = false;
			else result.append("\n");
			result.append(A);
		}

		return result.toString();
	}
}
