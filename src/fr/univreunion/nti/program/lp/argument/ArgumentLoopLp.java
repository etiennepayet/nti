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

package fr.univreunion.nti.program.lp.argument;

/**
 * A non-termination proof argument in LP. It is produced when
 * a looping atomic query has been found for a specific mode.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.loop.LoopWitness;
import fr.univreunion.nti.term.Function;

public class ArgumentLoopLp implements Argument {

	/**
	 * The mode whose loopingness has been proved.
	 */
	private final Mode m;

	/**
	 * The looping atomic query that corresponds to
	 * <code>m</code>.
	 */
	private final Function Q;

	/**
	 * The witness that <code>m</code> is looping.
	 */
	private final LoopWitness witness;

	/**
	 * Builds a loop argument for the specified mode.
	 * 
	 * @param m the mode whose loopingness has be proved
	 * @param Q the looping atomic query that corresponds to
	 * <code>m</code>
	 * @param witness the witness that <code>m</code> is
	 * looping
	 */
	public ArgumentLoopLp(Mode m, Function Q, LoopWitness witness) {
		this.m = m;
		this.Q = Q;
		this.witness = witness;
	}

	/**
	 * Returns a detailed String representation of
	 * this argument (usually used while printing
	 * proofs in verbose mode).
	 * 
	 * @param indentation the number of single spaces
	 * to print at the beginning of each line of the
	 * detailed representation
	 * @return a detailed String representation of
	 * this argument
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
		return "looping atomic query";
	}

	/**
	 * Returns a String representation of this proof argument.
	 * 
	 * @return a String representation of this proof argument
	 */
	@Override
	public String toString() {
		StringBuffer result = new StringBuffer();

		result.append("Mode ");
		result.append(this.m);
		result.append(": the query ");
		result.append(this.Q);
		/*
		result.append(" starts a ");
		result.append(this.witness.getLoopKind());
		result.append(" ");
		 */
		result.append(" is non-terminating ");
		result.append(this.witness.getShortDescription());

		return result.toString();
	}
}
