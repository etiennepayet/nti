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

package fr.univreunion.nti.program.lp.argument;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.term.Function;

/**
 * A non-termination proof argument in LP. It is produced
 * when a non-terminating atomic query has been found for
 * a specific mode.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentModeLp implements Argument {

	/**
	 * The mode whose non-termination has been proved.
	 */
	private final Mode mode;

	/**
	 * The non-terminating atomic query that corresponds
	 * to <code>mode</code>.
	 */
	private final Function query;

	/**
	 * The witness that <code>mode</code> is
	 * non-terminating.
	 */
	private final NonTerminationWitness witness;

	/**
	 * Builds a non-termination argument for the specified mode.
	 *
	 * @param mode the mode whose non-termination has be proved
	 * @param query the non-terminating atomic query that corresponds
	 * to <code>mode</code>
	 * @param witness the witness that <code>mode</code> is
	 * non-terminating
	 */
	public ArgumentModeLp(Mode mode, Function query, NonTerminationWitness witness) {
		this.mode = mode;
		this.query = query;
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
		return "non-terminating atomic query";
	}

	/**
	 * Returns a String representation of this proof argument.
	 *
	 * @return a String representation of this proof argument
	 */
	@Override
	public String toString() {
        return "Mode " +
                this.mode +
                ": the query " +
                this.query +
                " is non-terminating " +
                this.witness.getShortDescription();
	}
}
