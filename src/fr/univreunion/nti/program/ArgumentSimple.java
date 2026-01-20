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

package fr.univreunion.nti.program;

/**
 * The simplest form of a proof argument.
 * It only consists of a string that quickly
 * describes why the proof has succeeded or
 * failed.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentSimple implements Argument {

	/**
	 * A quick description of the reason why
	 * the proof has succeeded or failed.
	 */
	private final String description;

	/**
	 * Builds a simple proof argument.
	 * 
	 * @param description a quick description
	 * of the reason why the proof has succeeded
	 * or failed
	 */
	public ArgumentSimple(String description) {
		this.description = description;
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
	 * The empty string is always returned for objects
	 * of this class.
	 * 
	 * @return the empty string
	 */
	@Override
	public String getWitnessKind() {
		return "";
	}

	/**
	 * Returns a string representation of this argument.
	 * 
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		return this.description;
	}
}
