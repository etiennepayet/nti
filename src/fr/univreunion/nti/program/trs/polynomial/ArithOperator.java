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

package fr.univreunion.nti.program.trs.polynomial;

/**
 * An arithmetic operator.
 * 
 * An object of this class is immutable.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public enum ArithOperator {

	/**
	 * The arithmetic operators defined in this enum.
	 */
	PLUS  ("+"),
	MINUS ("-"),
	TIMES ("*");
	
	/**
	 * The name of this operator.
	 */
	private final String name;
		
	/**
	 * Constructs an arithmetic operator with
	 * the given name.
	 * 
	 * @param name the name of the operator
	 */
	private ArithOperator(String name) {
		this.name = name;
	}
	
	/**
	 * Returns the name of this operator.
	 * 
	 * @return the name of this operator
	 */
	public String getName() {
		return this.name;
	}
	
	/**
	 * Returns a string representation of this operator.
	 */
	public String toString() {
		return this.name;
	}
}
