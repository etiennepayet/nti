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
 
 package fr.univreunion.nti.parse;

/**
 * A pair (token, attribute) that is returned by a scanner.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Pair {
	
	/**
	 * The token in this pair.
	 */
	private final Token token;
	
	/**
	 * The attribute of the token in this pair.
	 */
	private final Object attribute;

	/**
	 * Constructs a pair (token, attribute).
	 * 
	 * @param token the token in this pair
	 * @param attribute the attribute of the token in this pair
	 */
	public Pair(Token token, Object attribute) {
		this.token = token;
		this.attribute = attribute;
	}
	
	/**
	 * Constructs a pair from the specified token.
	 * The corresponding attribute is set to <tt>null</tt>.
	 * 
	 * @param token the token in this pair
	 */
	public Pair(Token token) {
		this.token = token;
		this.attribute = null;
	}
	
	/**
	 * Returns the token in this pair.
	 * 
	 * @return the token in this pair
	 */
	public Token getToken() {
		return this.token;
	}
	
	/**
	 * Returns the attribute in this pair.
	 * 
	 * @return the attribute in this pair
	 */
	public Object getAttribute() {
		return this.attribute;
	}
	
	/**
	 * Returns a String representation of this pair.
	 * 
	 * @return a String representation of this pair
	 */
	@Override
	public String toString() {
		return "(" + this.token + ", " + this.attribute + ")";
	}
}
