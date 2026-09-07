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
 
 package fr.univreunion.nti.parse;

/**
 * A pair (token, attribute) that is returned by a scanner.
 *
 * @param token     The token in this pair.
 * @param attribute The attribute of the token in this pair.
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public record Pair(Token token, Object attribute) {

	/**
	 * Constructs a pair from the specified token.
	 * The corresponding attribute is set to {@code null}.
	 *
	 * @param token the token in this pair
	 */
	public Pair(Token token) {
		this(token, null);
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
