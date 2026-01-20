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

package fr.univreunion.nti.program.trs.reducpair;

import java.util.Collection;

import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;

/**
 * A lexicographic path order (LPO).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Lpo implements ReducPair {

	/**
	 * The strict order on function symbols that
	 * induces this LPO.
	 */
	private final LexOrder lexo = new LexOrder();
	
	/**
	 * Returns the strict order on function symbols
	 * that induces this LPO.
	 * 
	 * @return the strict order on function symbols
	 * that induces this LPO
	 */
	public LexOrder getLexOrder() {
		return this.lexo;
	}
	
	/**
	 * Completes this LPO so that, for each pair
	 * <code>(l,r)</code> in the specified collection,
	 * we have <code>l &ge; r</code> w.r.t. this LPO.
	 * 
	 * @param c a collection of pairs of terms
	 * @return <code>true</code> iff the completion
	 * succeeds
	 */
	public boolean complete(Collection<PairOfTerms> c) {
		
		for (PairOfTerms pair : c)
			if (!pair.getLeft().completeLPO(this.lexo, pair.getRight()))
				return false;

		return true;
	}
	
	/**
	 * Returns a string representation of this object.
	 * 
	 * @param indentation the number of single spaces to
	 * to print at the beginning of each line
	 * @return a string representation of this object
	 */
	@Override
	public String toString(int indentation) {
		StringBuffer s = new StringBuffer();
		
		for (int i = 0; i < indentation; i++)
			s.append(" ");
		
		s.append("Lexicographic path order induced by the precedence: ");
		s.append(this.lexo);
		
		return s.toString();
	}
}
