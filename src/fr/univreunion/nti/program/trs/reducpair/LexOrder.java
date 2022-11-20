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

package fr.univreunion.nti.program.trs.reducpair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A strict partial order on function symbols.
 * 
 * Used for defining lexicographic path orders, Knuth-Bendix orders...
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LexOrder {

	/**
	 * A data structure that maps any function symbol
	 * <code>f</code> to the set of function symbols
	 * <code>g</code> which are such that
	 * <code>f &gt; g</code>.
	 */
	private final Map<FunctionSymbol, Set<FunctionSymbol>> order =
			new HashMap<FunctionSymbol, Set<FunctionSymbol>>();

	/**
	 * Builds an empty order.
	 */
	public LexOrder() {}
	
	/**
	 * Copy constructor.
	 * 
	 * @param O the order to copy
	 */
	public LexOrder(LexOrder O) {
		for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> e : O.order.entrySet()) {
			Set<FunctionSymbol> S = new HashSet<FunctionSymbol>(e.getValue());
			this.order.put(e.getKey(), S);
		}
	}
	
	/**
	 * Adds <code>f &gt; g</code> to this order.
	 *  
	 * @param f a function symbol
	 * @param g a function symbol
	 * @return <code>true</code> if adding <code>f &gt; g</code>
	 * to this order succeeded and <code>false</code> otherwise
	 */
	public boolean add(FunctionSymbol f, FunctionSymbol g) {
		if (f != g) {
			Set<FunctionSymbol> S_f = this.order.get(f);
			Set<FunctionSymbol> S_g = this.order.get(g);

			if (S_g == null || !S_g.contains(f)) {
				// Here, this order does not contain g > f.
				// Hence, we can safely add f > g to it.
				// More generally, in order to get a transitively
				// closed relation, we add f' > g' for all symbols
				// f' and g' which are such that f' >= f and g >= g'. 
				
				if (S_f == null) {
					S_f = new HashSet<FunctionSymbol>();
					this.order.put(f, S_f);
				}
				
				// We consider the set consisting of all the
				// symbols g' which are such that g >= g'.
				Set<FunctionSymbol> SS_g = new HashSet<FunctionSymbol>();
				SS_g.add(g);
				if (S_g != null) SS_g.addAll(S_g);

				for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> e : this.order.entrySet()) {
					Set<FunctionSymbol> S = e.getValue();
					if (e.getKey() == f || S.contains(f))
						// Here, we come across a symbol f' which is such that f' >= f.
						// Hence, we add f' > g', for all g' such that g >= g'.
						S.addAll(SS_g);
				}

				return true;
			}
		}

		// Here, f = g or this order already contains g > f.
		// Hence, we cannot add f > g to it.
		return false;
	}
	
	/**
	 * Order union. Adds the specified order to this order.
	 * BEWARE: this operation might transform this order
	 * into an inconsistent order (i.e., an order where
	 * <code>f > g</code> and <code>g > f</code> occur,
	 * for some function symbols <code>f</code> and
	 * <code>g</code>).
	 * 
	 * @param O the order to add to this order
	 */
	public void addAll(LexOrder O) {
		for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> e : O.order.entrySet()) {
			FunctionSymbol f = e.getKey();
			Set<FunctionSymbol> S_f = e.getValue();
			
			Set<FunctionSymbol> S = this.order.get(f);
			if (S == null) {
				S = new HashSet<FunctionSymbol>();
				this.order.put(f, S);
			}
			
			S.addAll(S_f);
		}		
	}
	
	/**
	 * Removes all of the bindings <code>f > g</code>
	 * from this order.
	 */
	public void clear() {
		this.order.clear();
	}

	/**
	 * Returns a string representation of this order.
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer();
		
		boolean first = true;
		for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> e : this.order.entrySet()) {
			FunctionSymbol f = e.getKey();
			
			if (first) first = false;
			else s.append(", ");
			
			// s.append(f + " > " + e.getValue());
			
			s.append(f + " > [");
			boolean first2 = true;
			for (FunctionSymbol g : e.getValue()) {
				if (first2) first2 = false;
				else s.append(", ");
				
				s.append(g.toString());
			}
			s.append("]");
		}
		
		if (first)
			// Here, this order is necessarily empty.
			s.append("{}");
		
		return s.toString();
	}
}
