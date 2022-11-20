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

import java.util.Collection;
import java.util.Iterator;

import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A Knuth-Bendix order (KBO). It is induced by a strict order
 * on function symbols and a weight function.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Kbo implements ReducPair {

	/**
	 * The strict order on function symbols that
	 * induces this KBO.
	 */
	private final LexOrder lexo;
	
	/**
	 * The weight function that induces this KBO.
	 */
	private final WeightFunction wf;
	
	/**
	 * Builds a KBO with an empty strict order and
	 * the specified weight function.
	 * 
	 * @param wf a weight function
	 */
	public Kbo(WeightFunction wf) {
		this.lexo = new LexOrder();
		this.wf = wf;
	}
	
	/**
	 * Shallow copy constructor.
	 * 
	 * @param kbo the KBO to copy
	 */
	public Kbo(Kbo kbo) {
		this.lexo = new LexOrder(kbo.lexo);
		this.wf = kbo.wf;
	}
	
	/**
	 * Returns the strict order on function symbols
	 * that induces this KBO.
	 * 
	 * @return the strict order on function symbols
	 * that induces this KBO
	 */
	public LexOrder getLexOrder() {
		return this.lexo;
	}
	
	/**
	 * Returns the weight function that induces
	 * this KBO.
	 * 
	 * @return the weight function that induces
	 * this KBO
	 */
	public WeightFunction getWeightFunction() {
		return this.wf;
	}
	
	/**
	 * Removes all of the bindings <code>f &gt; g</code>
	 * from this order.
	 */
	public void clear() {
		this.lexo.clear();
	}
	
	/**
	 * Completes this KBO so that, for each pair
	 * <code>(l,r)</code> in the specified
	 * collection, we have <code>l &ge; r</code>
	 * w.r.t. this KBO.
	 * 
	 * @param c a collection of pairs of terms
	 * @return <code>true</code> iff the completion
	 * succeeds
	 */
	public boolean complete(Collection<PairOfTerms> c) {

		for (PairOfTerms pair : c)
			if (!pair.getLeft().
					completeKBO(this.lexo, this.wf, pair.getRight()))
				return false;

		return true;
	}
	
	/**
	 * Completes this KBO so that condition 2 of
	 * <em>admissibility</em> (see [Baader & Nipkow, 1998],
	 * p. 124) is satisfied.
	 * 
	 * @return <code>true</code> iff the completion succeeds
	 */
	public boolean completeAdmissible2() {

		Iterator<FunctionSymbol> it = this.wf.symbolsIterator();

		while (it.hasNext()) {
			FunctionSymbol f = it.next();

			if (f.getArity() == 1) {
				// f is a unary function symbol. If its weight
				// is 0, then it has to be the greatest element
				// relatively to the specified order.

				// We require that f is greater than the other symbols.
				Iterator<FunctionSymbol> it2 = this.wf.symbolsIterator();
				while (it2.hasNext()) {
					FunctionSymbol g = it2.next();
					if (f != g && !this.lexo.add(f, g)) return false;
				}
			}
		}

		// Here, we succeeded in completing the partial order.
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
		
		s.append("Knuth-Bendix order induced by the precedence: ");
		s.append(this.lexo);
		s.append("\n");
		
		for (int i = 0; i < indentation; i++)
			s.append(" ");
		
		s.append("and the weight function: ");
		s.append(this.wf);
		
		return s.toString();
	}
}
