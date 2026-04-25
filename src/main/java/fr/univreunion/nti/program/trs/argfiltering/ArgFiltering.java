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

package fr.univreunion.nti.program.trs.argfiltering;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * An argument filtering used in the dependency pair framework.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgFiltering {

	/**
	 * The mapping from symbols to their filter.
	 */
	private final Map<FunctionSymbol, Filter> filters = new HashMap<FunctionSymbol, Filter>();

	/**
	 * Adds an empty filter for the specified symbol
	 * to this argument filtering, if the specified
	 * symbol does not have a filter yet.
	 * 
	 * If the arity of the specified symbol is 0,
	 * then it is not added to this argument filtering.
	 * 
	 * @param f a function or tuple symbol
	 * @return <code>true</code> iff this argument
	 * filtering changed as a result of the call
	 */
	public boolean add(FunctionSymbol f) {
		if (0 < f.getArity())
			if (this.filters.get(f) == null) {
				this.filters.put(f, new Filter(f));
				return true;
			}

		return false;
	}

	/**
	 * Returns the filter associated with the specified
	 * function or tuple symbol.
	 * 
	 * @param f a function or tuple symbol
	 * @return the filter associated with the specified
	 * function or tuple symbol, or <code>null</code>
	 * if no filter is associated with the specified
	 * symbol
	 */
	public Filter get(FunctionSymbol f) {
		return this.filters.get(f);
	}

	/**
	 * Returns a collection consisting of all the filters
	 * stored in this object.
	 * 
	 * @return a collection consisting of all the filters
	 * stored in this object
	 */
	public Collection<Filter> getAllFilters() {
		// The collection to return at the end.
		Collection<Filter> L = new LinkedList<Filter>();

		for (Map.Entry<FunctionSymbol, Filter> e : this.filters.entrySet())
			L.add(e.getValue());

		return L;
	}

	/**
	 * Applies this argument filtering to the rules
	 * provided by the specified iterator.
	 * 
	 * @param it an iterator over a collection of rewrite rules
	 * @return the list of pairs resulting from applying this
	 * filtering to the rules provided by the specified
	 * iterator
	 */
	public List<PairOfTerms> applyFilters(Iterator<RuleTrs> it) {
		// The value to return at the end.
		List<PairOfTerms> L = new LinkedList<PairOfTerms>();

		while (it.hasNext()) {
			RuleTrs R = it.next();
			L.add(new PairOfTerms(R,
					R.getLeft().applyFilters(this),
					R.getRight().applyFilters(this)));
		}

		return L;
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer("{");

		boolean notfirst = false;
		for (Map.Entry<FunctionSymbol, Filter> e : this.filters.entrySet()) {
			if (notfirst) s.append(", ");
			else notfirst = true;

			FunctionSymbol f = e.getKey();
			if (":".equals(f.getName()))
				s.append("'" + f.toString() + "'");
			else 
				s.append(f.toString());
			s.append(":" + e.getValue());
		}

		s.append("}");
		return s.toString();
	}
}
