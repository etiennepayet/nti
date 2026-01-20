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

import java.util.LinkedList;
import java.util.List;

import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A filter for a function or tuple symbol i.e., either an argument
 * position or a list of argument positions. It is used in an argument
 * filtering, which maps function and tuple symbols to filters. 
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Filter {

	/**
	 * The function or tuple symbol to which this filter applies.
	 */
	private final FunctionSymbol f;

	/**
	 * A list of argument positions. Cannot be non-<code>null</code>
	 * while the argument position <code>I</code> (see below) is
	 * non-<code>null</code>.
	 */
	private List<Integer> L;

	/**
	 * An argument position. Cannot be non-<code>null</code>
	 * while the list <code>L</code> of argument positions
	 * (see above) is non-<code>null</code>.
	 */
	private Integer I;

	/**
	 * Builds an empty filter for the specified symbol.
	 * 
	 * @param f a function or tuple symbol
	 * @throws IllegalArgumentException if the specified
	 * symbol is a constant symbol i.e., its arity is 0
	 */
	public Filter(FunctionSymbol f) {
		if (f.getArity() <= 0)
			throw new IllegalArgumentException(
					"cannot make a filter for constant symbol");

		this.f = f;
	}

	/**
	 * Returns the function or tuple symbol to which
	 * this filter applies.
	 * 
	 * @return the function or tuple symbol to which
	 * this filter applies
	 */
	public FunctionSymbol getSymbol() {
		return this.f;
	}

	/**
	 * Returns the argument position embedded in
	 * this filter.
	 *  
	 * @return the argument position embedded in
	 * this filter, or <code>null</code> if no
	 * argument position is embedded in this
	 * filter
	 */
	public Integer getIntValue() {
		return this.I;
	}
	
	/**
	 * Returns the list of argument positions embedded
	 * in this filter.
	 *  
	 * @return the list of argument positions embedded
	 * in this filter, or <code>null</code> if no list
	 * is embedded in this filter
	 */
	public List<Integer> getListValue() {
		return this.L;
	}
	
	/**
	 * Sets the value of this filter to the specified
	 * argument position.
	 * 
	 * @param I an argument position, supposed to be
	 * a valid argument position for the function symbol
	 * associated with this filter (not checked by this
	 * method)
	 * @throws IllegalArgumentException 
	 */
	public void setValue(Integer I) {
		this.L = null;
		this.I = I;
	}

	/**
	 * Sets the value of this filter to the specified
	 * list of argument positions.
	 * 
	 * @param L a list of argument positions, supposed
	 * to be valid i.e., it only consists of valid argument
	 * positions for the function symbol associated with
	 * this filter, it is sorted in increasing order and
	 * it has no duplicate element (all these constraints
	 * are not checked by this method)
	 */
	public void setValue(List<Integer> L) {
		this.L = new LinkedList<Integer>(L);
		this.I = null;
	}

	/**
	 * Returns a string representation of this filter.
	 */
	@Override
	public String toString() {		
		return
				(this.L != null ?
						this.L.toString() :
							(this.I != null ? this.I.toString() : "?"));
	}
}
