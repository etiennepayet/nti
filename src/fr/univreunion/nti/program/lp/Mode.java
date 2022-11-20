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

package fr.univreunion.nti.program.lp;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;

/**
 * A mode for a predicate symbol.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Mode implements Iterable<Integer> {

	/**
	 * The predicate symbol of this mode.
	 */
	private final FunctionSymbol predSymbol;

	/**
	 * The argument positions that are considered input,
	 * bound or ground by this mode.
	 */
	private final LinkedList<Integer> positions = new LinkedList<Integer>();

	/**
	 * Constructs a new mode for the given predicate symbol.
	 * 
	 * @param predSymbol the predicate symbol of the mode
	 * @param positions the argument positions that are
	 * considered input, bound or ground by the mode
	 */
	public Mode(FunctionSymbol predSymbol, List<Integer> positions) {
		this.predSymbol = predSymbol;
		this.positions.addAll(positions);
	}

	/**
	 * Constructs a new mode from an atom <code>p(a_0,...,a_n)</code>.
	 * Each <code>a_k</code> of the form <code>i</code>, <code>b</code>
	 * and <code>g</code> respectively determines an input, bound and
	 * ground position of the constructed mode.
	 * 
	 * @param A an atom
	 * @throws IllegalArgumentException if <code>A</code> is <code>null</code>
	 */
	public Mode(Function A) throws IllegalArgumentException
	{
		if (A == null)
			throw new IllegalArgumentException("construction of a mode from a null term");
		
		this.predSymbol = A.getRootSymbol();

		int n = this.predSymbol.getArity();
		for (int p = 0; p < n; p++) {
			Term t_p = A.get(new Position(p));
			if (t_p instanceof Function) {
				FunctionSymbol f = ((Function)t_p).getRootSymbol();
				String name = f.getName();
				if (f.getArity() == 0 && 
						("i".equals(name) || "b".equals(name) || "g".equals(name)))
					this.positions.add(p);
			}
		}
	}

	/**
	 * Returns the predicate symbol of this mode.
	 * 
	 * @return the predicate symbol of this mode
	 */
	public FunctionSymbol getPredSymbol() {
		return this.predSymbol;
	}

	/**
	 * Returns an iterator over the elements of this mode.
	 * 
	 * @return an <code>Iterator</code>
	 */
	public Iterator<Integer> iterator() {
		return this.positions.listIterator();
	}

	/**
	 * Checks whether this mode contains the specified
	 * argument position.
	 * 
	 * @param i an argument position for the predicate
	 * symbol of this mode
	 * @return <code>true</code> iff this mode contains
	 * the specified argument position
	 */
	public boolean contains(int i) {
		return this.positions.contains(i);
	}
	
	/**
	 * Returns a string representation of this mode.
	 * 
	 * @return a string representation of this mode
	 */
	@Override
	public String toString() {
		int n = this.predSymbol.getArity();

		StringBuffer s = new StringBuffer(this.predSymbol.toString());

		if (n > 0) {
			s.append("(");

			int i = 0;
			for(Integer p: this.positions) {
				while (i++ < p) s.append("o,");
				s.append("i,");
			}
			while (i++ < n) s.append("o,");
			s.deleteCharAt(s.length() - 1); // remove the last comma
			
			s.append(")");
		}
		
		return s.toString();
	}
}
