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

package fr.univreunion.nti.term;

import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.NoSuchElementException;


/**
 * A position in a term.
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Position implements Iterable<Integer> {

	/**
	 * The elements of this position.
	 */
	private final Deque<Integer> elements;

	/**
	 * Constructs an empty position.
	 */
	public Position() {
		this.elements = new LinkedList<Integer>();
	}

	/**
	 * Constructs a singleton position whose
	 * unique element is the specified one.
	 */
	public Position(int i) {
		this.elements = new LinkedList<Integer>();
		this.elements.add(i);
	}

	/**
	 * Constructs a position whose elements are
	 * the specified ones.
	 * 
	 * @param elements the elements of this position
	 */
	private Position(Deque<Integer> elements) {
		this.elements = elements;
	}

	/**
	 * Indicates whether this position is the
	 * empty (root) position.
	 * 
	 * @return <code>true</code> iff this position
	 * is the empty position
	 */
	public boolean isEmpty() {
		return this.elements.isEmpty();
	}

	/**
	 * Returns the first element of this position.
	 * 
	 * @return the first element of this position
	 * @throws NoSuchElementException if this position
	 * is empty
	 */
	public int getFirst() {
		return this.elements.getFirst();
	}

	/**
	 * Returns a new position whose first element is the
	 * specified one, followed by the elements of this
	 * position. This position is not modified by this
	 * operation.
	 * 
	 * @param i the element to be added
	 * @return the new position
	 */
	public Position addFirst(int i) {
		LinkedList<Integer> L = new LinkedList<Integer>(this.elements);
		L.addFirst(i);

		return new Position(L);
	}

	/**
	 * Returns a new position whose elements are those of this
	 * position followed by those of the specified position.
	 * This position is not modified by this operation.
	 * 
	 * @param p a position to append at the end of this
	 * position
	 * @return the new position
	 * @throws NullPointerException if the specified position
	 * is <code>null</code>
	 */
	public Position append(Position p) {
		LinkedList<Integer> L = new LinkedList<Integer>(this.elements);
		L.addAll(p.elements);

		return new Position(L);
	}

	/**
	 * Returns a new position that contains the elements
	 * of this position but the last. If this position
	 * is empty, then returns <code>null</code>.
	 * 
	 * @return a new position that contains the elements
	 * of this position but the last, or <code>null</code>
	 */
	public Position properPrefix() {
		if (this.isEmpty())
			return null;

		LinkedList<Integer> L = new LinkedList<Integer>(this.elements);
		L.removeLast();

		return new Position(L);
	}

	/**
	 * Returns an iterator over the elements of
	 * this position.
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<Integer> iterator() {
		return this.elements.iterator();
	}

	/**
	 * Returns a string representation of this position.
	 * 
	 * @return a string representation of this position
	 */
	@Override
	public String toString() {
		return (this.elements.isEmpty() ? "epsilon" : this.elements.toString());
	}
}
