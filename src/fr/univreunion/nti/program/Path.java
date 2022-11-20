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

package fr.univreunion.nti.program;

import java.util.Deque;
import java.util.LinkedList;

/**
 * A path in a program that corresponds to an unfolded rule.
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Path {

	/**
	 * The elements of this path.
	 */
	private final Deque<Rule> elements = new LinkedList<Rule>();
	
	/**
	 * Builds an empty path.
	 */
	public Path() {}
	
	/**
	 * Builds a singleton path consisting of the
	 * provided rule.
	 * 
	 * @param R the unique element of this path
	 */
	public Path(Rule R) {
		this.elements.add(R);
	}
	
	/**
	 * Appends all of the elements in the specified path
	 * to the end of this path.
	 * 
	 * @param p path containing elements to be added to
	 * this path
	 * @return <code>true</code> if this path changed as
	 * a result of the call
	 */
	public boolean addAll(Path p) {
		return this.elements.addAll(p.elements);
	}
	
	/**
	 * Inserts the specified rule at the end of this
	 * path. 
	 * 
	 * @param R the element to add
	 */
	public void addLast​(Rule R) {
		this.elements.addLast(R);
	}
	
	/**
	 * Returns a string representation of this path.
	 * 
	 * @return a string representation of this path
	 */
	@Override
	public String toString() {
		StringBuffer result = new StringBuffer("<");
		
		int n = this.elements.size();
		for (Rule R : this.elements) {
			result.append(R.getNumberInFile());
			if (1 < n--) result.append(",");
		}
		
		result.append(">");
		
		return result.toString();
	}
}
