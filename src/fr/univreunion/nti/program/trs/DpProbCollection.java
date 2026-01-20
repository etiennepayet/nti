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

package fr.univreunion.nti.program.trs;

import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

/**
 * A collection of DP problems to be handled
 * by a DP processor. All the problems in
 * such a collection are supposed to consist
 * of the same TRS.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DpProbCollection implements Iterable<DpProblem> {

	/**
	 * The DP problems of this collection.
	 */
	private final Deque<DpProblem> problems = new LinkedList<DpProblem>();

	/**
	 * Builds an empty collection of DP problems.
	 */
	public DpProbCollection() {}

	/**
	 * Builds a collection of DP problems
	 * that contains the same elements as
	 * the specified collection.
	 * 
	 * @param PC a collection of DP problems
	 */
	public DpProbCollection(DpProbCollection PC) {
		this.problems.addAll(PC.problems);
	}

	/**
	 * Returns a deep copy of this collection.
	 * 
	 * @return a deep copy of this collection
	 */
	public DpProbCollection copy() {

		// The result to return at the end.
		DpProbCollection thisCopy = new DpProbCollection();

		if (!this.problems.isEmpty()) {
			// All the problems in this collection are
			// supposed to consist of the same TRS.
			Trs IR = this.problems.getFirst().getTRS();

			// We copy the TRS and its dependency pairs.
			HashMap<RuleTrs, RuleTrs> dpairsCopy = new HashMap<RuleTrs, RuleTrs>();
			Trs IRcopy = IR.copy(dpairsCopy);

			// Then, we copy each problem of this collection.
			for (DpProblem prob : this.problems) {
				// We copy the dependency pairs of prob.
				LinkedList<RuleTrs> L = new LinkedList<RuleTrs>();
				for (RuleTrs R : prob.getDependencyPairs())
					L.add(dpairsCopy.get(R));
				thisCopy.problems.add(new DpProblem(IRcopy, new Dpairs(L)));
			}
		}

		return thisCopy;
	}

	/**
	 * Returns the number of DP problems
	 * in this collection.
	 */
	public int size() {
		return this.problems.size();
	}

	/**
	 * Returns the average number of dependency
	 * pairs contained in the DP problems of this
	 * collection.
	 */
	public float averageNbOfDependencyPairs() {
		int sum = 0;

		for (DpProblem prob : this.problems)
			sum += prob.nbDependencyPairs();

		return ((float) sum) / ((float) this.problems.size());
	}

	/**
	 * Returns <code>true</code> iff this collection
	 * contains no elements.
	 * 
	 * @return <code>true</code> iff this collection
	 * contains no elements
	 */
	public boolean isEmpty() {
		return this.problems.isEmpty();
	}

	/**
	 * Adds the specified DP problem to this collection.
	 * 
	 * @param prob a DP problem to add to this collection
	 * @return <code>true</code> iff this collection changed
	 * as a result of the call
	 */
	public boolean add(DpProblem prob) {
		return this.problems.add(prob);
	}

	/**
	 * Adds all of the DP problems in the specified
	 * collection to this collection.
	 * 
	 * @param problems a collection of DP problems to
	 * add to this collection
	 * @return <code>true</code> iff this collection
	 * changed as a result of the call
	 */
	public boolean addAll(DpProbCollection PC) {
		return this.problems.addAll(PC.problems);
	}

	/**
	 * Removes all of the elements from this collection.
	 * The collection will be empty after this method
	 * returns.
	 */
	public void clear() {
		this.problems.clear();
	}

	/**
	 * Returns an iterator over the DP problems
	 * of this collection.
	 */
	@Override
	public Iterator<DpProblem> iterator() {
		return this.problems.iterator();
	}
}
