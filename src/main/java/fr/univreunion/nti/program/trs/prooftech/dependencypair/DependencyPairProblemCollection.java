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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;

/**
 * A collection of dependency pair problems to be
 * handled by a dependency pair processor. All the
 * problems in such a collection are supposed to
 * consist of the same TRS.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DependencyPairProblemCollection implements Iterable<DependencyPairProblem> {

	/**
	 * The dependency pair problems of this collection.
	 */
	private final Deque<DependencyPairProblem> problems = new LinkedList<>();

	/**
	 * Builds an empty collection of dependency pair problems.
	 */
	public DependencyPairProblemCollection() {
		// The field initializer creates the empty underlying collection.
	}

	/**
	 * Returns a deep copy of this collection.
	 * 
	 * @return a deep copy of this collection
	 */
	public DependencyPairProblemCollection copy() {

		// The result to return at the end.
		DependencyPairProblemCollection copy = new DependencyPairProblemCollection();

		if (!this.problems.isEmpty()) {
			// All the problems in this collection are
			// supposed to consist of the same TRS.
			Trs trs = this.problems.getFirst().getTRS();

			// We copy the TRS and its dependency pairs.
			HashMap<RuleTrs, RuleTrs> dependencyPairsCopy = new HashMap<>();
			Trs trsCopy = trs.copy(dependencyPairsCopy);

			// Then, we copy each problem of this collection.
			for (DependencyPairProblem problem : this.problems) {
				// We copy the dependency pairs of problem.
				LinkedList<RuleTrs> copiedDependencyPairs = new LinkedList<>();
				for (RuleTrs rule : problem.getDependencyPairs())
					copiedDependencyPairs.add(dependencyPairsCopy.get(rule));
				copy.problems.add(new DependencyPairProblem(
						trsCopy, new DependencyPairs(copiedDependencyPairs)));
			}
		}

		return copy;
	}

	/**
	 * Returns the number of dependency pair problems
	 * in this collection.
	 */
	public int size() {
		return this.problems.size();
	}

	/**
	 * Returns the average number of dependency
	 * pairs contained in the dependency pair problems
	 * of this collection.
	 */
	public float averageNbOfDependencyPairs() {
		int sum = 0;

		for (DependencyPairProblem problem : this.problems)
			sum += problem.nbDependencyPairs();

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
	 * Adds the specified dependency pair problem to this collection.
	 * 
	 * @param problem a dependency pair problem to add to this collection
	 * @return <code>true</code> iff this collection changed
	 * as a result of the call
	 */
	public boolean add(DependencyPairProblem problem) {
		return this.problems.add(problem);
	}

	/**
	 * Adds all the dependency pair problems in the
	 * specified collection to this collection.
	 * 
	 * @param probCollection a collection of dependency pair
	 * problems to add to this collection
	 * @return <code>true</code> iff this collection
	 * changed as a result of the call
	 */
	public boolean addAll(DependencyPairProblemCollection probCollection) {
		return this.problems.addAll(probCollection.problems);
	}

	/**
	 * Removes all the elements from this collection.
	 * The collection will be empty after this method
	 * returns.
	 */
	public void clear() {
		this.problems.clear();
	}

	/**
	 * Returns an iterator over the dependency pair problems
	 * of this collection.
	 */
	@Override
	public Iterator<DependencyPairProblem> iterator() {
		return this.problems.iterator();
	}
}
