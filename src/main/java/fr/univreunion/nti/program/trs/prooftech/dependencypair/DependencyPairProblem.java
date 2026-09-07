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

import java.util.HashMap;
import java.util.LinkedList;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;

/**
 * A dependency pair problem. It consists of a TRS and
 * a set of dependency pairs of this TRS.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DependencyPairProblem {

	/**
	 * The TRS of this problem.
	 */
	private final Trs trs;

	/**
	 * The set of dependency pairs of this problem.
	 */
	private final DependencyPairs dependencyPairs;

	/**
	 * Builds a dependency pair problem.
	 * <p>
	 * The specified set of dependency pairs is
	 * supposed to consist of dependency pairs
	 * of the specified TRS (this is not checked
	 * by this constructor).
	 * 
	 * @param trs the TRS of this problem
	 * @param dependencyPairs the set of dependency pairs
	 * of this problem
	 */
	public DependencyPairProblem(Trs trs, DependencyPairs dependencyPairs) {
		this.trs = trs;
		this.dependencyPairs = dependencyPairs;
	}

	/**
	 * Returns a deep copy of this problem.
	 * 
	 * @return a deep copy of this problem
	 */
	public DependencyPairProblem copy() {

		// We copy the TRS of this problem
		// together with its dependency pairs.
		HashMap<RuleTrs, RuleTrs> dependencyPairsCopy = new HashMap<>();
		Trs trsCopy = this.trs.copy(dependencyPairsCopy);

		// Then, we copy each dependency pair of
		// this problem.
		LinkedList<RuleTrs> copiedDependencyPairs = new LinkedList<>();
		for (RuleTrs rule : this.dependencyPairs)
			copiedDependencyPairs.add(dependencyPairsCopy.get(rule));

		return new DependencyPairProblem(
				trsCopy, new DependencyPairs(copiedDependencyPairs));
	}
	
	/**
	 * Returns a shallow copy of this problem, i.e.,
	 * only a shallow copy of its TRS is built. 
	 * 
	 * @return a shallow copy of this problem
	 */
	public DependencyPairProblem shallowCopy() {

		Trs trsCopy = this.trs.shallowCopy();
		DependencyPairs dependencyPairsCopy = this.dependencyPairs.copy();

		return new DependencyPairProblem(trsCopy, dependencyPairsCopy);
	}

	/**
	 * Returns the TRS of this problem.
	 */
	public Trs getTRS() {
		return this.trs;
	}

	/**
	 * Returns the set of dependency pairs of this problem.
	 */
	public DependencyPairs getDependencyPairs() {
		return this.dependencyPairs;
	}
	
	/**
	 * Returns the number of dependency pairs
	 * of this problem.
	 * 
	 * @return the number of dependency pairs
	 * of this problem
	 */
	public int nbDependencyPairs() {
		return this.dependencyPairs.size();
	}

	/**
	 * Returns a string representation of this problem.
	 * 
	 * @param indentation the number of single spaces
	 * to print before this problem
	 */
	public String toString(int indentation) {
		StringBuilder s = new StringBuilder();

		// The set of dependency pairs of this problem.
		s.repeat(" ", Math.max(0, indentation));
		s.append("Dependency pairs = ");
		s.append(this.dependencyPairs);
		s.append('\n');

		// The rules of the TRS of this problem.
		boolean first = true;
		s.repeat(" ", Math.max(0, indentation));
		s.append("TRS = {");
		for (RuleTrs rule : this.trs) {
			if (first) first = false;
			else s.append(", ");
			s.append(rule);
		}
		s.append("}");

		return s.toString();
	}

	/**
	 * Returns a string representation of this problem.
	 */
	@Override
	public String toString() {
		return this.toString(0);
	}
}
