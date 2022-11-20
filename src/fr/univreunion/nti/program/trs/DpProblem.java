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

package fr.univreunion.nti.program.trs;

import java.util.HashMap;
import java.util.LinkedList;

/**
 * A dependency pair problem. It consists of a TRS IR and
 * of a set of dependency pairs of IR.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DpProblem {

	/**
	 * The TRS of this problem.
	 */
	private final Trs IR;

	/**
	 * The set of dependency pairs of this problem.
	 */
	private final Dpairs dpairs;

	/**
	 * Builds a dependency pair problem.
	 * 
	 * The specified set of dependency pairs is
	 * supposed to consist of dependency pairs
	 * of the specified TRS (this is not checked
	 * by this constructor).
	 * 
	 * @param IR the TRS of this problem
	 * @param dpairs the set of dependency pairs
	 * of this problem
	 */
	public DpProblem(Trs IR, Dpairs dpairs) {
		this.IR = IR;
		this.dpairs = dpairs;
	}

	/**
	 * Returns a deep copy of this problem.
	 * 
	 * @return a deep copy of this problem
	 */
	public DpProblem copy() {

		// We copy the TRS of this problem
		// together with its dependency pairs.
		HashMap<RuleTrs, RuleTrs> dpairsCopy = new HashMap<RuleTrs, RuleTrs>();
		Trs IRcopy = this.IR.copy(dpairsCopy);

		// Then, we copy each dependency pair of
		// this problem.
		LinkedList<RuleTrs> L = new LinkedList<RuleTrs>();
		for (RuleTrs R : this.dpairs)
			L.add(dpairsCopy.get(R));

		return new DpProblem(IRcopy, new Dpairs(L));
	}
	
	/**
	 * Returns a shallow copy of this problem, i.e.,
	 * only a shallow copy of its TRS is built. 
	 * 
	 * @return a shallow copy of this problem
	 */
	public DpProblem shallowCopy() {

		Trs IRcopy = this.IR.shallowCopy();
		Dpairs dpairsCopy = this.dpairs.copy();

		return new DpProblem(IRcopy, dpairsCopy);
	}

	/**
	 * Returns the TRS of this problem.
	 */
	public Trs getTRS() {
		return this.IR;
	}

	/**
	 * Returns the set of dependency pairs of this problem.
	 */
	public Dpairs getDependencyPairs() {
		return this.dpairs;
	}
	
	/**
	 * Returns the number of dependency pairs
	 * of this problem.
	 * 
	 * @return the number of dependency pairs
	 * of this problem
	 */
	public int nbDependencyPairs() {
		return this.dpairs.size();
	}

	/**
	 * Returns a string representation of this problem.
	 * 
	 * @param indentation the number of single spaces
	 * to print before this problem
	 */
	public String toString(int indentation) {
		StringBuffer s = new StringBuffer();

		// The set of dependency pairs of this problem.
		for (int i = 0; i < indentation; i++) s.append(" ");
		s.append("Dependency pairs = ");
		s.append(this.dpairs);
		s.append('\n');

		// The rules of the TRS of this problem.
		boolean first = true;
		for (int i = 0; i < indentation; i++) s.append(" ");
		s.append("TRS = {");
		for (RuleTrs R : this.IR) {
			if (first) first = false;
			else s.append(", ");
			s.append(R);
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
