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

package fr.univreunion.nti.program.trs.family;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A graph of functional dependencies of a term rewrite system.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class FdGraph {

	/**
	 * The term rewrite system to which this graph refers.
	 */
	private final Trs IR;

	/**
	 * The set of edges of the graph. It is a mapping from hash codes
	 * of terms to sets of function symbols. A mapping h(t) -> F
	 * from the hash code h(t) of term t to the set F of function
	 * symbols means that each symbol f of F is reachable from t.
	 */
	private final Map<String, Set<FunctionSymbol>> edges =
			new HashMap<String, Set<FunctionSymbol>>();

	/**
	 * The set of terms corresponding to the hash codes
	 * in the edges. 
	 */
	private final Map<String, Term> hashCodes = new HashMap<String, Term>();

	/**
	 * Builds a graph of functional dependencies
	 * for the provided term rewrite system.
	 * 
	 * @param IR the term rewrite system to which
	 * this graph refers 
	 */
	public FdGraph(Trs IR) {
		this.IR = IR;
	}

	/**
	 * Adds an edge from <code>start</code> to <code>end</code>
	 * to this graph if it is not already present.
	 * 
	 * @param start the start node of the edge to add 
	 * @param end the end node of the edge to add
	 * @return <code>true</code> if this graph did not already
	 * contain the specified edge
	 * @throws NullPointerException if <code>start</code> or
	 * <code>end</code> is <code>null</code>
	 */
	public boolean addEdge(Term start, Term end) {
		String s = start.toString();
		Set<FunctionSymbol> ends = this.edges.get(s);
		if (ends == null) {
			ends = new HashSet<FunctionSymbol>();
			ends.add(end.getRootSymbol());
			this.edges.put(s, ends);
			this.hashCodes.put(s, start.deepCopy());
			return true;
		}
		else
			return ends.add(end.getRootSymbol());
	}

	/**
	 * Returns the family of the specified term relatively
	 * to this graph and to the specified depth.
	 * 
	 * @param t the term whose family has to be computed
	 * @return the family of the specified term relatively
	 * to this graph and to the specified depth
	 * @throws NullPointerException if <code>t</code> is
	 * <code>null</code>
	 */
	public Family getFamily(Term t) {
		Family family = new Family(t);

		// First, compute the symbols that are reachable from t.
		for (Map.Entry<String, Term> e : this.hashCodes.entrySet())
			// if (t.hasSameStructureAs(e.getValue()))
			if (t.isConnectableTo(e.getValue(), this.IR))
				family.addAll(this.edges.get(e.getKey()));

		// Then, compute the family sets of the arguments of t.
		int n = t.getRootSymbol().getArity();
		for (int i = 0; i < n; i++) 
			family.add(i, this.getFamily(t.get(i)));

		return family;
	}

	/**
	 * Transforms this graph into its transitive closure. 
	 */
	public void closeTransitively() {
		boolean hasChanged;

		do {
			hasChanged = false;
			Set<String> starts = this.edges.keySet();
			for (String s : starts) {
				Set<FunctionSymbol> F_s = this.edges.get(s);
				for (String other : starts)
					if (!other.equals(s)) {
						FunctionSymbol f = this.hashCodes.get(other).getRootSymbol();
						if (F_s.contains(f) || F_s.contains(Variable.VARIABLE_ROOT_SYMBOL))
							hasChanged |= F_s.addAll(this.edges.get(other));
					}
			}
		} while (hasChanged);
	}

	/**
	 * Returns a String representation of this graph.
	 * 
	 * @return a String representation of this graph
	 */
	@Override
	public String toString() {
		return this.edges.toString();
	}
}
