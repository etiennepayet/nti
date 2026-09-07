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

package fr.univreunion.nti.program.trs.family;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.ReadOnlyTermUnifier;
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
	private final Trs trs;

	/**
	 * The set of edges of the graph. It is a mapping from hash codes
	 * of terms to sets of function symbols. A mapping h(t) -> F
	 * from the hash code h(t) of term t to the set F of function
	 * symbols means that each symbol f of F is reachable from t.
	 */
	private final Map<String, Set<FunctionSymbol>> edges =
            new HashMap<>();

	/**
	 * The set of terms corresponding to the hash codes
	 * in the edges.
	 */
	private final Map<String, Term> hashCodes = new HashMap<>();

	/**
	 * Builds a graph of functional dependencies
	 * for the provided term rewrite system.
	 *
	 * @param trs the term rewrite system to which
	 * this graph refers
	 */
	public FdGraph(Trs trs) {
		this.trs = trs;
	}

	/**
	 * Adds an edge from <code>start</code> to <code>end</code>
	 * to this graph if it is not already present.
	 *
	 * @param start the start node of the edge to add
	 * @param end the end node of the edge to add
	 * @throws NullPointerException if <code>start</code> or
	 * <code>end</code> is <code>null</code>
	 */
	public void addEdge(Term start, Term end) {
		String s = start.toString();
		Set<FunctionSymbol> ends = this.edges.get(s);
		if (ends == null) {
			ends = new HashSet<>();
			ends.add(end.getRootSymbol());
			this.edges.put(s, ends);
			this.hashCodes.put(s, start.deepCopy());
		}
		else
			ends.add(end.getRootSymbol());
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
		this.addReachableSymbols(t, family);

		// Then, compute the family sets of the arguments of t.
		int n = t.getRootSymbol().getArity();
		for (int i = 0; i < n; i++)
			family.add(i, this.getFamily(t.get(i)));

		return family;
	}

	/**
	 * Adds to the specified family every symbol reachable from the specified
	 * term.
	 *
	 * @param term the term whose reachable symbols have to be added
	 * @param family the family to complete
	 */
	private void addReachableSymbols(Term term, Family family) {
		if (this.hashCodes.isEmpty()) return;

		ReadOnlyTermUnifier unifier =
				ReadOnlyTermUnifier.forFreshLinearSource(
						term.buildConnectabilityPattern(this.trs));
		for (Map.Entry<String, Term> entry : this.hashCodes.entrySet())
			if (unifier.isUnifiableWith(entry.getValue()))
				family.addAll(this.edges.get(entry.getKey()));
	}

	/**
	 * Transforms this graph into its transitive closure.
	 */
	public void closeTransitively() {
		boolean hasChanged;

		do {
			hasChanged = this.propagateReachability();
		} while (hasChanged);
	}

	/**
	 * Performs one reachability-propagation pass over this graph.
	 *
	 * @return <code>true</code> if at least one reachable symbol was added
	 */
	private boolean propagateReachability() {
		boolean hasChanged = false;
		Set<String> starts = this.edges.keySet();

		for (String start : starts)
			hasChanged |= this.propagateReachabilityFrom(start, starts);

		return hasChanged;
	}

	/**
	 * Propagates the symbols reachable from the nodes that are themselves
	 * reachable from the specified start node.
	 *
	 * @param start the start node from which reachability is propagated
	 * @param starts all the start nodes of this graph
	 * @return <code>true</code> if at least one reachable symbol was added
	 */
	private boolean propagateReachabilityFrom(String start, Set<String> starts) {
		boolean hasChanged = false;
		Set<FunctionSymbol> reachableSymbols = this.edges.get(start);

		for (String other : starts)
			if (this.isReachableStart(other, start, reachableSymbols))
				hasChanged |= reachableSymbols.addAll(this.edges.get(other));

		return hasChanged;
	}

	/**
	 * Returns whether the specified other node can be reached from a start node.
	 *
	 * @param other the potential reachable node
	 * @param start the node from which reachability is considered
	 * @param reachableSymbols the symbols currently reachable from start
	 * @return <code>true</code> if other can be reached from start
	 */
	private boolean isReachableStart(
			String other, String start, Set<FunctionSymbol> reachableSymbols) {
		if (other.equals(start))
			return false;

		FunctionSymbol otherRoot = this.hashCodes.get(other).getRootSymbol();
		return reachableSymbols.contains(otherRoot) ||
				reachableSymbols.contains(Variable.VARIABLE_ROOT_SYMBOL);
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
