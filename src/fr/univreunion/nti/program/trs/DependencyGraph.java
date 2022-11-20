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

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * An (estimated) dependency graph of a TRS.
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DependencyGraph {

	/**
	 * The nodes of this graph.
	 */
	private final Dpairs nodes;

	/**
	 * The predecessors of each node of this graph.
	 * 
	 * Every node in this map belongs to the set of
	 * nodes of this graph.
	 */
	private final Map<RuleTrs, Dpairs> predecessors = new HashMap<RuleTrs, Dpairs>();

	/**
	 * The successors of each node of this graph.
	 * 
	 * Every node in this map belongs to the set of
	 * nodes of this graph.
	 */
	private final Map<RuleTrs, Dpairs> successors = new HashMap<RuleTrs, Dpairs>();

	/**
	 * The SCCs of this graph.
	 */
	private final Deque<Dpairs> sccs;

	/**
	 * Builds the estimated dependency graph of
	 * the specified TRS.
	 * 
	 * @param IR a TRS whose estimated dependency
	 * graph has to be built
	 */
	public DependencyGraph(Trs IR) {

		// The nodes of this graph are the specified
		// dependency pairs.
		this.nodes = IR.dependencyPairs();

		// We first build an over-approximation of the arcs
		// of this graph.
		Map<RuleTrs, List<RuleTrs>> predecessors =
				new HashMap<RuleTrs, List<RuleTrs>>();
		Map<RuleTrs, List<RuleTrs>> successors =
				new HashMap<RuleTrs, List<RuleTrs>>();
		for (RuleTrs N : this.nodes)
			for (RuleTrs M : this.nodes)
				if (N.isConnectableTo(M, IR)) {
					List<RuleTrs> succN = successors.get(N);
					if (succN == null) {
						succN = new LinkedList<RuleTrs>();
						successors.put(N, succN);
					}
					succN.add(M);

					List<RuleTrs> predM = predecessors.get(M);
					if (predM == null) {
						predM = new LinkedList<RuleTrs>();
						predecessors.put(M, predM);
					}
					predM.add(N);
				}

		// Then, we build the SCCs of this graph from
		// the above over-approximation.
		this.sccs = buildSCCs(this.nodes, predecessors, successors);

		// finally, we build the arcs of this graph.
		for (Map.Entry<RuleTrs, List<RuleTrs>> e : predecessors.entrySet())
			this.predecessors.put(e.getKey(), new Dpairs(e.getValue()));
		for (Map.Entry<RuleTrs, List<RuleTrs>> e : successors.entrySet())
			this.successors.put(e.getKey(), new Dpairs(e.getValue()));

		// From now on, this graph consists of disconnected
		// SCCs: there is no more arc between any node of
		// a SCC to any node of another SCC.
	}

	/**
	 * Returns a collection consisting of the SCCs of this graph.
	 * 
	 * @return the SCCs of this graph
	 */
	public Deque<Dpairs> getSCCs() {
		return this.sccs;
	}

	/**
	 * Builds the SCCs of the graph having the specified
	 * set of nodes and the specified arcs.
	 * 
	 * @param nodes the nodes of the graph
	 * @param predecessors the predecessors of the nodes
	 * of the graph
	 * @param successors the successors of the nodes of
	 * the graph
	 * @return a list consisting of the SCCs of the graph
	 */
	private Deque<Dpairs> buildSCCs(
			Dpairs nodes,
			Map<RuleTrs, List<RuleTrs>> predecessors,
			Map<RuleTrs, List<RuleTrs>> successors) {

		// The list to return at the end.
		Deque<Dpairs> sccs = new LinkedList<Dpairs>();

		// First, we perform a depth first search in this graph.
		Deque<RuleTrs> L = this.depthFirstSearch(nodes, successors);

		// Then, we perform a depth first search in the
		// transpose graph, but we consider the nodes
		// in their order of appearance in L.

		// We need to know whether a node has been visited yet.
		Set<RuleTrs> visited = new HashSet<RuleTrs>();

		for (RuleTrs R : L) {
			if (!visited.contains(R)) {
				Deque<RuleTrs> scc = new LinkedList<RuleTrs>();
				this.visitBackwards(R, predecessors, visited, scc);
				// We only keep the components consisting of:
				// - more than one node
				// - one node only with an edge from the node to itself.
				// We also remove the arcs from/to nodes that do
				// not belong to the same component.
				if (scc.size() > 1 || this.isSingleLoop(scc.getFirst(), successors)) {
					this.sanitize(scc, predecessors, successors);
					sccs.add(new Dpairs(scc));
				}
			}
		}

		return sccs;
	}
	
	/**
	 * Depth first search in a graph having the specified set
	 * of nodes and the specified outgoing arcs.
	 * 
	 * @param nodes the nodes of the graph
	 * @param successors the successors of the nodes of the graph
	 * @return the list of nodes resulting from the search
	 */
	private Deque<RuleTrs> depthFirstSearch(Dpairs nodes,
			Map<RuleTrs, List<RuleTrs>> successors) {

		// The list of nodes that this method builds and returns.
		Deque<RuleTrs> result = new LinkedList<RuleTrs>();

		// We need to know whether a node has been visited yet.
		Set<RuleTrs> visited = new HashSet<RuleTrs>();

		// We visit each node that has not been visited yet.
		for (RuleTrs R : nodes)
			if (!visited.contains(R))
				this.visitForwards(R, successors, visited, result);

		return result;
	}

	/**
	 * Visits the specified node <code>R</code> forwards in
	 * a graph having the specified set of outgoing arcs
	 * <code>successors</code>. Then, inserts it at the
	 * beginning of the specified <code>result</code>.
	 * 
	 * Used in depth first search.
	 * 
	 * @param R the node to visit forwards
	 * @param successors the successors of the nodes of the graph
	 * @param visited the nodes that have been visited yet
	 * @param result the list of nodes resulting from the visit
	 */
	private void visitForwards(RuleTrs R, 
			Map<RuleTrs, List<RuleTrs>> successors,
			Set<RuleTrs> visited, Deque<RuleTrs> result) {

		visited.add(R);

		List<RuleTrs> succR = successors.get(R);
		if (succR != null)
			for (RuleTrs S : succR)
				if (!visited.contains(S))
					this.visitForwards(S, successors, visited, result);

		result.addFirst(R);
	}

	/**
	 * Visits the specified node <code>R</code> backwards in
	 * a graph having the specified set of incoming	arcs
	 * <code>predecessors</code>. Then, inserts it at the
	 * beginning of the specified <code>scc</code>.
	 * 
	 * Used for computing the SCCs.
	 * 
	 * @param R the node to visit backwards
	 * @param predecessors the predecessors of the nodes of
	 * the graph
	 * @param visited the nodes that have been visited yet
	 * @param scc the list of nodes resulting from the visit
	 * and that form the SCC currently being computed
	 */
	private void visitBackwards(RuleTrs R,
			Map<RuleTrs, List<RuleTrs>> predecessors,
			Set<RuleTrs> visited,
			Deque<RuleTrs> scc) {

		visited.add(R);

		List<RuleTrs> predR = predecessors.get(R);
		if (predR != null)
			for (RuleTrs P : predR)
				if (!visited.contains(P))
					this.visitBackwards(P, predecessors, visited, scc);

		scc.addFirst(R);
	}

	/**
	 * Removes all of the arcs to or from a node that
	 * does not belong to the specified SCC, in a graph
	 * having the specified arcs <code>predecessors</code>
	 * and <code>successors</code>.
	 * 
	 * Therefore, the specified <code>predecessors</code>
	 * and <code>successors</code> may be modified
	 * by this method.
	 *  
	 * @param scc a SCC to sanitize
	 * @param predecessors the predecessors of the nodes of
	 * the graph
	 * @param successors the successors of the nodes of
	 * the graph
	 */
	private void sanitize(Deque<RuleTrs> scc,
			Map<RuleTrs, List<RuleTrs>> predecessors,
			Map<RuleTrs, List<RuleTrs>> successors) {

		for (RuleTrs R : scc) {
			// First, we sanitize the set of predecessors of R.
			List<RuleTrs> predR = predecessors.get(R);
			if (predR != null)
				for (RuleTrs P : new LinkedList<RuleTrs>(predR))
					if (!scc.contains(P)) {
						predR.remove(P);
						List<RuleTrs> succP = successors.get(P);
						if (succP != null) succP.remove(R);
					}

			// Then, we sanitize the set of successors of R.
			List<RuleTrs> succR = successors.get(R);
			if (succR != null)
				for (RuleTrs S : new LinkedList<RuleTrs>(succR))
					if (!scc.contains(S)) {
						succR.remove(S);
						List<RuleTrs> predS = predecessors.get(S);
						if (predS != null) predS.remove(R);
					}
		}
	}

	/**
	 * Returns <code>true</code> iff the specified
	 * node is a single loop w.r.t. the specified
	 * outgoing arcs.
	 * 
	 * @param R a node to check
	 * @param successors some outgoing arcs
	 * @return <code>true</code> iff the specified
	 * node is a single loop w.r.t. the specified
	 * outgoing arcs
	 */
	private boolean isSingleLoop(RuleTrs R, Map<RuleTrs, List<RuleTrs>> successors) {
		List<RuleTrs> succR = successors.get(R);
		return (succR != null && succR.contains(R));
	}
	
	/**
	 * Returns the SCCs of the subgraph which consists of
	 * the specified nodes.
	 *  
	 * @param sub a subset of the nodes of this graph
	 * @return the SCCs of the subgraph which consists of the
	 * specified nodes
	 */
	public Deque<Dpairs> getSCCs(Collection<RuleTrs> sub) {

		// The list to return at the end.
		Deque<Dpairs> sccs = new LinkedList<Dpairs>();

		// First, we perform a depth first search in this graph.
		Deque<RuleTrs> L = this.depthFirstSearch(sub);

		// Then, we perform a depth first search in the
		// transpose graph, but we consider the nodes
		// in their order of appearance in L.

		// We need to know whether a node has been visited yet.
		Set<RuleTrs> visited = new HashSet<RuleTrs>();

		for (RuleTrs R : L) {
			if (!visited.contains(R)) {
				Deque<RuleTrs> scc = new LinkedList<RuleTrs>();
				this.visitBackwards(R, sub, visited, scc);
				// We only keep the components consisting of:
				// - more than one node
				// - one node only with an edge from the node to itself.
				if (scc.size() > 1 || this.isSingleLoop(scc.getFirst()))
					sccs.add(new Dpairs(scc));
			}
		}

		return sccs;
	}

	/**
	 * Depth first search in the subgraph of this graph having
	 * the specified set of nodes <code>sub</code>.
	 * 
	 * @param sub a subset of the nodes of this graph
	 * @return the list of nodes resulting from the search
	 */
	private Deque<RuleTrs> depthFirstSearch(Collection<RuleTrs> sub) {

		// The list of nodes that this method builds and returns.
		Deque<RuleTrs> result = new LinkedList<RuleTrs>();

		// We need to know whether a node has been visited yet.
		Set<RuleTrs> visited = new HashSet<RuleTrs>();

		// We visit each node that has not been visited yet.						
		for (RuleTrs R : sub)
			if (!visited.contains(R))
				this.visitForwards(R, sub, visited, result);

		return result;
	}

	/**
	 * Visits the specified node <code>R</code> forwards in
	 * the subgraph of this graph having the specified set
	 * of nodes <code>sub</code>. Then, inserts it at the
	 * beginning of the specified <code>result</code>.
	 * 
	 * Used in depth first search in a subgraph of this graph.
	 * 
	 * @param R the node to visit forwards
	 * @param sub a subset of the nodes of this graph
	 * @param visited the nodes that have been visited yet
	 * @param result the list of nodes resulting from the visit
	 */
	private void visitForwards(RuleTrs R, Collection<RuleTrs> sub,
			Set<RuleTrs> visited, Deque<RuleTrs> result) {

		visited.add(R);

		Dpairs succR = this.successors.get(R);
		if (succR != null)
			for (RuleTrs S : succR)
				if (!visited.contains(S) && sub.contains(S))
					this.visitForwards(S, sub, visited, result);

		result.addFirst(R);
	}

	/**
	 * Visits the specified node <code>R</code> backwards in
	 * the subgraph of this graph having the specified set
	 * of nodes <code>sub</code>. Then, inserts it at the
	 * beginning of the specified <code>scc</code>.
	 * 
	 * Used for computing the SCCs of the subgraph which
	 * consists of the specified nodes.
	 * 
	 * @param R the node to visit backwards
	 * @param sub a subset of the nodes of this graph
	 * @param visited the nodes that have been visited yet
	 * @param scc the list of nodes resulting from the visit
	 * and that form the SCC currently being computed
	 */
	private void visitBackwards(RuleTrs R,
			Collection<RuleTrs> sub,
			Set<RuleTrs> visited,
			Deque<RuleTrs> scc) {

		visited.add(R);

		Dpairs predR = this.predecessors.get(R);
		if (predR != null)
			for (RuleTrs P : predR)
				if (!visited.contains(P) && sub.contains(P))
					this.visitBackwards(P, sub, visited, scc);

		scc.addFirst(R);
	}
	
	/**
	 * Returns <code>true</code> iff the specified
	 * node is a single loop in this graph.
	 * 
	 * @param R a node to check
	 * @return <code>true</code> iff the specified
	 * node is a single loop in this graph
	 */
	private boolean isSingleLoop(RuleTrs R) {
		Dpairs succR = this.successors.get(R);
		return (succR != null && succR.contains(R));
	}

	/**
	 * Returns a String representation of this graph.
	 * 
	 * @return a String representation of this graph
	 */
	@Override
	public String toString() {
		StringBuffer s1 = new StringBuffer("** Nodes:\n");
		StringBuffer s2 = new StringBuffer("** Successors:\n");

		for (RuleTrs R : this.nodes) {
			String addr_e = "@" + Integer.toHexString(System.identityHashCode(R));
			s1.append(addr_e + ": " + R + "\n");
			s2.append(addr_e + " -> {");

			Dpairs succR = this.successors.get(R);
			if (succR != null) {
				boolean first = true;
				for (RuleTrs S : succR) {
					if (first) first = false;
					else s2.append(", ");
					s2.append("@" + Integer.toHexString(System.identityHashCode(S)));
				}
			}
			
			s2.append("}\n");
		}
		s1.append(s2);

		return s1.toString();
	}
}
