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

package fr.univreunion.nti.program.trs.dependencypair;

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CancellationException;

import fr.univreunion.nti.program.trs.RuleTrs;

/**
 * Computes strongly connected components for dependency graphs and dependency
 * subgraphs.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
class DependencyGraphSccComputer {

	/**
	 * Builds the SCCs of a temporary graph having the specified set of nodes
	 * and the specified arcs.
	 *
	 * @param nodes the nodes of the graph
	 * @param predecessors the predecessors of the nodes of the graph
	 * @param successors the successors of the nodes of the graph
	 * @return a list consisting of the SCCs of the graph
	 */
	Deque<DependencyPairs> compute(
			DependencyPairs nodes,
			Map<RuleTrs, List<RuleTrs>> predecessors,
			Map<RuleTrs, List<RuleTrs>> successors) {

		SccComputation computation = this.computeComponents(
				nodes,
				predecessors,
				successors,
				null);

		this.retainIntraComponentArcs(
				predecessors, computation.componentIds());
		this.retainIntraComponentArcs(
				successors, computation.componentIds());

		return this.wrapAsDependencyPairs(computation.cyclicComponents());
	}

	/**
	 * Builds the SCCs of the subgraph which consists of the specified nodes.
	 *
	 * @param sub a subset of the nodes of this graph
	 * @param predecessors the predecessors of each node of the graph
	 * @param successors the successors of each node of the graph
	 * @return the SCCs of the subgraph which consists of the specified nodes
	 */
	Deque<DependencyPairs> compute(
			Collection<RuleTrs> sub,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> predecessors,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> successors) {

		return this.wrapAsDependencyPairs(
				this.computeComponents(sub, predecessors, successors, sub)
						.cyclicComponents());
	}

	/**
	 * Builds the SCCs of a graph having the specified set of nodes and the
	 * specified arcs.
	 *
	 * @param nodes the nodes to start from
	 * @param predecessors the predecessors of the nodes of the graph
	 * @param successors the successors of the nodes of the graph
	 * @param allowedNodes the nodes allowed in the computed SCCs,
	 * or <code>null</code> if all nodes are allowed
	 * @return the cyclic SCCs of the graph and the component identifier of each
	 * visited node
	 */
	private SccComputation computeComponents(
			Iterable<RuleTrs> nodes,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> predecessors,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> successors,
			Collection<RuleTrs> allowedNodes) {

		// The list to return at the end.
		Deque<Deque<RuleTrs>> sccs = new LinkedList<>();

		// First, we perform a depth first search in this graph.
		Deque<RuleTrs> finishOrder =
				this.depthFirstSearch(nodes, successors, allowedNodes);

		// Then, we perform a depth first search in the
		// transpose graph, but we consider the nodes
		// in their computed finish order.

		// We need to know whether a node has been visited yet.
		Set<RuleTrs> visited = new HashSet<>();
		Map<RuleTrs, Integer> componentIds = new HashMap<>();
		int componentId = 0;

		for (RuleTrs node : finishOrder) {
			if (!visited.contains(node)) {
				Deque<RuleTrs> scc = new LinkedList<>();
				this.visitBackwards(
						node, predecessors, allowedNodes, visited, scc);
				for (RuleTrs componentNode : scc) {
					ensureNotInterrupted();
					componentIds.put(componentNode, componentId);
				}
				// We only keep the components consisting of:
				// - more than one node
				// - one node only with an edge from the node to itself.
				if (scc.size() > 1 || this.isSingleLoop(scc.getFirst(), successors))
					sccs.add(scc);
				componentId++;
			}
		}

		return new SccComputation(sccs, componentIds);
	}

	/**
	 * Wraps each of the specified SCCs as a collection of dependency pairs.
	 *
	 * @param sccs the SCCs to wrap
	 * @return the SCCs wrapped as collections of dependency pairs
	 */
	private Deque<DependencyPairs> wrapAsDependencyPairs(
			Deque<Deque<RuleTrs>> sccs) {
		Deque<DependencyPairs> result = new LinkedList<>();

		for (Deque<RuleTrs> scc : sccs)
			result.add(new DependencyPairs(scc));

		return result;
	}

	/**
	 * Depth first search in a graph having the specified set of nodes and the
	 * specified outgoing arcs.
	 *
	 * @param nodes the nodes to start from
	 * @param successors the successors of the nodes of the graph
	 * @param allowedNodes the nodes allowed in the search,
	 * or <code>null</code> if all nodes are allowed
	 * @return the list of nodes resulting from the search
	 */
	private Deque<RuleTrs> depthFirstSearch(
			Iterable<RuleTrs> nodes,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> successors,
			Collection<RuleTrs> allowedNodes) {

		// The list of nodes that this method builds and returns.
		Deque<RuleTrs> result = new LinkedList<>();

		// We need to know whether a node has been visited yet.
		Set<RuleTrs> visited = new HashSet<>();

		// We visit each node that has not been visited yet.
		for (RuleTrs node : nodes) {
			ensureNotInterrupted();
			if (!visited.contains(node))
				this.visitForwards(
						node, successors, allowedNodes, visited, result);
		}

		return result;
	}

	/**
	 * Visits the specified node forwards in a graph having the specified set of
	 * outgoing arcs <code>successors</code>. Then, inserts it at the beginning
	 * of the specified <code>result</code>.
	 * <p>
	 * Used in depth first search.
	 *
	 * @param node the node to visit forwards
	 * @param successors the successors of the nodes of the graph
	 * @param allowedNodes the nodes allowed in the search,
	 * or <code>null</code> if all nodes are allowed
	 * @param visited the nodes that have been visited yet
	 * @param result the list of nodes resulting from the visit
	 */
	private void visitForwards(
			RuleTrs node,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> successors,
			Collection<RuleTrs> allowedNodes,
			Set<RuleTrs> visited,
			Deque<RuleTrs> result) {

		ensureNotInterrupted();
		visited.add(node);

		Iterable<RuleTrs> nodeSuccessors = successors.get(node);
		if (nodeSuccessors != null)
			for (RuleTrs successor : nodeSuccessors)
				if (!visited.contains(successor) &&
						this.isAllowed(successor, allowedNodes))
					this.visitForwards(
							successor, successors, allowedNodes, visited, result);

		result.addFirst(node);
	}

	/**
	 * Visits the specified node backwards in a graph having the specified set of
	 * incoming arcs <code>predecessors</code>. Then, inserts it at the beginning
	 * of the specified <code>scc</code>.
	 * <p>
	 * Used for computing the SCCs.
	 *
	 * @param node the node to visit backwards
	 * @param predecessors the predecessors of the nodes of the graph
	 * @param allowedNodes the nodes allowed in the search,
	 * or <code>null</code> if all nodes are allowed
	 * @param visited the nodes that have been visited yet
	 * @param scc the list of nodes resulting from the visit and that form the
	 * SCC currently being computed
	 */
	private void visitBackwards(
			RuleTrs node,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> predecessors,
			Collection<RuleTrs> allowedNodes,
			Set<RuleTrs> visited,
			Deque<RuleTrs> scc) {

		ensureNotInterrupted();
		visited.add(node);

		Iterable<RuleTrs> nodePredecessors = predecessors.get(node);
		if (nodePredecessors != null)
			for (RuleTrs predecessor : nodePredecessors)
				if (!visited.contains(predecessor) &&
						this.isAllowed(predecessor, allowedNodes))
					this.visitBackwards(
							predecessor, predecessors, allowedNodes, visited, scc);

		scc.addFirst(node);
	}

	/**
	 * Removes every arc whose endpoints belong to different SCCs.
	 * <p>
	 * Each adjacency list is filtered independently in one pass, without
	 * searching for and removing reciprocal arcs.
	 *
	 * @param arcs the adjacency lists to filter
	 * @param componentIds the component identifier of each node
	 */
	private void retainIntraComponentArcs(
			Map<RuleTrs, List<RuleTrs>> arcs,
			Map<RuleTrs, Integer> componentIds) {

		for (Map.Entry<RuleTrs, List<RuleTrs>> entry : arcs.entrySet()) {
			ensureNotInterrupted();
			Integer componentId = componentIds.get(entry.getKey());
			entry.getValue().removeIf(adjacentNode -> {
				ensureNotInterrupted();
				return componentId == null ||
						!componentId.equals(componentIds.get(adjacentNode));
			});
		}
	}

	/** Stops SCC computation when its worker has been cancelled. */
	private static void ensureNotInterrupted() {
		if (Thread.currentThread().isInterrupted())
			throw new CancellationException(
					"dependency graph construction interrupted");
	}

	/**
	 * Returns <code>true</code> iff the specified node is allowed.
	 *
	 * @param node the node to check
	 * @param allowedNodes the allowed nodes, or <code>null</code> if all nodes
	 * are allowed
	 * @return <code>true</code> iff the specified node is allowed
	 */
	private boolean isAllowed(
			RuleTrs node, Collection<RuleTrs> allowedNodes) {
		return allowedNodes == null || allowedNodes.contains(node);
	}

	/**
	 * Returns <code>true</code> iff the specified node is a single loop w.r.t.
	 * the specified outgoing arcs.
	 *
	 * @param node a node to check
	 * @param successors some outgoing arcs
	 * @return <code>true</code> iff the specified node is a single loop w.r.t.
	 * the specified outgoing arcs
	 */
	private boolean isSingleLoop(
			RuleTrs node,
			Map<RuleTrs, ? extends Iterable<RuleTrs>> successors) {
		Iterable<RuleTrs> nodeSuccessors = successors.get(node);
		if (nodeSuccessors == null)
			return false;
		for (RuleTrs successor : nodeSuccessors)
			if (successor == node || successor.equals(node))
				return true;
		return false;
	}

	/** The result of one complete SCC traversal. */
	private record SccComputation(
			Deque<Deque<RuleTrs>> cyclicComponents,
			Map<RuleTrs, Integer> componentIds) {}
}
