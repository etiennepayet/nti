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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.PrimitiveIterator;
import java.util.concurrent.CancellationException;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.ReadOnlyTermUnifier;
import fr.univreunion.nti.term.Term;

/**
 * An (estimated) dependency graph of a TRS.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DependencyGraph {

	/** Maximum number of arcs retained in one approximate dependency graph. */
	private static final int MAX_APPROXIMATE_ARC_COUNT = 100_000;

	/**
	 * The nodes of this graph.
	 */
	private final DependencyPairs nodes;

	/**
	 * The predecessors of each node of this graph.
	 * <p>
	 * Every node in this map belongs to the set of
	 * nodes of this graph.
	 */
	private final Map<RuleTrs, List<RuleTrs>> predecessors;

	/**
	 * The successors of each node of this graph.
	 * <p>
	 * Every node in this map belongs to the set of
	 * nodes of this graph.
	 */
	private final Map<RuleTrs, List<RuleTrs>> successors;

	/**
	 * The SCCs of this graph.
	 */
	private final Deque<DependencyPairs> sccs;

	/**
	 * Builds the estimated dependency graph of the specified TRS from the
	 * specified dependency pairs.
	 *
	 * @param trs a TRS whose estimated dependency graph has to be built
	 * @param dependencyPairs the dependency pairs used as nodes of this graph
	 */
	public DependencyGraph(Trs trs, DependencyPairs dependencyPairs) {
		// The nodes of this graph are the specified dependency pairs.
		this.nodes = dependencyPairs;

		// We first build an over-approximation of the arcs
		// of this graph.
		ApproximateArcs approximateArcs = this.buildApproximateArcs(trs);

		// Then, we build the SCCs of this graph from
		// the above over-approximation.
		this.sccs = new DependencyGraphSccComputer().compute(
				this.nodes,
				approximateArcs.predecessors(),
				approximateArcs.successors());

		// The SCC computation filtered the approximate adjacency lists in place.
		// They are now the final arcs of this graph and can be retained directly.
		this.predecessors = approximateArcs.predecessors();
		this.successors = approximateArcs.successors();

		// From now on, this graph consists of disconnected
		// SCCs: there is no more arc between any node of
		// an SCC to any node of another SCC.
	}

	/**
	 * Returns a collection consisting of the SCCs of this graph.
	 *
	 * @return the SCCs of this graph
	 */
	public Deque<DependencyPairs> getSCCs() {
		return this.sccs;
	}

	/**
	 * Builds an over-approximation of the arcs of this graph.
	 *
	 * @param trs the TRS used to check whether two dependency pairs may be
	 * connected
	 * @return the computed over-approximation of the arcs of this graph
	 */
	private ApproximateArcs buildApproximateArcs(Trs trs) {
		Map<RuleTrs, List<RuleTrs>> approximatePredecessors = new HashMap<>();
		Map<RuleTrs, List<RuleTrs>> approximateSuccessors = new HashMap<>();
		DependencyPairTargetIndex targetIndex =
				new DependencyPairTargetIndex(this.nodes);
		List<List<RuleTrs>> predecessorsByTargetIndex =
				new ArrayList<>(this.nodes.size());
		for (int targetIndexNumber = 0;
			 targetIndexNumber < this.nodes.size();
			 targetIndexNumber++)
			predecessorsByTargetIndex.add(null);

		int approximateArcCount = 0;
		for (RuleTrs source : this.nodes) {
			ensureNotInterrupted();
			List<RuleTrs> sourceSuccessors = buildApproximateArcsFromSource(
					source,
					trs,
					targetIndex,
					predecessorsByTargetIndex,
					approximatePredecessors,
					MAX_APPROXIMATE_ARC_COUNT - approximateArcCount);
			if (sourceSuccessors != null) {
				approximateArcCount += sourceSuccessors.size();
				approximateSuccessors.put(source, sourceSuccessors);
			}
		}

		return new ApproximateArcs(
				approximatePredecessors, approximateSuccessors);
	}

	/**
	 * Builds the approximate outgoing arcs of one source and records the
	 * corresponding incoming arcs.
	 *
	 * @param source the source dependency pair
	 * @param trs the TRS used for connectability
	 * @param targetIndex the indexed dependency-pair targets
	 * @param predecessorsByTargetIndex predecessor lists by stable target index
	 * @param approximatePredecessors the predecessor map to complete
	 * @param remainingArcCapacity the number of further arcs that may be retained
	 * @return the source successors, or <code>null</code> if there are none
	 * @throws DependencyGraphLimitException if one more arc would exceed the
	 * resource bound
	 */
	private static List<RuleTrs> buildApproximateArcsFromSource(
			RuleTrs source,
			Trs trs,
			DependencyPairTargetIndex targetIndex,
			List<List<RuleTrs>> predecessorsByTargetIndex,
			Map<RuleTrs, List<RuleTrs>> approximatePredecessors,
			int remainingArcCapacity) {

		Term connectabilityPattern =
				source.getRight().buildConnectabilityPattern(trs);
		boolean variableSource = connectabilityPattern.isVariable();
		boolean allSourceFunctionsIndexed =
				targetIndex.coversAllFunctionPositions(connectabilityPattern);
		ReadOnlyTermUnifier unifier = null;
		List<RuleTrs> sourceSuccessors = null;
		DependencyPairTargetIndex.CandidateSelection candidateSelection =
				targetIndex.candidateSelectionFor(connectabilityPattern);
		PrimitiveIterator.OfInt candidateIndexes =
				candidateSelection.indexes();
		while (candidateIndexes.hasNext()) {
			int targetIndexNumber = candidateIndexes.nextInt();
			RuleTrs target = targetIndex.targetAt(targetIndexNumber);
			ensureNotInterrupted();
			// The connectability pattern is fresh, linear and variable-disjoint
			// from every target. If all its function positions were indexed,
			// structural compatibility leaves only equalities induced by repeated
			// target variables. Such an equality cannot fail when at most one of
			// its occurrences faces a source function subterm.
			boolean unifiable = variableSource ||
					allSourceFunctionsIndexed &&
							candidateSelection.hasNoRepeatedVariableConflict(
									targetIndexNumber);
			if (!unifiable) {
				if (unifier == null)
					unifier = ReadOnlyTermUnifier.forFreshLinearSource(
							connectabilityPattern);
				unifiable = unifier.isUnifiableWith(target.getLeft());
			}
			if (!unifiable)
				continue;

			ensureArcCapacity(remainingArcCapacity, sourceSuccessors);

			if (sourceSuccessors == null)
				sourceSuccessors = new ArrayList<>();
			sourceSuccessors.add(target);

			predecessorsForTarget(
					targetIndexNumber,
					target,
					predecessorsByTargetIndex,
					approximatePredecessors).add(source);
		}
		return sourceSuccessors;
	}

	/** Fails before one more arc would exceed the graph resource bound. */
	private static void ensureArcCapacity(
			int remainingArcCapacity, List<RuleTrs> sourceSuccessors) {

		int sourceArcCount = sourceSuccessors == null
				? 0 : sourceSuccessors.size();
		if (remainingArcCapacity <= sourceArcCount)
			throw new DependencyGraphLimitException(
					MAX_APPROXIMATE_ARC_COUNT);
	}

	/** Returns the lazily created predecessor list for one indexed target. */
	private static List<RuleTrs> predecessorsForTarget(
			int targetIndexNumber,
			RuleTrs target,
			List<List<RuleTrs>> predecessorsByTargetIndex,
			Map<RuleTrs, List<RuleTrs>> approximatePredecessors) {

		List<RuleTrs> targetPredecessors =
				predecessorsByTargetIndex.get(targetIndexNumber);
		if (targetPredecessors == null) {
			targetPredecessors = new ArrayList<>();
			predecessorsByTargetIndex.set(
					targetIndexNumber, targetPredecessors);
			approximatePredecessors.put(target, targetPredecessors);
		}
		return targetPredecessors;
	}

	/** Stops graph construction when its worker has been cancelled. */
	private static void ensureNotInterrupted() {
		if (Thread.currentThread().isInterrupted())
			throw new CancellationException(
					"dependency graph construction interrupted");
	}

	/**
	 * An over-approximation of the arcs of a dependency graph.
	 */
	private record ApproximateArcs(
			Map<RuleTrs, List<RuleTrs>> predecessors,
			Map<RuleTrs, List<RuleTrs>> successors) {}

	/**
	 * Returns the SCCs of the subgraph which consists of
	 * the specified nodes.
	 *
	 * @param sub a subset of the nodes of this graph
	 * @return the SCCs of the subgraph which consists of the
	 * specified nodes
	 */
	public Deque<DependencyPairs> getSCCs(Collection<RuleTrs> sub) {
		return new DependencyGraphSccComputer()
				.compute(sub, this.predecessors, this.successors);
	}

	/**
	 * Returns a String representation of this graph.
	 *
	 * @return a String representation of this graph
	 */
	@Override
	public String toString() {
		StringBuilder s1 = new StringBuilder("** Nodes:\n");
		StringBuilder s2 = new StringBuilder("** Successors:\n");

		for (RuleTrs node : this.nodes) {
			String nodeAddress =
					"@" + Integer.toHexString(System.identityHashCode(node));
			s1.append(nodeAddress).append(": ").append(node).append("\n");
			s2.append(nodeAddress).append(" -> {");

			List<RuleTrs> nodeSuccessors = this.successors.get(node);
			if (nodeSuccessors != null) {
				boolean first = true;
				for (RuleTrs successor : nodeSuccessors) {
					if (first) first = false;
					else s2.append(", ");
					s2.append("@")
							.append(Integer.toHexString(System.identityHashCode(successor)));
				}
			}

			s2.append("}\n");
		}
		s1.append(s2);

		return s1.toString();
	}
}
