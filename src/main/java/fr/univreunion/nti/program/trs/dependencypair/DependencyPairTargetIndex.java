/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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
import java.util.BitSet;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.PrimitiveIterator;
import java.util.concurrent.CancellationException;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Indexes dependency-pair targets by their root and function symbols down to
 * depth two. Variables at an indexed position or one of its indexed ancestors
 * are retained as wildcards.
 */
final class DependencyPairTargetIndex {

	/** Maximum depth of function positions represented by this index. */
	private static final int MAX_INDEXED_DEPTH = 2;

	/** The indexed targets in dependency-pair order. */
	private final List<RuleTrs> targets = new ArrayList<>();

	/** The target indexes grouped by left-hand-side root symbol. */
	private final Map<FunctionSymbol, RootIndex> targetsByRoot = new HashMap<>();

	/**
	 * Builds an index for the specified dependency-pair targets.
	 *
	 * @param targets the targets to index
	 */
	DependencyPairTargetIndex(DependencyPairs targets) {
		for (RuleTrs target : targets) {
			ensureNotInterrupted();
			int targetIndex = this.targets.size();
			this.targets.add(target);
			Function left = target.getLeft();
			RootIndex rootIndex = this.targetsByRoot.computeIfAbsent(
					left.getRootSymbol(), key -> new RootIndex());
			rootIndex.targetIndexes.set(targetIndex);
			Map<Variable, List<ArgumentPosition>> variablePositions =
					new IdentityHashMap<>();

			int arity = left.getRootSymbol().getArity();
			for (int argumentIndex = 0;
					argumentIndex < arity;
					argumentIndex++) {
				Term argument = left.get(argumentIndex);
				ArgumentPosition position = ArgumentPosition.direct(argumentIndex);
				indexArgument(
						rootIndex, position, argument, targetIndex,
						variablePositions);
				if (argument instanceof Function argumentFunction) {
					int argumentArity = argumentFunction.getRootSymbol().getArity();
					for (int childIndex = 0;
							childIndex < argumentArity;
							childIndex++)
						indexArgument(
								rootIndex,
								position.child(childIndex),
								argumentFunction.get(childIndex),
								targetIndex,
								variablePositions);
				}
			}
			indexRepeatedVariableConflicts(
					rootIndex, variablePositions, targetIndex);
		}
	}

	/** Indexes one target argument at the specified position. */
	private static void indexArgument(
			RootIndex rootIndex,
			ArgumentPosition position,
			Term argument,
			int targetIndex,
			Map<Variable, List<ArgumentPosition>> variablePositions) {

		if (argument instanceof Variable variable) {
			rootIndex.variableArguments.computeIfAbsent(
					position, key -> new BitSet()).set(targetIndex);
			variablePositions.computeIfAbsent(
					variable, key -> new ArrayList<>()).add(position);
		}
		else
			rootIndex.functionArguments.computeIfAbsent(
					new ArgumentSymbol(position, argument.getRootSymbol()),
					key -> new BitSet()).set(targetIndex);
	}

	/** Indexes pairs of positions occupied by the same target variable. */
	private static void indexRepeatedVariableConflicts(
			RootIndex rootIndex,
			Map<Variable, List<ArgumentPosition>> variablePositions,
			int targetIndex) {

		for (List<ArgumentPosition> positions : variablePositions.values())
			for (int firstIndex = 0;
				 firstIndex < positions.size();
				 firstIndex++)
				for (int secondIndex = firstIndex + 1;
					 secondIndex < positions.size();
					 secondIndex++)
					rootIndex.repeatedVariableConflicts.computeIfAbsent(
							new PositionPair(
									positions.get(firstIndex),
									positions.get(secondIndex)),
							key -> new BitSet()).set(targetIndex);
	}

	/**
	 * Returns the structurally compatible targets and the targets for which
	 * repeated variables impose potentially conflicting source constraints.
	 *
	 * @param pattern a connectability pattern
	 * @return the candidate selection for the pattern
	 */
	CandidateSelection candidateSelectionFor(Term pattern) {
		if (pattern.isVariable()) {
			BitSet allTargetIndexes = new BitSet();
			allTargetIndexes.set(0, this.targets.size());
			return new CandidateSelection(allTargetIndexes, null);
		}
		if (!(pattern instanceof Function function))
			return new CandidateSelection(new BitSet(), null);

		RootIndex rootIndex = this.targetsByRoot.get(function.getRootSymbol());
		if (rootIndex == null)
			return new CandidateSelection(new BitSet(), null);

		BitSet candidateIndexes = (BitSet) rootIndex.targetIndexes.clone();
		int arity = function.getRootSymbol().getArity();
		for (int argumentIndex = 0;
				argumentIndex < arity && !candidateIndexes.isEmpty();
				argumentIndex++)
			retainCompatibleArgument(
					candidateIndexes,
					rootIndex,
					argumentIndex,
					function.get(argumentIndex));

		return new CandidateSelection(
				candidateIndexes,
				repeatedVariableConflictsFor(function, rootIndex));
	}

	/**
	 * Returns the target having the specified stable index.
	 *
	 * @param targetIndex the target index
	 * @return the target having the specified index
	 */
	RuleTrs targetAt(int targetIndex) {
		return this.targets.get(targetIndex);
	}

	/**
	 * Returns whether every function position of the specified pattern is
	 * covered by this index.
	 *
	 * @param pattern the pattern to inspect
	 * @return <code>true</code> iff every function position is indexed
	 */
	boolean coversAllFunctionPositions(Term pattern) {
		return coversAllFunctionPositions(pattern, MAX_INDEXED_DEPTH);
	}

	/** Returns whether all function positions fit within the remaining depth. */
	private static boolean coversAllFunctionPositions(Term term, int depth) {
		if (term.isVariable())
			return true;
		if (!(term instanceof Function function) || depth < 0)
			return false;

		int arity = function.getRootSymbol().getArity();
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++)
			if (!coversAllFunctionPositions(
					function.getChild(argumentIndex), depth - 1))
				return false;
		return true;
	}

	/** Returns conflicts activated by function positions of the source. */
	private static BitSet repeatedVariableConflictsFor(
			Function source,
			RootIndex rootIndex) {

		if (rootIndex.repeatedVariableConflicts.isEmpty())
			return null;

		List<ArgumentPosition> functionPositions =
				indexedFunctionPositionsOf(source);
		BitSet conflicts = null;
		for (int firstIndex = 0;
			 firstIndex < functionPositions.size();
			 firstIndex++)
			for (int secondIndex = firstIndex + 1;
				 secondIndex < functionPositions.size();
				 secondIndex++) {
				BitSet pairConflicts = rootIndex.repeatedVariableConflicts.get(
						new PositionPair(
								functionPositions.get(firstIndex),
								functionPositions.get(secondIndex)));
				if (pairConflicts != null) {
					if (conflicts == null)
						conflicts = (BitSet) pairConflicts.clone();
					else
						conflicts.or(pairConflicts);
				}
			}
		return conflicts;
	}

	/** Returns the indexed positions occupied by source functions. */
	private static List<ArgumentPosition> indexedFunctionPositionsOf(
			Function source) {

		List<ArgumentPosition> result = new ArrayList<>();
		int arity = source.getRootSymbol().getArity();
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++) {
			Term argument = source.getChild(argumentIndex);
			if (argument instanceof Function argumentFunction) {
				ArgumentPosition position =
						ArgumentPosition.direct(argumentIndex);
				result.add(position);
				int argumentArity =
						argumentFunction.getRootSymbol().getArity();
				for (int childIndex = 0;
					 childIndex < argumentArity;
					 childIndex++)
					if (argumentFunction.getChild(childIndex)
							instanceof Function)
						result.add(position.child(childIndex));
			}
		}
		return result;
	}

	/** Retains targets compatible with one direct pattern argument. */
	private static void retainCompatibleArgument(
			BitSet candidateIndexes,
			RootIndex rootIndex,
			int argumentIndex,
			Term argument) {

		if (argument.isVariable())
			return;

		ArgumentPosition position = ArgumentPosition.direct(argumentIndex);
		retainCompatibleArguments(
				candidateIndexes,
				rootIndex,
				position,
				argument.getRootSymbol());
		if (argument instanceof Function argumentFunction)
			retainCompatibleChildren(
					candidateIndexes, rootIndex, position, argumentFunction);
	}

	/** Retains targets compatible with the children of one pattern argument. */
	private static void retainCompatibleChildren(
			BitSet candidateIndexes,
			RootIndex rootIndex,
			ArgumentPosition parentPosition,
			Function argument) {

		int arity = argument.getRootSymbol().getArity();
		for (int childIndex = 0;
				childIndex < arity && !candidateIndexes.isEmpty();
				childIndex++) {
			Term child = argument.get(childIndex);
			if (!child.isVariable())
				retainCompatibleArguments(
						candidateIndexes,
						rootIndex,
						parentPosition.child(childIndex),
						child.getRootSymbol());
		}
	}

	/** Retains targets having a wildcard or the specified argument symbol. */
	private static void retainCompatibleArguments(
			BitSet candidateIndexes,
			RootIndex rootIndex,
			ArgumentPosition position,
			FunctionSymbol argumentSymbol) {

		BitSet sameSymbol = rootIndex.functionArguments.get(
				new ArgumentSymbol(position, argumentSymbol));
		BitSet variables = rootIndex.variableArguments.get(position);
		BitSet ancestorVariables = position.isDirect()
				? null
				: rootIndex.variableArguments.get(position.parent());

		BitSet compatible = null;
		if (sameSymbol != null)
			compatible = (BitSet) sameSymbol.clone();
		if (variables != null) {
			if (compatible == null)
				compatible = (BitSet) variables.clone();
			else
				compatible.or(variables);
		}
		if (ancestorVariables != null) {
			if (compatible == null)
				compatible = (BitSet) ancestorVariables.clone();
			else
				compatible.or(ancestorVariables);
		}

		if (compatible == null)
			candidateIndexes.clear();
		else
			candidateIndexes.and(compatible);
	}

	/** Stops index construction when its worker has been cancelled. */
	private static void ensureNotInterrupted() {
		if (Thread.currentThread().isInterrupted())
			throw new CancellationException(
					"dependency graph construction interrupted");
	}

	/** Index data for targets having one common root symbol. */
	private static final class RootIndex {

		/** All targets having this root symbol. */
		private final BitSet targetIndexes = new BitSet();

		/** Targets having a variable at each indexed position. */
		private final Map<ArgumentPosition, BitSet> variableArguments =
				new HashMap<>();

		/** Targets having a function symbol at each indexed position. */
		private final Map<ArgumentSymbol, BitSet> functionArguments =
				new HashMap<>();

		/** Targets sharing one variable at each pair of indexed positions. */
		private final Map<PositionPair, BitSet> repeatedVariableConflicts =
				new HashMap<>();
	}

	/** Candidate indexes and repeated-variable conflicts for one source. */
	static final class CandidateSelection {

		/** Structurally compatible targets. */
		private final BitSet candidateIndexes;

		/** Targets constrained at two source function positions. */
		private final BitSet repeatedVariableConflicts;

		private CandidateSelection(
				BitSet candidateIndexes,
				BitSet repeatedVariableConflicts) {
			this.candidateIndexes = candidateIndexes;
			this.repeatedVariableConflicts = repeatedVariableConflicts;
		}

		/** Returns the compatible target indexes in ascending order. */
		PrimitiveIterator.OfInt indexes() {
			return selectedIndexes(this.candidateIndexes);
		}

		/**
		 * Returns whether repeated target variables impose no potentially
		 * conflicting equality between source function subterms.
		 */
		boolean hasNoRepeatedVariableConflict(int targetIndex) {
			return this.repeatedVariableConflicts == null ||
					!this.repeatedVariableConflicts.get(targetIndex);
		}

		/** Returns a primitive iterator over selected ascending indexes. */
		private static PrimitiveIterator.OfInt selectedIndexes(BitSet indexes) {
			return new PrimitiveIterator.OfInt() {

				private int nextIndex = indexes.nextSetBit(0);

				@Override
				public boolean hasNext() {
					return this.nextIndex >= 0;
				}

				@Override
				public int nextInt() {
					if (this.nextIndex < 0)
						throw new NoSuchElementException();
					int result = this.nextIndex;
					this.nextIndex = indexes.nextSetBit(this.nextIndex + 1);
					return result;
				}
			};
		}
	}

	/**
	 * An indexed position below the root. A negative child index denotes a
	 * direct-argument position.
	 */
	private record ArgumentPosition(
			int argumentIndex, int childIndex) {

		/** Child-index marker used for a direct argument of the root. */
		private static final int DIRECT_ARGUMENT_CHILD_INDEX = -1;

		private static ArgumentPosition direct(int argumentIndex) {
			return new ArgumentPosition(
					argumentIndex, DIRECT_ARGUMENT_CHILD_INDEX);
		}

		private ArgumentPosition child(int childIndex) {
			return new ArgumentPosition(this.argumentIndex, childIndex);
		}

		private boolean isDirect() {
			return this.childIndex < 0;
		}

		private ArgumentPosition parent() {
			return direct(this.argumentIndex);
		}
	}

	/** An indexed argument position and its function symbol. */
	private record ArgumentSymbol(
			ArgumentPosition position, FunctionSymbol functionSymbol) {}

	/** Two indexed positions occupied by the same target variable. */
	private record PositionPair(
			ArgumentPosition first, ArgumentPosition second) {}

}
