/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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

package fr.univreunion.nti.program.lp.binaryunfolding;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * Extends nontermination witnesses with binary rules.
 *
 * <p>The construction is from E. Payet and F. Mesnard,
 * <a href="https://doi.org/10.1145/1119479.1119481">Non-Termination
 * Inference of Logic Programs</a>, ACM Transactions on Programming
 * Languages and Systems 28(2), 256--289, 2006.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class WitnessExtender {

	/**
	 * This class cannot be instantiated.
	 */
	private WitnessExtender() {}

	/**
	 * Implements the function <code>loopsFromDict</code> of Payet and
	 * Mesnard (2006), cited in the class documentation.
	 * <p>
	 * This method builds the witnesses obtained by adding each
	 * binary rule to the witnesses of the given dictionary.
	 *
	 * @param binaryRules a list of binary unfolded rules
	 * @param loopDictionary a loop dictionary
	 * @return the new witnesses obtained from
	 * <code>loopDictionary</code> and <code>binaryRules</code>
	 */
	static List<NonTerminationWitness> extend(
			Iterable<BinaryRuleLp> binaryRules,
			Iterable<NonTerminationWitness> loopDictionary) {

		// The witnesses to return at the end.
		List<NonTerminationWitness> newWitnesses = new ArrayList<>();

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();

		WitnessIndex witnessIndex = null;
		for (BinaryRuleLp binaryRule : binaryRules) {
			if (currentThread.isInterrupted())
				return newWitnesses;

			if (witnessIndex == null) {
				witnessIndex = WitnessIndex.tryBuild(
						loopDictionary, currentThread);
				if (witnessIndex == null)
					return newWitnesses;
			}

			if (!witnessIndex.extendInOrder(
					binaryRule, newWitnesses, currentThread))
				return newWitnesses;
		}

		return newWitnesses;
	}

	/**
	 * An index of witnesses by the predicate relationships required for an
	 * extension. Every indexed witness retains its global dictionary position.
	 */
	private static final class WitnessIndex {

		/** Looping pairs grouped by the required candidate body predicate. */
		private final Map<FunctionSymbol, List<IndexedWitness>> loopingPairs =
				new HashMap<>();

		/** Incomplete recurrent pairs grouped by required candidate predicates. */
		private final Map<RulePredicates, List<IndexedWitness>> recurrentPairs =
				new HashMap<>();

		/** Unknown witness implementations which must still receive every rule. */
		private final List<IndexedWitness> otherWitnesses = new ArrayList<>();

		/** This class is built through {@link #tryBuild(Iterable, Thread)}. */
		private WitnessIndex() {}

		/**
		 * Builds an index, or returns <code>null</code> if interrupted.
		 *
		 * @param witnesses the witnesses to index
		 * @param currentThread the proof thread
		 * @return the completed index, or <code>null</code> if interrupted
		 */
		private static WitnessIndex tryBuild(
				Iterable<NonTerminationWitness> witnesses,
				Thread currentThread) {

			WitnessIndex result = new WitnessIndex();
			int position = 0;
			for (NonTerminationWitness witness : witnesses) {
				if (currentThread.isInterrupted())
					return null;
				result.add(new IndexedWitness(position++, witness));
			}
			return result;
		}

		/** Adds one witness to its compatible bucket. */
		private void add(IndexedWitness indexedWitness) {
			NonTerminationWitness witness = indexedWitness.witness();
			if (witness instanceof LoopingPair loopingPair &&
					loopingPair.getClass() == LoopingPair.class) {
				this.loopingPairs.computeIfAbsent(
						loopingPair.getRequiredBodyPredicateSymbol(),
						ignored -> new ArrayList<>()).add(indexedWitness);
				return;
			}

			if (witness instanceof RecurrentPairLp recurrentPair &&
					recurrentPair.getClass() == RecurrentPairLp.class) {
				FunctionSymbol requiredHead =
						recurrentPair.getRequiredHeadPredicateSymbol();
				if (requiredHead != null)
					this.recurrentPairs.computeIfAbsent(
							new RulePredicates(
								requiredHead,
								recurrentPair.getRequiredBodyPredicateSymbol()),
							ignored -> new ArrayList<>()).add(indexedWitness);
				return;
			}

			this.otherWitnesses.add(indexedWitness);
		}

		/**
		 * Extends compatible witnesses in their original dictionary order.
		 *
		 * @return <code>false</code> iff interrupted
		 */
		private boolean extendInOrder(
				BinaryRuleLp rule,
				List<NonTerminationWitness> extensions,
				Thread currentThread) {

			List<IndexedWitness> looping = this.loopingPairs.getOrDefault(
					rule.getBodyPredicateSymbol(), List.of());
			List<IndexedWitness> recurrent = this.recurrentPairs.getOrDefault(
					new RulePredicates(
						rule.getHeadPredicateSymbol(),
						rule.getBodyPredicateSymbol()),
					List.of());

			int loopingIndex = 0;
			int recurrentIndex = 0;
			int otherIndex = 0;
			while (loopingIndex < looping.size() ||
					recurrentIndex < recurrent.size() ||
					otherIndex < this.otherWitnesses.size()) {
				if (currentThread.isInterrupted())
					return false;

				int loopingPosition = positionAt(looping, loopingIndex);
				int recurrentPosition = positionAt(
						recurrent, recurrentIndex);
				int otherPosition = positionAt(
						this.otherWitnesses, otherIndex);

				IndexedWitness next;
				if (loopingPosition < recurrentPosition &&
						loopingPosition < otherPosition)
					next = looping.get(loopingIndex++);
				else if (recurrentPosition < otherPosition)
					next = recurrent.get(recurrentIndex++);
				else
					next = this.otherWitnesses.get(otherIndex++);

				NonTerminationWitness witness = next.witness();
				NonTerminationWitness extended = witness.add(rule);
				if (extended != witness)
					extensions.add(extended);
			}
			return true;
		}

		/** Returns the global position at an index, or the maximum value. */
		private static int positionAt(
				List<IndexedWitness> witnesses,
				int index) {
			return index < witnesses.size() ?
					witnesses.get(index).position() : Integer.MAX_VALUE;
		}
	}

	/** A witness paired with its stable dictionary position. */
	private record IndexedWitness(
			int position,
			NonTerminationWitness witness) {}

	/** The candidate head and body predicate symbols required by a witness. */
	private record RulePredicates(
			FunctionSymbol head,
			FunctionSymbol body) {}
}
