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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;

/**
 * A small nondeterministic bottom-up finite tree automaton.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class FiniteTreeAutomaton {

	/** Number of automaton states. */
	private final int stateCount;
	/** Immutable set of accepting states. */
	private final Set<Integer> finalStates;
	/** Immutable list of bottom-up transitions. */
	private final List<Transition> transitions;
	/** Transition-source index mapping to all nondeterministic targets. */
	private final Map<TransitionSource, BitSet> targets = new HashMap<>();

	/**
	 * Creates an automaton and indexes its transitions.
	 *
	 * @param stateCount number of states, numbered from zero
	 * @param finalStates accepting states
	 * @param transitions bottom-up transitions
	 * @throws IllegalArgumentException if a state or transition is invalid
	 */
	FiniteTreeAutomaton(
			int stateCount,
			Set<Integer> finalStates,
			List<Transition> transitions) {

		if (stateCount <= 0)
			throw new IllegalArgumentException("a tree automaton needs states");
		this.stateCount = stateCount;
		this.finalStates = Set.copyOf(finalStates);
		this.transitions = List.copyOf(transitions);

		for (int state : this.finalStates)
			checkState(state);
		for (Transition transition : this.transitions) {
			if (transition.arguments().size() !=
					transition.symbol().getArity())
				throw new IllegalArgumentException("transition arity mismatch");
			for (int state : transition.arguments())
				checkState(state);
			checkState(transition.result());
			this.targets.computeIfAbsent(
					new TransitionSource(
							transition.symbol(), transition.arguments()),
					ignored -> new BitSet(stateCount))
					.set(transition.result());
		}
	}

	/**
	 * Returns the number of states.
	 *
	 * @return the state count
	 */
	int stateCount() {
		return this.stateCount;
	}

	/**
	 * Returns the accepting states.
	 *
	 * @return an immutable set of final states
	 */
	Set<Integer> finalStates() {
		return this.finalStates;
	}

	/**
	 * Returns the bottom-up transitions.
	 *
	 * @return an immutable transition list
	 */
	List<Transition> transitions() {
		return this.transitions;
	}

	/**
	 * Looks up all targets of a transition source.
	 *
	 * @param symbol transition symbol
	 * @param arguments source states, in argument order
	 * @return a defensive bit-set copy of the target states
	 */
	BitSet targets(FunctionSymbol symbol, List<Integer> arguments) {
		BitSet result = this.targets.get(
				new TransitionSource(symbol, arguments));
		return result == null ? new BitSet(this.stateCount) :
				(BitSet) result.clone();
	}

	/**
	 * Returns a ground term accepted by this automaton, if one exists.
	 *
	 * @return an accepted ground witness, or {@code null} for an empty language
	 */
	Term acceptedTermWitness() {
		Map<Integer, Term> witnesses = reachableStateWitnesses();
		Term witness = null;
		for (int state : this.finalStates) {
			Term candidate = witnesses.get(state);
			if (candidate != null &&
					(witness == null || candidate.depth() < witness.depth()))
				witness = candidate;
		}
		return witness;
	}

	/**
	 * Computes one ground witness for every reachable state.
	 *
	 * @return a state-to-witness map in discovery order
	 */
	Map<Integer, Term> reachableStateWitnesses() {
		Map<Integer, Term> witnesses = new LinkedHashMap<>();
		boolean changed;
		do {
			changed = false;
			for (Transition transition : this.transitions) {
				List<Term> arguments = new ArrayList<>(
						transition.arguments().size());
				boolean argumentsReachable = true;
				for (int state : transition.arguments()) {
					Term argument = witnesses.get(state);
					if (argument == null) {
						argumentsReachable = false;
						break;
					}
					arguments.add(argument);
				}
				if (argumentsReachable &&
						!witnesses.containsKey(transition.result())) {
					witnesses.put(transition.result(), new Function(
							transition.symbol(), arguments));
					changed = true;
				}
			}
		}
		while (changed);
		return witnesses;
	}

	/**
	 * Evaluates a ground term and returns all possible root states.
	 *
	 * @param term ground term to evaluate
	 * @return the set of states reachable at the term root
	 */
	BitSet evaluate(Term term) {
		if (!(term instanceof Function function))
			return new BitSet(this.stateCount);

		List<BitSet> childStates = new ArrayList<>(
				function.getRootSymbol().getArity());
		for (int index = 0;
				index < function.getRootSymbol().getArity(); index++)
			childStates.add(evaluate(function.getChild(index)));

		BitSet result = new BitSet(this.stateCount);
		enumerateStateTuples(childStates, 0, new ArrayList<>(), arguments ->
				result.or(targets(function.getRootSymbol(), arguments)));
		return result;
	}

	/**
	 * Enumerates one state from every child-state set.
	 *
	 * @param choices possible states for each child
	 * @param index next child position to enumerate
	 * @param current tuple prefix under construction
	 * @param consumer consumer invoked for each complete tuple
	 */
	private static void enumerateStateTuples(
			List<BitSet> choices,
			int index,
			List<Integer> current,
			java.util.function.Consumer<List<Integer>> consumer) {

		if (index == choices.size()) {
			consumer.accept(List.copyOf(current));
			return;
		}
		BitSet states = choices.get(index);
		for (int state = states.nextSetBit(0);
				state >= 0; state = states.nextSetBit(state + 1)) {
			current.add(state);
			enumerateStateTuples(choices, index + 1, current, consumer);
			current.removeLast();
		}
	}

	/**
	 * Checks that a state belongs to this automaton.
	 *
	 * @param state state number to check
	 * @throws IllegalArgumentException if the state is outside the state space
	 */
	private void checkState(int state) {
		if (state < 0 || this.stateCount <= state)
			throw new IllegalArgumentException("invalid automaton state " + state);
	}

	/**
	 * Renders the states, final states and transitions.
	 *
	 * @return a multiline automaton description
	 */
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		result.append("States: 0..").append(this.stateCount - 1)
				.append("; final states: ").append(this.finalStates).append('\n');
		for (Transition transition : this.transitions)
			result.append(transition).append('\n');
		return result.toString().stripTrailing();
	}

	/**
	 * A bottom-up transition.
	 *
	 * @param symbol transition symbol
	 * @param arguments source states
	 * @param result target state
	 */
	record Transition(
			FunctionSymbol symbol, List<Integer> arguments, int result) {

		Transition {
			arguments = List.copyOf(arguments);
		}

		/**
		 * Renders this transition.
		 *
		 * @return a transition in {@code source -> target} form
		 */
		@Override
		public String toString() {
			return this.symbol +
					(this.arguments.isEmpty() ? "" : this.arguments.toString()) +
					" -> " + this.result;
		}
	}

	/**
	 * A transition source used as an index key.
	 *
	 * @param symbol transition symbol
	 * @param arguments source states
	 */
	private record TransitionSource(
			FunctionSymbol symbol, List<Integer> arguments) {

		TransitionSource {
			arguments = List.copyOf(arguments);
		}
	}
}
