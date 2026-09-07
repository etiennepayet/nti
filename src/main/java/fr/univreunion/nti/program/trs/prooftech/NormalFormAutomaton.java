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
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Builds a deterministic automaton recognizing the ground normal forms.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class NormalFormAutomaton {

	/** Deterministic automaton recognizing exactly the ground normal forms. */
	private final FiniteTreeAutomaton automaton;

	/**
	 * Wraps the automaton recognizing ground normal forms.
	 *
	 * @param automaton normal-form automaton
	 */
	private NormalFormAutomaton(FiniteTreeAutomaton automaton) {
		this.automaton = automaton;
	}

	/**
	 * Returns the underlying deterministic automaton.
	 *
	 * @return the normal-form automaton
	 */
	FiniteTreeAutomaton automaton() {
		return this.automaton;
	}

	/**
	 * Builds the automaton, or returns {@code null} if its explicit reachable
	 * state space exceeds one of the supplied bounds.
	 *
	 * @param trs rewrite system whose normal forms are recognized
	 * @param alphabet function symbols of the rewrite system
	 * @param maximumStateCount maximum number of reachable states
	 * @param maximumTransitionCount maximum number of explicit transitions
	 * @return the normal-form automaton, or {@code null} when a bound is reached
	 */
	static NormalFormAutomaton build(
			Trs trs,
			List<FunctionSymbol> alphabet,
			int maximumStateCount,
			int maximumTransitionCount) {

		return new Builder(
				trs, maximumStateCount, maximumTransitionCount).build(alphabet);
	}

	/** Performs the bounded reachable-state saturation. */
	private static final class Builder {
		/** Index of non-variable patterns occurring in rule left-hand sides. */
		private final PatternIndex patterns;
		/** Maximum number of reachable automaton states. */
		private final int maximumStateCount;
		/** Maximum number of explicit deterministic transitions. */
		private final int maximumTransitionCount;
		/** Pattern states in deterministic discovery order. */
		private final List<PatternState> states = new ArrayList<>();
		/** Canonical index assigned to each discovered pattern state. */
		private final Map<PatternState, Integer> stateIndexes = new HashMap<>();
		/** Deterministic transition table in enumeration order. */
		private final Map<TransitionSource, Integer> transitions =
				new LinkedHashMap<>();
		/** Whether neither explicit saturation bound has been exceeded. */
		private boolean withinBounds = true;

		/**
		 * Creates a bounded saturation builder.
		 *
		 * @param trs rewrite system whose left-hand sides define redexes
		 * @param maximumStateCount maximum number of states
		 * @param maximumTransitionCount maximum number of transitions
		 */
		private Builder(
				Trs trs, int maximumStateCount, int maximumTransitionCount) {

			this.patterns = new PatternIndex(trs);
			this.maximumStateCount = maximumStateCount;
			this.maximumTransitionCount = maximumTransitionCount;
		}

		/**
		 * Computes the state reached by one transition source.
		 *
		 * @param symbol transition symbol
		 * @param arguments source states
		 * @return the pattern state reached by the transition
		 */
		private PatternState transitionState(
				FunctionSymbol symbol, List<Integer> arguments) {

			BitSet matches = new BitSet(this.patterns.size());
			boolean reducible = false;
			for (int argument : arguments)
				reducible |= this.states.get(argument).reducible();

			for (int patternIndex = 0;
					patternIndex < this.patterns.size(); patternIndex++) {
				Function pattern = this.patterns.pattern(patternIndex);
				if (pattern.getRootSymbol() != symbol)
					continue;

				boolean match = true;
				for (int childIndex = 0;
						childIndex < symbol.getArity(); childIndex++) {
					Term childPattern = pattern.getChild(childIndex);
					if (!(childPattern instanceof Variable) &&
							!this.states.get(arguments.get(childIndex)).matches()
									.get(this.patterns.indexOf(childPattern))) {
						match = false;
						break;
					}
				}
				if (match) {
					matches.set(patternIndex);
					if (this.patterns.isLeftHandSide(patternIndex))
						reducible = true;
				}
			}
			return new PatternState(matches, reducible);
		}

		/**
		 * Enumerates state tuples of the requested arity.
		 *
		 * @param stateCount number of states available at each position
		 * @param arity tuple length
		 * @return all tuples in lexicographic enumeration order
		 */
		private static List<List<Integer>> stateTuples(
				int stateCount, int arity) {

			List<List<Integer>> result = new ArrayList<>();
			if (arity == 0) {
				result.add(List.of());
				return result;
			}
			if (stateCount == 0)
				return result;
			enumerateTuples(stateCount, arity, new ArrayList<>(), result);
			return result;
		}

		/**
		 * Recursively enumerates state-tuple suffixes.
		 *
		 * @param stateCount number of states available at each position
		 * @param remaining number of positions left to fill
		 * @param current tuple prefix under construction
		 * @param result destination list for complete tuples
		 */
		private static void enumerateTuples(
				int stateCount,
				int remaining,
				List<Integer> current,
				List<List<Integer>> result) {

			if (remaining == 0) {
				result.add(List.copyOf(current));
				return;
			}
			for (int state = 0; state < stateCount; state++) {
				current.add(state);
				enumerateTuples(stateCount, remaining - 1, current, result);
				current.removeLast();
			}
		}

		/**
		 * Saturates the reachable states and constructs the automaton.
		 *
		 * @param alphabet function symbols to enumerate
		 * @return the completed automaton, or {@code null} when a bound is reached
		 */
		private NormalFormAutomaton build(List<FunctionSymbol> alphabet) {
			boolean changed;
			do {
				changed = expand(alphabet);
			}
			while (changed && this.withinBounds);
			return this.withinBounds && !this.states.isEmpty() ?
					toAutomaton() : null;
		}

		/**
		 * Expands every symbol using the states present at round start.
		 *
		 * @param alphabet function symbols to expand
		 * @return {@code true} if the round discovered a new state
		 */
		private boolean expand(List<FunctionSymbol> alphabet) {
			int sourceStateCount = this.states.size();
			boolean changed = false;
			for (FunctionSymbol symbol : alphabet) {
				changed |= expand(symbol, sourceStateCount);
				if (!this.withinBounds)
					break;
			}
			return changed;
		}

		/**
		 * Adds all transitions for one symbol and one saturation round.
		 *
		 * @param symbol function symbol to expand
		 * @param sourceStateCount number of states present at round start
		 * @return {@code true} if a transition discovered a new state
		 */
		private boolean expand(FunctionSymbol symbol, int sourceStateCount) {
			boolean changed = false;
			for (List<Integer> arguments :
					stateTuples(sourceStateCount, symbol.getArity())) {
				TransitionAddition addition = addTransition(symbol, arguments);
				changed |= addition == TransitionAddition.STATE_ADDED;
				if (addition == TransitionAddition.LIMIT_EXCEEDED)
					break;
			}
			return changed;
		}

		/**
		 * Adds one transition and reports whether it introduced a state.
		 *
		 * @param symbol transition symbol
		 * @param arguments source states
		 * @return the effect of adding the transition
		 */
		private TransitionAddition addTransition(
				FunctionSymbol symbol, List<Integer> arguments) {

			PatternState state = transitionState(symbol, arguments);
			Integer result = this.stateIndexes.get(state);
			TransitionAddition addition = TransitionAddition.UNCHANGED;
			if (result == null) {
				if (this.states.size() >= this.maximumStateCount) {
					this.withinBounds = false;
					return TransitionAddition.LIMIT_EXCEEDED;
				}
				result = this.states.size();
				this.states.add(state);
				this.stateIndexes.put(state, result);
				addition = TransitionAddition.STATE_ADDED;
			}
			this.transitions.put(
					new TransitionSource(symbol, arguments), result);
			if (this.transitions.size() > this.maximumTransitionCount) {
				this.withinBounds = false;
				return TransitionAddition.LIMIT_EXCEEDED;
			}
			return addition;
		}

		/**
		 * Converts the saturated tables to the automaton representation.
		 *
		 * @return the completed normal-form automaton
		 */
		private NormalFormAutomaton toAutomaton() {
			Set<Integer> normalStates = new HashSet<>();
			for (int index = 0; index < this.states.size(); index++)
				if (!this.states.get(index).reducible())
					normalStates.add(index);

			List<FiniteTreeAutomaton.Transition> automatonTransitions =
					new ArrayList<>(this.transitions.size());
			for (Map.Entry<TransitionSource, Integer> entry :
					this.transitions.entrySet())
				automatonTransitions.add(new FiniteTreeAutomaton.Transition(
						entry.getKey().symbol(), entry.getKey().arguments(),
						entry.getValue()));

			return new NormalFormAutomaton(new FiniteTreeAutomaton(
					this.states.size(), normalStates, automatonTransitions));
		}
	}

	/** Outcome of inserting one transition during saturation. */
	private enum TransitionAddition {
		/** The transition reaches an already known state. */
		UNCHANGED,
		/** The transition introduces a new reachable state. */
		STATE_ADDED,
		/** A configured state or transition bound is exceeded. */
		LIMIT_EXCEEDED
	}

	/** Identity-based index of the patterns needed to recognize redexes. */
	private static final class PatternIndex {
		/** Non-variable patterns in deterministic traversal order. */
		private final List<Function> patterns = new ArrayList<>();
		/** Identity-based map from pattern terms to their indexes. */
		private final IdentityHashMap<Term, Integer> indexes =
				new IdentityHashMap<>();
		/** Bits identifying patterns that are complete left-hand sides. */
		private final BitSet leftHandSides = new BitSet();

		/**
		 * Indexes all non-variable patterns in left-hand sides.
		 *
		 * @param trs rewrite system to index
		 */
		private PatternIndex(Trs trs) {
			for (RuleTrs rule : trs) {
				collect(rule.getLeft());
				this.leftHandSides.set(indexOf(rule.getLeft()));
			}
		}

		/**
		 * Adds the non-variable subpatterns of a term to the index.
		 *
		 * @param term term whose subpatterns are collected
		 */
		private void collect(Term term) {
			if (!(term instanceof Function function) ||
					this.indexes.containsKey(term))
				return;
			int index = this.patterns.size();
			this.patterns.add(function);
			this.indexes.put(term, index);
			for (int child = 0;
					child < function.getRootSymbol().getArity(); child++)
				collect(function.getChild(child));
		}

		/**
		 * Returns the number of indexed patterns.
		 *
		 * @return the pattern count
		 */
		private int size() {
			return this.patterns.size();
		}

		/**
		 * Returns an indexed pattern.
		 *
		 * @param index pattern index
		 * @return the corresponding function pattern
		 */
		private Function pattern(int index) {
			return this.patterns.get(index);
		}

		/**
		 * Looks up the identity-based index of a non-variable pattern.
		 *
		 * @param term indexed pattern term
		 * @return the pattern index
		 * @throws IllegalArgumentException if the term is not indexed
		 */
		private int indexOf(Term term) {
			Integer result = this.indexes.get(term);
			if (result == null)
				throw new IllegalArgumentException("unknown non-variable pattern");
			return result;
		}

		/**
		 * Reports whether a pattern is a complete left-hand side.
		 *
		 * @param index pattern index
		 * @return {@code true} if the pattern is a rewrite-rule left-hand side
		 */
		private boolean isLeftHandSide(int index) {
			return this.leftHandSides.get(index);
		}
	}

	/**
	 * State recording matched patterns and redex reachability.
	 *
	 * @param matches indexes of patterns matched at the root
	 * @param reducible whether this state recognizes reducible terms
	 */
	private record PatternState(BitSet matches, boolean reducible) {
		private PatternState {
			matches = (BitSet) matches.clone();
		}
	}

	/**
	 * Deterministic transition source.
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
