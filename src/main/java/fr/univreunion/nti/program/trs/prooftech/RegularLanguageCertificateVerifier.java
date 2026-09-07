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
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Independently checks regular-language nontermination certificates.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class RegularLanguageCertificateVerifier {

	/**
	 * Checks all obligations of a regular-language certificate.
	 *
	 * @param trs rewrite system certified as nonterminating
	 * @param candidate automaton recognizing the candidate language
	 * @param normalForms automaton recognizing ground normal forms
	 * @return the verification result and an accepted witness on success
	 */
	Verification verify(
			Trs trs,
			FiniteTreeAutomaton candidate,
			NormalFormAutomaton normalForms) {

		if (hasNonLeftLinearRule(trs))
			return Verification.failed("the TRS is not left-linear");

		Term witness = candidate.acceptedTermWitness();
		if (witness == null)
			return Verification.failed("the accepted language is empty");
		BitSet witnessStates = candidate.evaluate(witness);
		witnessStates.and(finalStates(candidate));
		if (witnessStates.isEmpty())
			return Verification.failed("the language witness is not accepted");

		for (RuleTrs rule : trs)
			if (!isClosedForRule(rule, candidate))
				return Verification.failed(
						"the language is not closed under " + rule);

		if (acceptsNormalForm(candidate, normalForms.automaton()))
			return Verification.failed(
					"the accepted language contains a normal form");

		return new Verification(true, witness, null);
	}

	/**
	 * Reports whether a rewrite-rule left-hand side is non-left-linear.
	 *
	 * @param trs rewrite system to inspect
	 * @return {@code true} if a variable occurs more than once in a left side
	 */
	static boolean hasNonLeftLinearRule(Trs trs) {
		for (RuleTrs rule : trs) {
			Map<Variable, Integer> occurrences = new IdentityHashMap<>();
			rule.getLeft().getVariableOccurrences(occurrences);
			for (int count : occurrences.values())
				if (count != 1)
					return true;
		}
		return false;
	}

	/**
	 * Converts the final-state set to a bit set.
	 *
	 * @param automaton automaton whose final states are converted
	 * @return bit set of final states
	 */
	private static BitSet finalStates(FiniteTreeAutomaton automaton) {
		BitSet result = new BitSet(automaton.stateCount());
		for (int state : automaton.finalStates())
			result.set(state);
		return result;
	}

	/**
	 * Checks state-wise closure under one rewrite rule.
	 *
	 * @param rule rule whose closure obligations are checked
	 * @param automaton candidate language automaton
	 * @return {@code true} if every state assignment satisfies closure
	 */
	private static boolean isClosedForRule(
			RuleTrs rule, FiniteTreeAutomaton automaton) {

		List<Variable> variables = variablesInTraversalOrder(rule.getLeft());
		int[] assignment = new int[variables.size()];
		return checkAssignments(
				rule, automaton, variables, assignment, 0);
	}

	/**
	 * Enumerates assignments and checks the induced closure inclusions.
	 *
	 * @param rule rule whose sides are evaluated
	 * @param automaton candidate language automaton
	 * @param variables left-hand-side variables in traversal order
	 * @param assignment state assigned to every variable
	 * @param index next variable position to assign
	 * @return {@code true} if all remaining assignments satisfy closure
	 */
	private static boolean checkAssignments(
			RuleTrs rule,
			FiniteTreeAutomaton automaton,
			List<Variable> variables,
			int[] assignment,
			int index) {

		if (index < assignment.length) {
			for (int state = 0; state < automaton.stateCount(); state++) {
				assignment[index] = state;
				if (!checkAssignments(
						rule, automaton, variables, assignment, index + 1))
					return false;
			}
			return true;
		}

		IdentityHashMap<Variable, Integer> states = new IdentityHashMap<>();
		for (int variable = 0; variable < variables.size(); variable++)
			states.put(variables.get(variable), assignment[variable]);
		BitSet leftStates = evaluate(rule.getLeft(), states, automaton);
		BitSet rightStates = evaluate(rule.getRight(), states, automaton);
		leftStates.andNot(rightStates);
		return leftStates.isEmpty();
	}

	/**
	 * Evaluates a term under a variable-to-state assignment.
	 *
	 * @param term term to evaluate
	 * @param assignment identity-based variable-state assignment
	 * @param automaton automaton providing the transitions
	 * @return all possible root states
	 */
	private static BitSet evaluate(
			Term term,
			IdentityHashMap<Variable, Integer> assignment,
			FiniteTreeAutomaton automaton) {

		if (term instanceof Variable variable) {
			BitSet result = new BitSet(automaton.stateCount());
			Integer state = assignment.get(variable);
			if (state != null)
				result.set(state);
			return result;
		}

		Function function = (Function) term;
		List<BitSet> childStates = new ArrayList<>(
				function.getRootSymbol().getArity());
		for (int child = 0;
				child < function.getRootSymbol().getArity(); child++)
			childStates.add(evaluate(
					function.getChild(child), assignment, automaton));

		BitSet result = new BitSet(automaton.stateCount());
		enumerateChildStates(childStates, 0, new ArrayList<>(), states ->
				result.or(automaton.targets(
						function.getRootSymbol(), states)));
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
	private static void enumerateChildStates(
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
			enumerateChildStates(choices, index + 1, current, consumer);
			current.removeLast();
		}
	}

	/**
	 * Checks whether the candidate language contains a ground normal form.
	 *
	 * @param candidate candidate language automaton
	 * @param normalForms ground-normal-form automaton
	 * @return {@code true} if the automata have a common accepted term
	 */
	private static boolean acceptsNormalForm(
			FiniteTreeAutomaton candidate,
			FiniteTreeAutomaton normalForms) {

		BitSet reachablePairs = reachableProductStates(candidate, normalForms);
		return hasReachableFinalPair(candidate, normalForms, reachablePairs);
	}

	/**
	 * Computes the reachable states of the product automaton.
	 *
	 * @param candidate candidate language automaton
	 * @param normalForms ground-normal-form automaton
	 * @return reachable product-state pairs
	 */
	private static BitSet reachableProductStates(
			FiniteTreeAutomaton candidate,
			FiniteTreeAutomaton normalForms) {

		BitSet reachablePairs = new BitSet(
				candidate.stateCount() * normalForms.stateCount());
		boolean changed;
		do {
			changed = propagateReachability(
					candidate, normalForms, reachablePairs);
		}
		while (changed);
		return reachablePairs;
	}

	/**
	 * Performs one product-reachability propagation round.
	 *
	 * @param candidate candidate language automaton
	 * @param normalForms ground-normal-form automaton
	 * @param reachablePairs product pairs reached before this round
	 * @return {@code true} if the round reaches a new pair
	 */
	private static boolean propagateReachability(
			FiniteTreeAutomaton candidate,
			FiniteTreeAutomaton normalForms,
			BitSet reachablePairs) {

		boolean changed = false;
		for (FiniteTreeAutomaton.Transition left : candidate.transitions())
			for (FiniteTreeAutomaton.Transition right :
					normalForms.transitions())
				changed |= addReachablePair(
						left, right, reachablePairs, normalForms.stateCount());
		return changed;
	}

	/**
	 * Adds the result pair when two transitions are jointly reachable.
	 *
	 * @param left candidate-automaton transition
	 * @param right normal-form-automaton transition
	 * @param reachablePairs currently reachable product pairs
	 * @param normalStateCount number of normal-form states
	 * @return {@code true} if a new result pair was added
	 */
	private static boolean addReachablePair(
			FiniteTreeAutomaton.Transition left,
			FiniteTreeAutomaton.Transition right,
			BitSet reachablePairs,
			int normalStateCount) {

		if (left.symbol() != right.symbol() ||
				left.arguments().size() != right.arguments().size() ||
				!childrenReachable(
						left, right, reachablePairs, normalStateCount))
			return false;
		int pair = pairIndex(
				left.result(), right.result(), normalStateCount);
		if (reachablePairs.get(pair))
			return false;
		reachablePairs.set(pair);
		return true;
	}

	/**
	 * Checks whether a reachable product state is final on both sides.
	 *
	 * @param candidate candidate language automaton
	 * @param normalForms ground-normal-form automaton
	 * @param reachablePairs reachable product pairs
	 * @return {@code true} if a reachable pair is final in both automata
	 */
	private static boolean hasReachableFinalPair(
			FiniteTreeAutomaton candidate,
			FiniteTreeAutomaton normalForms,
			BitSet reachablePairs) {

		for (int candidateFinal : candidate.finalStates())
			for (int normalFinal : normalForms.finalStates())
				if (reachablePairs.get(pairIndex(
						candidateFinal, normalFinal,
						normalForms.stateCount())))
					return true;
		return false;
	}

	/**
	 * Checks whether all paired transition arguments are reachable.
	 *
	 * @param left candidate-automaton transition
	 * @param right normal-form-automaton transition
	 * @param reachablePairs reachable product pairs
	 * @param normalStateCount number of normal-form states
	 * @return {@code true} if every child-state pair is reachable
	 */
	private static boolean childrenReachable(
			FiniteTreeAutomaton.Transition left,
			FiniteTreeAutomaton.Transition right,
			BitSet reachablePairs,
			int normalStateCount) {

		for (int index = 0; index < left.arguments().size(); index++)
			if (!reachablePairs.get(pairIndex(
					left.arguments().get(index), right.arguments().get(index),
					normalStateCount)))
				return false;
		return true;
	}

	/**
	 * Maps a product-state pair to its bit-set index.
	 *
	 * @param candidateState candidate-automaton state
	 * @param normalState normal-form-automaton state
	 * @param normalStateCount number of normal-form states
	 * @return flattened pair index
	 */
	private static int pairIndex(
			int candidateState, int normalState, int normalStateCount) {

		return candidateState * normalStateCount + normalState;
	}

	/**
	 * Collects distinct variables in deterministic traversal order.
	 *
	 * @param term term whose variables are collected
	 * @return identity-distinct variables in first-occurrence order
	 */
	static List<Variable> variablesInTraversalOrder(Term term) {
		Set<Variable> variables = java.util.Collections.newSetFromMap(
				new IdentityHashMap<>());
		List<Variable> result = new ArrayList<>();
		collectVariables(term, variables, result);
		return result;
	}

	/**
	 * Recursively collects first occurrences of variables.
	 *
	 * @param term term or subterm to traverse
	 * @param seen identity-based set of variables already encountered
	 * @param result destination list in traversal order
	 */
	private static void collectVariables(
			Term term, Set<Variable> seen, List<Variable> result) {

		if (term instanceof Variable variable) {
			if (seen.add(variable))
				result.add(variable);
			return;
		}
		Function function = (Function) term;
		for (int index = 0;
				index < function.getRootSymbol().getArity(); index++)
			collectVariables(function.getChild(index), seen, result);
	}

	/**
	 * Result of independent certificate verification.
	 *
	 * @param valid whether every certificate obligation holds
	 * @param witness accepted ground witness on success, otherwise {@code null}
	 * @param failure failure explanation, or {@code null} on success
	 */
	record Verification(boolean valid, Term witness, String failure) {
		/**
		 * Creates a failed verification result.
		 *
		 * @param failure failure explanation
		 * @return a failed result without a witness
		 */
		private static Verification failed(String failure) {
			return new Verification(false, null, failure);
		}
	}
}
