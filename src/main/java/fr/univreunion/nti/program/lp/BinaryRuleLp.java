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

package fr.univreunion.nti.program.lp;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A binary logic program rule, i.e., a logic program
 * rule whose body contains exactly one atom.
 * <p>
 * A binary logic program rule results from unfolding
 * an ordinary logic program rule. It is used for proving
 * non-termination of a logic program (it occurs in
 * looping pairs constructed during the proofs).
 * <p>
 * An object of this class is mutable (because a term
 * is mutable).
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class BinaryRuleLp extends UnfoldedRuleLp {

	/**
	 * Constructs a binary logic program rule from the given head,
	 * body atom and iteration.
	 *
	 * @param head the head of the rule
	 * @param body the only atom of the body
	 * @param iteration the iteration of the unfolding operator
	 * at which this binary rule is generated
	 * @throws IllegalArgumentException if the given head
	 * or body atom is <code>null</code>
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public BinaryRuleLp(
			Function head, Function body, int iteration) {

		super(head, new Function[] { body }, iteration);
	}

	/**
	 * Returns the only body atom of this binary rule.
	 *
	 * @return the only body atom of this binary rule
	 */
	private Function bodyAtom() {
		return this.body[0];
	}

	/**
	 * Returns the predicate symbol of the head
	 * of this rule.
	 *
	 * @return the predicate symbol of the head
	 * of this rule
	 */
	public FunctionSymbol getHeadPredicateSymbol() {
		return this.head.getRootSymbol();
	}

	/**
	 * Returns the predicate symbol of the body
	 * atom of this rule.
	 *
	 * @return the predicate symbol of the body
	 * atom of this rule
	 */
	public FunctionSymbol getBodyPredicateSymbol() {
		return this.bodyAtom().getRootSymbol();
	}

	/**
	 * Checks if the argument of the head of this rule at
	 * the given index is ground.
	 *
	 * @param argumentIndex the given argument index
	 * @return <code>true</code> if the argument of the
	 * head of this rule at index <code>argumentIndex</code> is ground
	 * and <code>false</code> otherwise
	 */
	public boolean isGroundHeadArgument(int argumentIndex) {
		return this.head.getChild(argumentIndex).isGround();
	}

	/**
	 * Checks whether this rule is a unit loop with respect
	 * to the given set of positions <code>tau</code>, i.e.,
	 * whether its body atom is <code>tau</code>-more general
	 * than its head.
	 *
	 * @param tau a set of positions
	 * @return <code>true</code> if this rule is a unit loop
	 * with respect to <code>tau</code> and <code>false</code>
	 * otherwise
	 */
	public boolean isTauUnitLoop(SoP tau) {
		return Function.tauMoreGeneral(
				this.bodyAtom(), this.head, tau, new Substitution());
	}

	/**
	 * Checks whether this rule is pluggable into the given rule
	 * with respect to the given set of positions <code>tau</code>,
	 * i.e., whether the body atom of this rule is
	 * <code>tau</code>-more general than the head of the given rule.
	 *
	 * @param rule the given rule
	 * @param tau the given set of positions
	 * @return <code>true</code> if this rule is pluggable
	 * into <code>rule</code> with respect to <code>tau</code>
	 * and <code>false</code> otherwise
	 */
	public boolean isTauPluggableInto(BinaryRuleLp rule, SoP tau) {
		return Function.tauMoreGeneral(
				this.bodyAtom(), rule.head, tau, new Substitution());
	}

	/**
	 * Returns the indexes of the head arguments of this rule
	 * that violate condition DN1.
	 * <p>
	 * In the notation of DN1, this checks pairs of head arguments
	 * <code>s_i</code> and <code>s_j</code>.
	 *
	 * @return the indexes of the head arguments of this rule
	 * that violate condition DN1
	 */
	public List<Integer> findDN1ViolatingHeadArgumentIndexes() {
		List<Integer> violatingHeadArgumentIndexes = new LinkedList<>();

		int headArity = this.head.getRootSymbol().getArity();
		List<Set<Variable>> headArgumentVariables = new ArrayList<>(headArity);
		for (int argumentIndex = 0;
				argumentIndex < headArity;
				argumentIndex++)
			headArgumentVariables.add(
					this.head.getChild(argumentIndex).getVariables());

		for (int firstArgumentIndex = 0;
				firstArgumentIndex < headArity;
				firstArgumentIndex++)
			for (int secondArgumentIndex = 0;
					secondArgumentIndex < headArity;
					secondArgumentIndex++) {
				if (secondArgumentIndex != firstArgumentIndex &&
						!Collections.disjoint(
								headArgumentVariables.get(firstArgumentIndex),
								headArgumentVariables.get(secondArgumentIndex)))
					violatingHeadArgumentIndexes.add(firstArgumentIndex);
			}

		return violatingHeadArgumentIndexes;
	}

	/**
	 * Let <code>p/n</code> be the predicate symbol of the head
	 * of this rule. This method computes an array of size
	 * <code>n</code> such that, for each integer <code>i</code>
	 * in <code>[0,n-1]</code>, the cell at index <code>i</code>
	 * contains the value that <code>tau(p)(i)</code> must have
	 * for DN2 to hold, or <code>null</code> if this value is
	 * undefined.
	 * <p>
	 * In the notation of DN2, this computes a value for
	 * <code>tau(p)(i)</code> by comparing it with the head
	 * argument <code>s_i</code>.
	 *
	 * @param tau the given set of positions
	 * @return an array representing the values that
	 * <code>tau(p)</code> must have for DN2 to hold
	 */
	public Term[] computeDN2RequiredValues(SoP tau) {
		FunctionSymbol headPredicateSymbol = this.head.getRootSymbol();
		Term[] dn2Values = new Term[headPredicateSymbol.getArity()];

		Term tauValueAtIndex;
		Term headArgument;
		for (int argumentIndex = 0;
				argumentIndex < dn2Values.length;
				argumentIndex++) {
			tauValueAtIndex =
					tau.getMappedTerm(headPredicateSymbol, argumentIndex);
			if (tauValueAtIndex != null) {
				headArgument = this.head.getChild(argumentIndex);
				if (headArgument.isMoreGeneralThan(tauValueAtIndex))
					dn2Values[argumentIndex] = tauValueAtIndex;
				else if (tauValueAtIndex.isMoreGeneralThan(headArgument))
					dn2Values[argumentIndex] = headArgument;
				else
					dn2Values[argumentIndex] = null;
			}
			else
				dn2Values[argumentIndex] = null;
		}

		return dn2Values;
	}

	/**
	 * Returns the indexes of the body arguments of this rule
	 * that violate condition DN3 relatively to the given set
	 * of positions.
	 * <p>
	 * In the notation of DN3, this checks whether each defined
	 * value <code>tau(q)(j)</code> is more general than the body
	 * argument <code>t_j</code>.
	 *
	 * @param tau the given set of positions
	 * @return the indexes of the body arguments of this rule
	 * that violate condition DN3
	 */
	public List<Integer> findDN3ViolatingBodyArgumentIndexes(SoP tau) {
		List<Integer> violatingBodyArgumentIndexes = new LinkedList<>();

		Term tauValueAtIndex;
		Term bodyArgument;
		FunctionSymbol bodyPredicateSymbol = this.bodyAtom().getRootSymbol();
		int bodyArity = bodyPredicateSymbol.getArity();
		for (int argumentIndex = 0;
				argumentIndex < bodyArity;
				argumentIndex++) {
			tauValueAtIndex =
					tau.getMappedTerm(bodyPredicateSymbol, argumentIndex);
			bodyArgument = this.bodyAtom().getChild(argumentIndex);
			if (tauValueAtIndex != null &&
					!tauValueAtIndex.isMoreGeneralThan(bodyArgument))
				violatingBodyArgumentIndexes.add(argumentIndex);
		}

		return violatingBodyArgumentIndexes;
	}

	/**
	 * Returns the indexes of the head arguments of this rule
	 * that violate condition DN4 relatively to the given set
	 * of positions.
	 * <p>
	 * In the notation of DN4, this checks pairs made of a head
	 * argument <code>s_i</code> and a body argument <code>t_j</code>.
	 *
	 * @param tau the given set of positions
	 * @return the indexes of the head arguments of this rule
	 * that violate condition DN4
	 */
	public List<Integer> findDN4ViolatingHeadArgumentIndexes(SoP tau) {
		int selectedHeadArgumentCount =
				countSelectedArguments(this.head, tau, true);
		int selectedBodyArgumentCount =
				countSelectedArguments(this.bodyAtom(), tau, false);

		if (selectedHeadArgumentCount == 0 ||
				selectedBodyArgumentCount == 0)
			return new LinkedList<>();

		return selectedHeadArgumentCount <= selectedBodyArgumentCount ?
				findDN4ViolationsWithStoredHeadVariables(tau) :
				findDN4ViolationsWithStoredBodyVariables(tau);
	}

	/**
	 * Finds DN4 violations while storing the selected head variables and
	 * reusing one variable set for the body arguments.
	 *
	 * @param tau the set of positions defining the selection
	 * @return the violating head argument indexes
	 */
	private List<Integer> findDN4ViolationsWithStoredHeadVariables(SoP tau) {
		List<Set<Variable>> headArgumentVariables =
				selectedArgumentVariables(this.head, tau, true);
		int[] violationCounts = new int[headArgumentVariables.size()];
		Set<Variable> bodyVariables = new HashSet<>();
		Function body = this.bodyAtom();
		FunctionSymbol bodyPredicateSymbol = body.getRootSymbol();

		for (int bodyArgumentIndex = 0;
				bodyArgumentIndex < bodyPredicateSymbol.getArity();
				bodyArgumentIndex++) {
			if (!tau.isInDomain(bodyPredicateSymbol, bodyArgumentIndex)) {
				bodyVariables.clear();
				body.getChild(bodyArgumentIndex)
						.collectVariablesInto(bodyVariables);
				for (int headArgumentIndex = 0;
						headArgumentIndex < headArgumentVariables.size();
						headArgumentIndex++) {
					Set<Variable> headVariables =
							headArgumentVariables.get(headArgumentIndex);
					if (headVariables != null &&
							!Collections.disjoint(
									headVariables, bodyVariables))
						violationCounts[headArgumentIndex]++;
				}
			}
		}

		List<Integer> violatingHeadArgumentIndexes = new LinkedList<>();
		for (int headArgumentIndex = 0;
				headArgumentIndex < violationCounts.length;
				headArgumentIndex++)
			for (int count = violationCounts[headArgumentIndex];
					count > 0;
					count--)
				violatingHeadArgumentIndexes.add(headArgumentIndex);

		return violatingHeadArgumentIndexes;
	}

	/**
	 * Finds DN4 violations while storing the selected body variables and
	 * reusing one variable set for the head arguments.
	 *
	 * @param tau the set of positions defining the selection
	 * @return the violating head argument indexes
	 */
	private List<Integer> findDN4ViolationsWithStoredBodyVariables(SoP tau) {
		List<Integer> violatingHeadArgumentIndexes = new LinkedList<>();
		List<Set<Variable>> bodyArgumentVariables =
				selectedArgumentVariables(this.bodyAtom(), tau, false);
		Set<Variable> headVariables = new HashSet<>();
		FunctionSymbol headPredicateSymbol = this.head.getRootSymbol();

		for (int headArgumentIndex = 0;
				headArgumentIndex < headPredicateSymbol.getArity();
				headArgumentIndex++) {
			if (tau.isInDomain(headPredicateSymbol, headArgumentIndex)) {
				headVariables.clear();
				this.head.getChild(headArgumentIndex)
						.collectVariablesInto(headVariables);
				for (Set<Variable> bodyVariables : bodyArgumentVariables)
					if (bodyVariables != null &&
							!Collections.disjoint(
									headVariables, bodyVariables))
						violatingHeadArgumentIndexes.add(headArgumentIndex);
			}
		}

		return violatingHeadArgumentIndexes;
	}

	/**
	 * Counts arguments selected by their membership in the domain of the
	 * provided set of positions.
	 *
	 * @param atom the atom whose arguments are inspected
	 * @param tau the set of positions defining the selection
	 * @param selectDomain {@code true} to select arguments in the domain,
	 * and {@code false} to select arguments outside it
	 * @return the number of selected arguments
	 */
	private static int countSelectedArguments(
			Function atom,
			SoP tau,
			boolean selectDomain) {
		FunctionSymbol predicateSymbol = atom.getRootSymbol();
		int selectedArgumentCount = 0;

		for (int argumentIndex = 0;
				argumentIndex < predicateSymbol.getArity();
				argumentIndex++)
			if (tau.isInDomain(predicateSymbol, argumentIndex) == selectDomain)
				selectedArgumentCount++;

		return selectedArgumentCount;
	}

	/**
	 * Collects the variables of arguments selected by their membership in
	 * the domain of the provided set of positions. Unselected arguments are
	 * represented by <code>null</code> so indexes remain aligned with the atom.
	 *
	 * @param atom the atom whose arguments are inspected
	 * @param tau the set of positions defining the selection
	 * @param selectDomain <code>true</code> to select arguments in the domain,
	 * and <code>false</code> to select arguments outside it
	 * @return the selected argument-variable sets, aligned with the atom
	 */
	private static List<Set<Variable>> selectedArgumentVariables(
			Function atom,
			SoP tau,
			boolean selectDomain) {
		FunctionSymbol predicateSymbol = atom.getRootSymbol();
		int arity = predicateSymbol.getArity();
		List<Set<Variable>> argumentVariables = new ArrayList<>(arity);

		for (int argumentIndex = 0;
				argumentIndex < arity;
				argumentIndex++) {
			boolean isInDomain =
					tau.isInDomain(predicateSymbol, argumentIndex);
			if (isInDomain == selectDomain) {
				Set<Variable> variables = new HashSet<>();
				atom.getChild(argumentIndex).collectVariablesInto(variables);
				argumentVariables.add(variables);
			}
			else
				argumentVariables.add(null);
		}

		return argumentVariables;
	}

	/**
	 * Returns a String representation of this binary rule, without
	 * a final dot.
	 * <p>
	 * This format is used when displaying a binary sequence inside
	 * a looping pair. It differs from <code>RuleLp.toString()</code>,
	 * which appends a final dot to the rule representation.
	 *
	 * @return a String representation of this binary rule, without
	 * a final dot
	 */
	@Override
	public String toString() {
		// A set of pairs (V,s) where s is
		// the symbol associated to variable V.
		HashMap<Variable,String> variables = new HashMap<>();

		return this.head.toString(variables, false) +
				" :- " +
				this.bodyAtom().toString(variables, false);
	}
}
