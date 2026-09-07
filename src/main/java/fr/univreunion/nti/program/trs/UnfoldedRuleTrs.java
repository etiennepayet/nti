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

package fr.univreunion.nti.program.trs;

import java.util.Collection;
import java.util.LinkedList;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.argument.ArgumentLoopByUnfolding;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;

/**
 * A rule which results from unfolding a TRS rule.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class UnfoldedRuleTrs extends RuleTrs {

	/**
	 * The iteration of the unfolding operator
	 * at which this rule is generated.
	 */
	protected final int iteration;
	
	/**
	 * The parent of this unfolded rule.
	 */
	protected final ParentTrs parent;
	
	/**
	 * Constructs an unfolded TRS rule from the given left-hand side,
	 * right-hand side and iteration.
	 * 
	 * @param left the left-hand side of this rule 
	 * @param right the right-hand side of this rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @param parent the parent of this rule
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	protected UnfoldedRuleTrs(Function left, Term right,
			int iteration, ParentTrs parent) {
		
		super(left, right);

		if (iteration < 0)
			throw new IllegalArgumentException(
					"construction of an unfolded TRS rule with a negative iteration");

		this.iteration = iteration;
		this.parent = parent;
	}

	/**
	 * Returns the iteration of the unfolding operator
	 * at which this rule is generated.
	 * 
	 * @return the iteration of the unfolding operator
	 * at which this rule is generated
	 */
	public int getIteration() {
		return this.iteration;
	}

	/**
	 * Returns the parent of this rule.
	 * 
	 * @return the parent of this rule
	 */
	public ParentTrs getParent() {
		return this.parent;
	}

	/**
	 * Returns a deep copy of this rule i.e., a copy
	 * where each subterm is also copied.
	 * 
	 * @return a deep copy of this rule
	 */
	@Override
	public UnfoldedRuleTrs deepCopy() {
		return this.deepCopy(this.iteration, this.parent);
	}

	/**
	 * Returns a deep copy of this rule i.e., a copy
	 * where each subterm is also copied. The iteration
	 * and the parent of the generated copy are set to
	 * the specified iteration and parent.
	 * 
	 * @param iteration the iteration of the generated copy
	 * @param parent the parent of the generated copy
	 * @return a deep copy of this rule
	 */
	public abstract UnfoldedRuleTrs deepCopy(int iteration, ParentTrs parent);

	/**
	 * Implements the following non-termination test: the
	 * right-hand side of the provided rule is an instance
	 * of, or unifies with, the left-hand side.
	 * <p>
	 * This method does not modify the provided rule.
	 * 
	 * @param rule an unfolded rule
	 * @return if the test succeeds, then a non-termination
	 * argument which embeds the corresponding looping term
	 * and substitutions; else <code>null</code>
	 */
	public static synchronized ArgumentLoopByUnfolding shallowMatchAndUnifyTest(UnfoldedRuleTrs rule) {
		UnfoldedRuleTrs ruleCopy = rule.deepCopy();

		// Here, as we perform some shallow tests, we do not need to
		// transform ruleCopy.left and ruleCopy.right into functions
		// (because if ruleCopy.left is a tuple, so is ruleCopy.right).

		// Subsumption test.
		Substitution theta2 = new Substitution(); 
		if (ruleCopy.left.isMoreGeneralThan(ruleCopy.right, theta2))
			return new ArgumentLoopByUnfolding(
					ruleCopy, true,
					new Position(), ruleCopy.left,
					new Substitution(), theta2);

		// Unification test.
		Substitution theta1 = new Substitution();
		if (ruleCopy.left.unifyWith(ruleCopy.right, theta1)) {
			return new ArgumentLoopByUnfolding(
					ruleCopy, true,
					new Position(), ruleCopy.left,
					theta1, new Substitution());
		}

		// Both tests above failed.
		return null;
	}

	/**
	 * Implements the following non-termination test:
	 * a subterm of the right-hand side of the provided
	 * rule is an instance of, or unifies with, the
	 * left-hand side.
	 * <p>
	 * This method does not modify the provided rule.
	 * 
	 * @param rule an unfolded rule
	 * @return if the test succeeds, then a non-termination
	 * argument which embeds the corresponding looping term
	 * and substitutions; else <code>null</code>
	 */
	public static synchronized ArgumentLoopByUnfolding deepMatchAndUnifyTest(UnfoldedRuleTrs rule) {
		for (Position p : rule.right) {
			UnfoldedRuleTrs ruleCopy = rule.deepCopy();
			// Here, as we perform some deep tests,
			// we need to transform ruleCopy.left and
			// ruleCopy.right into functions (because
			// if ruleCopy.left is a tuple, then we
			// have a problem because the inner
			// subterms of ruleCopy.right are not tuples).
			Term left = ruleCopy.left.toFunction();
			Term right = ruleCopy.right.toFunction();
			Term rightAtPosition = right.get(p);

			// Subsumption test.
			Substitution theta2 = new Substitution(); 
			if (left.isMoreGeneralThan(rightAtPosition, theta2))
				return new ArgumentLoopByUnfolding(
						ruleCopy, true,
						p, left,
						new Substitution(), theta2);

			// Unification test.
			Substitution theta1 = new Substitution();
			if (left.unifyWith(rightAtPosition, theta1)) {
				return new ArgumentLoopByUnfolding(
						ruleCopy, true,
						p, left,
						theta1, new Substitution());
			}
		}

		// All the tests failed.
		return null;
	}

	/**
	 * Implements the following non-termination test: the
	 * left-hand side of the provided rule left-unifies with
	 * the right-hand side.
	 * <p>
	 * This method does not modify the provided rule.
	 * 
	 * @param rule an unfolded rule
	 * @return if the test succeeds, then a non-termination
	 * argument which embeds the corresponding looping term
	 * and substitutions; else <code>null</code>
	 */
	public static synchronized ArgumentLoopByUnfolding shallowLeftUnifyTest(UnfoldedRuleTrs rule) {
		// We do not need to copy rule in order to apply
		// the left-unifiability test because this
		// test already copies and flattens rule.

		// Moreover, as we perform a shallow test,
		// we do not need to transform rule.left and
		// rule.right into functions (because if
		// rule.left is a tuple, so is rule.right).

		// Left-unification test.
		Substitution theta1 = new Substitution();
		Substitution theta2 = new Substitution();
		if (rule.left.leftUnifyWith(rule.right, theta1, theta2))
			return new ArgumentLoopByUnfolding(
					rule, false,
					new Position(),
					rule.left.apply(theta1),
					theta1, theta2);

		// The test above failed.
		return null;
	}

	/**
	 * Implements a non-termination test over this rule.
	 * 
	 * @return a non-<code>null</code> non-termination argument
	 * if the test succeeds and <code>null</code> otherwise
	 */
	public abstract Argument nonTerminationTest();

	/**
	 * Applies the <code>elim</code> operator to this rule.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param trs the TRS used for applying <code>elim</code>
	 * @return the rules resulting from applying <code>elim</code>
	 * to this rule
	 */
	public abstract Collection<UnfoldedRuleTrs> elim(
			Parameters parameters, Trs trs, SimpleCycleRegistry simpleCycles);

	/**
	 * Checks whether this rule is a non-termination witness.
	 * If this test succeeds, then builds a corresponding proof
	 * argument, adds it to the specified <code>proof</code> and
	 * returns a collection consisting of this rule only.
	 * Otherwise, applies the <code>elim</code> operator to this rule.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param trs the TRS used for applying <code>elim</code>
	 * @param proof the proof to build
	 * @return the rules resulting from applying <code>elim</code>
	 * to this rule
	 */
	public Collection<UnfoldedRuleTrs> elimAndProve(Parameters parameters,
			Trs trs, SimpleCycleRegistry simpleCycles, Proof proof) {

		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();

		Argument argument = this.nonTerminationTest();
		if (argument == null)
			result.addAll(this.elim(parameters, trs, simpleCycles));
		else {
			// If this rule is a non-termination witness, then
			// build a corresponding proof argument.
			proof.setArgument(argument);
			result.add(this);
		}			

		return result;
	}

	/**
	 * Adds the specified unfolded rule to the specified list.
	 *
	 * @param parameters parameters for applying <code>elim</code>
	 * @param trs the context of this operation
	 * @param simpleCycles the registry owned by the current unfolding execution
	 * @param proof a proof owned by the current unfolding execution
	 * @param unfoldedRule the unfolded rule to be added
	 * @param result the list to which the specified rule has to
	 * be added; it is owned by the current unfolding execution
	 * @return <code>true</code> iff we are in non-termination proof
	 * mode (i.e., <code>proof</code> is not <code>null</code>)
	 * and the specified rule is a proof argument
	 */
	protected static boolean add(Parameters parameters,
			Trs trs, SimpleCycleRegistry simpleCycles, Proof proof,
			UnfoldedRuleTrs unfoldedRule, LinkedList<UnfoldedRuleTrs> result) {

		result.addAll(
				proof == null ?
						unfoldedRule.elim(parameters, trs, simpleCycles) :
							unfoldedRule.elimAndProve(parameters, trs, simpleCycles, proof));

		// If we are in non-termination proof mode and if the rule unfoldedRule
		// is a proof argument, then stop everything.
		return proof != null && proof.isSuccess();
	}

	/**
	 * Adds the specified collection <code>rules</code> to the specified
	 * collection <code>result</code>.
	 *
	 * @param proof the proof owned by the current unfolding execution
	 * @param rules the rules to add
	 * @param result the collection owned by the current unfolding execution
	 * @return <code>true</code> iff the specified proof is a success
	 */
	protected static boolean addAll(Proof proof,
			Collection<UnfoldedRuleTrs> rules, Collection<UnfoldedRuleTrs> result) {

		result.addAll(rules);

		return proof != null && proof.isSuccess();
	}

	/**
	 * Unfolds this rule forwards with the provided rule and
	 * at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param rule the rule to use for unfolding this rule
	 * @param p a position in this rule at which the unfolding
	 * takes place
	 * @param iteration the iteration of the unfolding operator
	 * at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	public abstract Collection<UnfoldedRuleTrs> unfoldForwardsWith(
			Parameters parameters, RuleTrs rule, Position p, int iteration);

	/**
	 * Unfolds this rule backwards with the provided rule and
	 * at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param rule the rule to use for unfolding this rule
	 * @param p a position in this rule at which the unfolding
	 * takes place
	 * @param iteration the iteration of the unfolding operator
	 * at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	public abstract Collection<UnfoldedRuleTrs> unfoldBackwardsWith(
			Parameters parameters, RuleTrs rule, Position p, int iteration);

	/**
	 * Unfolds this rule once using the rules of <code>trs</code>.
	 * <p>
	 * Also applies <code>nonTerminationTest</code> to the computed
	 * unfolded rules if <code>proof</code> is not <code>null</code>;
	 * if <code>nonTerminationTest</code> succeeds for an unfolded rule,
	 * then the corresponding proof argument is added to <code>proof</code>.
	 * 
	 * @param parameters parameters for unfolding
	 * @param trs the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule
	 * @return the resulting unfolded rules
	 */
	public Collection<UnfoldedRuleTrs> unfold(
			Parameters parameters, Trs trs, SimpleCycleRegistry simpleCycles,
			int iteration, Proof proof) {

		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();

		if (parameters.isForwardUnfoldingEnabled() &&
				this.unfoldForwards(
						parameters, trs, simpleCycles, iteration, proof, result))
			return result;

		if (parameters.isBackwardUnfoldingEnabled())
			this.unfoldBackwards(
					parameters, trs, simpleCycles, iteration, proof, result);

		return result;
	}

	/**
	 * Unfolds this rule forwards at each position of its right-hand side,
	 * using the rules of the specified TRS in their iteration order.
	 *
	 * @param parameters parameters for unfolding and elimination
	 * @param trs the TRS whose rules are used for unfolding and elimination
	 * @param simpleCycles the registry used while eliminating generated rules
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof the proof to build, or <code>null</code> when no
	 * non-termination proof is requested
	 * @param result the ordered collection receiving retained generated rules
	 * @return <code>true</code> iff a generated rule completed the proof
	 */
	private boolean unfoldForwards(
			Parameters parameters, Trs trs, SimpleCycleRegistry simpleCycles,
			int iteration, Proof proof, LinkedList<UnfoldedRuleTrs> result) {

		for (Position position : this.right)
			for (RuleTrs rule : trs) {
			Collection<UnfoldedRuleTrs> unfoldedRules =
						this.unfoldForwardsWith(parameters, rule, position, iteration);
				for (UnfoldedRuleTrs unfoldedRule : unfoldedRules)
					if (add(parameters, trs, simpleCycles, proof, unfoldedRule, result))
						return true;
			}

		return false;
	}

	/**
	 * Unfolds this rule backwards at each position of its left-hand side,
	 * using the rules of the specified TRS in their iteration order.
	 *
	 * @param parameters parameters for unfolding and elimination
	 * @param trs the TRS whose rules are used for unfolding and elimination
	 * @param simpleCycles the registry used while eliminating generated rules
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof the proof to build, or <code>null</code> when no
	 * non-termination proof is requested
	 * @param result the ordered collection receiving retained generated rules
	 */
	private void unfoldBackwards(
			Parameters parameters, Trs trs, SimpleCycleRegistry simpleCycles,
			int iteration, Proof proof, LinkedList<UnfoldedRuleTrs> result) {

		for (Position position : this.left)
			for (RuleTrs rule : trs) {
			Collection<UnfoldedRuleTrs> unfoldedRules =
						this.unfoldBackwardsWith(parameters, rule, position, iteration);
				for (UnfoldedRuleTrs unfoldedRule : unfoldedRules)
					if (add(parameters, trs, simpleCycles, proof, unfoldedRule, result))
						return;
			}
	}
}
