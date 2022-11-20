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
import java.util.LinkedList;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Path;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.argument.ArgumentLoopByUnfolding;
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
	 * The path (in the program being unfolded) that
	 * corresponds to this unfolded rule.
	 */
	protected final Path path = new Path(); 

	/**
	 * Constructs an unfolded TRS rule from the given left-hand side,
	 * right-hand side and iteration.
	 * 
	 * @param left the left-hand side of this rule 
	 * @param right the right-hand side of this rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @param parent the parent of this rule
	 * @param path the path in the program being unfolded that
	 * corresponds to this rule
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	protected UnfoldedRuleTrs(Function left, Term right,
			int iteration, ParentTrs parent, Path path) {
		
		super(left, right);

		if (iteration < 0)
			throw new IllegalArgumentException(
					"construction of an unfolded TRS rule with a negative iteration");

		this.iteration = iteration;
		this.parent = parent;
		if (path != null) this.path.addAll(path);
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
	 * 
	 * This method does not modify the provided rule.
	 * 
	 * @param R an unfolded rule
	 * @return if the test succeeds, then a non-termination
	 * argument which embeds the corresponding looping term
	 * and substitutions; else <code>null</code>
	 */
	public synchronized static ArgumentLoopByUnfolding shallowMatchAndUnifyTest(UnfoldedRuleTrs R) {
		UnfoldedRuleTrs R_copy = R.deepCopy();

		// Here, as we perform some shallow tests, we do not need to
		// transform R_copy.left and R_copy.right into functions
		// (because if R_copy.left is a tuple, so is R_copy.right).

		// Subsumption test.
		Substitution theta2 = new Substitution(); 
		if (R_copy.left.isMoreGeneralThan(R_copy.right, theta2))
			return new ArgumentLoopByUnfolding(
					R_copy, true,
					new Position(), R_copy.left,
					new Substitution(), theta2);

		// Unification test.
		Substitution theta1 = new Substitution();
		if (R_copy.left.unifyWith(R_copy.right, theta1)) {
			return new ArgumentLoopByUnfolding(
					R_copy, true,
					new Position(), R_copy.left,
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
	 * 
	 * This method does not modify the provided rule.
	 * 
	 * @param R an unfolded rule
	 * @return if the test succeeds, then a non-termination
	 * argument which embeds the corresponding looping term
	 * and substitutions; else <code>null</code>
	 */
	public synchronized static ArgumentLoopByUnfolding deepMatchAndUnifyTest(UnfoldedRuleTrs R) {
		for (Position p : R.right) {
			UnfoldedRuleTrs R_copy = R.deepCopy();
			// Here, as we perform some deep tests,
			// we need to transform R_copy.left and
			// R_copy.right into functions (because
			// if R_copy.left is a tuple, then we
			// have a problem because the inner
			// subterms of R_copy.right are not tuples).
			Term left = R_copy.left.toFunction();
			Term right = R_copy.right.toFunction();
			Term right_p = right.get(p);

			// Subsumption test.
			Substitution theta2 = new Substitution(); 
			if (left.isMoreGeneralThan(right_p, theta2))
				return new ArgumentLoopByUnfolding(
						R_copy, true,
						p, left,
						new Substitution(), theta2);

			// Unification test.
			Substitution theta1 = new Substitution();
			if (left.unifyWith(right_p, theta1)) {
				return new ArgumentLoopByUnfolding(
						R_copy, true,
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
	 * 
	 * This method does not modify the provided rule.
	 * 
	 * @param R an unfolded rule
	 * @return if the test succeeds, then a non-termination
	 * argument which embeds the corresponding looping term
	 * and substitutions; else <code>null</code>
	 */
	public synchronized static ArgumentLoopByUnfolding shallowLeftUnifyTest(UnfoldedRuleTrs R) {
		// We do not need to copy R in order to apply
		// the left-unifiability test because this
		// test already copies and flattens R.

		// Moreover, as we perform a shallow test,
		// we do not need to transform R.left and
		// R.right into functions (because if
		// R.left is a tuple, so is R.right).

		// Left-unification test.
		Substitution theta1 = new Substitution();
		Substitution theta2 = new Substitution();
		if (R.left.leftUnifyWith(R.right, theta1, theta2))
			return new ArgumentLoopByUnfolding(
					R, false,
					new Position(),
					R.left.apply(theta1),
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
	 * @param IR the TRS used for applying <code>elim</code>
	 * @return the rules resulting from applying <code>elim</code>
	 * to this rule
	 */
	public abstract Collection<? extends UnfoldedRuleTrs> elim(Parameters parameters, Trs IR);

	/**
	 * Checks whether this rule is a non-termination witness.
	 * If this test succeeds, then builds a corresponding proof
	 * argument, adds it to the specified <code>proof</code> and
	 * returns a collection consisting of this rule only.
	 * Otherwise, applies the <code>elim</code> operator to this rule.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param IR the TRS used for applying <code>elim</code>
	 * @param proof the proof to build
	 * @return the rules resulting from applying <code>elim</code>
	 * to this rule
	 */
	public Collection<? extends UnfoldedRuleTrs> elimAndProve(Parameters parameters,
			Trs IR, Proof proof) {

		LinkedList<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		Argument A = this.nonTerminationTest();
		if (A == null)
			Result.addAll(this.elim(parameters, IR));
		else {
			// If this rule is a non-termination witness, then
			// build a corresponding proof argument.
			proof.setArgument(A);
			Result.add(this);
		}			

		return Result;
	}

	/**
	 * Adds the specified unfolded rule to the specified list.
	 *
	 * @param parameters parameters for applying <code>elim</code>
	 * @param IR the context of this operation
	 * @param proof a proof to build
	 * @param U the unfolded rule to be added
	 * @param Result the list to which the specified rule has to
	 * be added
	 * @return <code>true</code> iff we are in non-termination proof
	 * mode (i.e., <code>proof</code> is not <code>null</code>)
	 * and the specified rule is a proof argument
	 */
	protected synchronized static boolean add(Parameters parameters,
			Trs IR, Proof proof,
			UnfoldedRuleTrs U, LinkedList<UnfoldedRuleTrs> Result) {

		Result.addAll(
				proof == null ?
						U.elim(parameters, IR) :
							U.elimAndProve(parameters, IR, proof));

		// If we are in non-termination proof mode and if the rule U
		// is a proof argument, then stop everything.
		return proof != null && proof.isSuccess();
	}

	/**
	 * Adds the specified collection <code>C</code> to the specified
	 * collection <code>Result</code>.
	 *
	 * @return <code>true</code> iff the specified proof is a success
	 */
	protected synchronized static boolean addAll(Proof proof,
			Collection<? extends UnfoldedRuleTrs> C, Collection<UnfoldedRuleTrs> Result) {

		Result.addAll(C);

		return proof != null && proof.isSuccess();
	}

	/**
	 * Unfolds this rule forwards with the provided rule and
	 * at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param R the rule to use for unfolding this rule
	 * @param p a position in this rule at which the unfolding
	 * takes place
	 * @param iteration the iteration of the unfolding operator
	 * at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	public abstract Collection<? extends UnfoldedRuleTrs> unfoldForwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration);

	/**
	 * Unfolds this rule backwards with the provided rule and
	 * at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param R the rule to use for unfolding this rule
	 * @param p a position in this rule at which the unfolding
	 * takes place
	 * @param iteration the iteration of the unfolding operator
	 * at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	public abstract Collection<? extends UnfoldedRuleTrs> unfoldBackwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration);

	/**
	 * Unfolds this rule once using the rules of <code>IR</code>. 
	 * 
	 * Also applies <code>nonTerminationTest</code> to the computed
	 * unfolded rules if <code>proof</code> is not <code>null</code>;
	 * if <code>nonTerminationTest</code> succeeds for an unfolded rule,
	 * then the corresponding proof argument is added to <code>proof</code>.
	 * 
	 * @param parameters parameters for unfolding
	 * @param IR the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule
	 * @return the resulting unfolded rules
	 */
	public Collection<? extends UnfoldedRuleTrs> unfold(
			Parameters parameters, Trs IR, int iteration, Proof proof) {

		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		if (parameters.isForwardUnfoldingEnabled())
			// Forward unfolding is ON, hence we unfold this rule forwards.
			for (Position p : this.right) 
				for (RuleTrs R : IR) {
					Collection<? extends UnfoldedRuleTrs> unfoldedRules = 
							this.unfoldForwardsWith(parameters, R, p, iteration);
					for (UnfoldedRuleTrs U : unfoldedRules)
						if (add(parameters, IR, proof, U, Result))
							return Result;
				}

		if (parameters.isBackwardUnfoldingEnabled())
			// Backward unfolding is ON, hence we unfold this rule backwards.
			for (Position p: this.left)
				for (RuleTrs R : IR) {
					Collection<? extends UnfoldedRuleTrs> unfoldedRules = 
							this.unfoldBackwardsWith(parameters, R, p, iteration);
					for (UnfoldedRuleTrs U : unfoldedRules)
						if (add(parameters, IR, proof, U, Result))
							return Result;
				}

		return Result;
	}
}
