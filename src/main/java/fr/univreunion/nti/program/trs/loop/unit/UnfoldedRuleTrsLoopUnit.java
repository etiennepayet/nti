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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.loop.unit;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.Options;
import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An implementation of class <code>UnfoldedRuleTRS</code> used
 * in the technique based on dependency pairs (JAR version).
 * It implements a unit triple ie a triple of the form (N,_,_).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class UnfoldedRuleTrsLoopUnit extends UnfoldedRuleTrs {

	/**
	 * The component \cL of this triple.
	 */
	private final Set<RuleTrs> simpleCycle = new HashSet<RuleTrs>();

	/**
	 * Constructs a unit triple whose unique rule has the specified left-hand
	 * side and specified right-hand side.
	 * 
	 * @param left the left-hand side of the unique rule of this triple
	 * @param right the right-hand side of the unique rule of this triple
	 * @param iteration the iteration of the unfolding operator
	 * at which this triple is generated
	 * @param parent the parent of this triple
	 * @param simpleCycle the component \cL of this triple
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public UnfoldedRuleTrsLoopUnit(Function left, Term right,
			int iteration, ParentTrs parent,
			Collection<RuleTrs> simpleCycle) {

		super(left, right, iteration, parent);

		this.simpleCycle.addAll(simpleCycle);
	}

	/**
	 * Returns a deep copy of this rule i.e., a copy
	 * where each subterm is also copied.
	 * 
	 * @return a deep copy of this rule
	 */
	@Override
	public UnfoldedRuleTrsLoopUnit deepCopy() {
		return this.deepCopy(this.iteration, this.parent);
	}

	/**
	 * Returns a deep copy of this triple i.e., a copy
	 * where each subterm is also copied. The iteration
	 * and the parent of the generated copy is set to
	 * the specified iteration and parent.
	 * 
	 * @param iteration the iteration of the generated copy
	 * @param parent the parent of the generated copy
	 * @return a deep copy of this triple
	 */
	@Override
	public UnfoldedRuleTrsLoopUnit deepCopy(int iteration, ParentTrs parent) {
		HashMap<Term, Term> copies = new HashMap<Term, Term>();

		return new UnfoldedRuleTrsLoopUnit(
				(Function) this.left.deepCopy(copies),
				this.right.deepCopy(copies),
				iteration,
				parent,
				this.simpleCycle);
	}

	/**
	 * Implements a non-termination test over this rule.
	 * 
	 * @return a non-<code>null</code> non-termination argument
	 * if the test succeeds and <code>null</code> otherwise
	 */
	@Override
	public Argument nonTerminationTest() {
		// return deepMatchAndUnifyTest(this);
		return shallowLeftUnifyTest(this);
	}

	/**
	 * Applies the <code>elim</code> operator to this triple.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param IR the TRS used for applying <code>elim</code>
	 * @return the triples resulting from applying <code>elim</code>
	 * to this triple
	 */
	@Override
	public Collection<UnfoldedRuleTrsLoopUnit> elim(Parameters parameters, Trs IR) {
		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrsLoopUnit> Result = new LinkedList<UnfoldedRuleTrsLoopUnit>();

		int m = parameters.getMaxDepth();
		if (m < 0 || this.depth() <= m)
			// We only consider the rules that are not deeper than the pruning depth.
			/*
			if (!this.left.embeds(this.right)) {
				if (IR.descendants(this.right).contains(this.left) || 
						IR.ascendants(this.left).contains(this.right)) {
					// IR.addSimpleCycle(this.simpleCycle);
					Result.add(this);
				}
			}
			 */
			// Using ascendants and descendants as above is far too costly.
			// Hence, we prefer using connectivity:
			if (!this.left.embeds(this.right) && this.right.isConnectableTo(this.left, IR))
				Result.add(this);

		return Result;
	}

	/**
	 * Unfolds this rule forwards with the provided rule
	 * and at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param R the rule to use for unfolding this rule
	 * @param p a position in this rule at which the
	 * unfolding takes place
	 * @param iteration the iteration of the unfolding
	 * operator at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	@Override
	public Collection<UnfoldedRuleTrsLoopUnit> unfoldForwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		// The rules that will be returned.
		Collection<UnfoldedRuleTrsLoopUnit> Result = new LinkedList<UnfoldedRuleTrsLoopUnit>();

		// We try to unfold the right-hand side of this rule
		// forwards with the provided rule.
		HashMap<Term,Term> copies = new HashMap<Term,Term>();
		Term right = this.right.unfoldWith(
				R, p, false, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (right != null) {
			Term left = this.left.deepCopy(copies);

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
					ParentTrsLoopUnit.getInstance(this, R, p, false) : null);

			Result.add(new UnfoldedRuleTrsLoopUnit(
					(Function) left, right, iteration,
					parent,
					this.simpleCycle));
		}

		return Result;
	}

	/**
	 * Unfolds this rule backwards with the provided rule
	 * and at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param R the rule to use for unfolding this rule
	 * @param p a position in this rule at which the
	 * unfolding takes place
	 * @param iteration the iteration of the unfolding
	 * operator at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	@Override
	public Collection<UnfoldedRuleTrsLoopUnit> unfoldBackwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		// The rule that will be returned.
		Collection<UnfoldedRuleTrsLoopUnit> Result = new LinkedList<UnfoldedRuleTrsLoopUnit>();

		// We try to unfold the left-hand side of this rule
		// backwards with the provided rule.
		HashMap<Term,Term> copies = new HashMap<Term,Term>();
		Term left = this.left.unfoldWith(
				R, p, true, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (left != null) {
			Term right = this.right.deepCopy(copies);

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
					ParentTrsLoopUnit.getInstance(this, R, p, true) : null);

			Result.add(new UnfoldedRuleTrsLoopUnit(
					(Function) left, right, iteration,
					parent,
					this.simpleCycle));
		}

		return Result;
	}

	/**
	 * Applies the GU_R (guided unfolding) operator to this triple using
	 * the rules of <code>IR</code>. 
	 * 
	 * Also applies <code>nonTerminationTest</code> to the computed
	 * unfolded triples if <code>proof</code> is not <code>null</code>;
	 * if <code>nonTerminationTest</code> succeeds for an unfolded
	 * triple, then the corresponding proof argument is added to
	 * <code>proof</code>.
	 * 
	 * @param parameters parameters for unfolding
	 * @param IR the TRS used for unfolding this triple and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this triple
	 * @return the resulting unfolded triples
	 */
	@Override
	public Collection<UnfoldedRuleTrs> unfold( 
			Parameters parameters, Trs IR, int iteration, Proof proof) {

		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		StrategyLoop strategy = parameters.getStrategy();

		// We compute the disagreement positions of the 
		// left-hand side and the right-hand side of this rule.
		Collection<Position> D = this.left.dpos(
				this.right, parameters.isVariableUnfoldingEnabled());

		// We iterate through these disagreement positions.
		for (Position p : D) {
			if (currentThread.isInterrupted()) break;

			if (this.left.get(p).isVariable() && this.right.get(p).isVariable()) {
				if (addAll(proof,
						this.unfoldForwards_var(parameters, p, IR, iteration, proof),
						Result))
					break;
			}
			else {
				if (parameters.isForwardUnfoldingEnabled() &&
						addAll(proof,
								this.unfoldForwards(parameters, p, IR, iteration, proof),
								Result))
					break;
				if (parameters.isBackwardUnfoldingEnabled() &&
						addAll(proof,
								this.unfoldBackwards(parameters, p, IR, iteration, proof),
								Result))
					break;
			}
			if (strategy == StrategyLoop.LEFTMOST ||
					(strategy == StrategyLoop.LEFTMOST_NE && !Result.isEmpty()))
				break;
		}

		return Result;
	}

	/**
	 * Implements the F_R(l -> r, s, p) operation for the situation
	 * where the leftmost disagreement pair consists of two variables.
	 * 
	 * @param parameters parameters for unfolding
	 * @param p the position of a disagreement pair of r and s
	 * @param IR the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule forwards
	 * @return the resulting unfolded rules
	 */
	private Collection<UnfoldedRuleTrs> unfoldForwards_var(
			Parameters parameters, Position p, Trs IR, int iteration, Proof proof) {

		// The list to return at the end.
		LinkedList<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		for (RuleTrs R: IR) {
			if (currentThread.isInterrupted()) break;

			Collection<UnfoldedRuleTrsLoopUnit> unfoldedRules =
					this.unfoldForwardsWith(parameters, R, p, iteration);

			for (UnfoldedRuleTrsLoopUnit U : unfoldedRules)
				if (add(parameters, IR, proof, U, Result))
					return Result;
		}

		return Result;
	}

	/**
	 * Implements the F_R(l -> r, s, p) operation.
	 * 
	 * @param parameters parameters for unfolding
	 * @param p the position of a disagreement pair of r and s
	 * @param IR the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule forwards
	 * @return the resulting unfolded rules
	 */
	private Collection<UnfoldedRuleTrs> unfoldForwards(
			Parameters parameters, Position p, Trs IR, int iteration, Proof proof) {

		// The list to return at the end.
		LinkedList<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		// A boolean indicating whether we have to unfold at positions
		// deeper than p i.e., positions that include p as a prefix.
		boolean unfoldInner = false;

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// A boolean indicating whether we are in verbose mode.
		boolean verbose = Options.getInstance().isInVerboseMode();

		// First, we iterate through the non-empty prefixes of p.
		for (Position q = p; !q.isEmpty(); q = q.properPrefix()) {
			if (currentThread.isInterrupted()) break;

			Term r_q = this.right.get(q);
			if (!r_q.isVariable()) {
				boolean unfold_q = IR.descendants(r_q).contains(this.left.get(q));
				unfoldInner = unfoldInner || unfold_q;
				if (unfold_q) {
					// Part (1) of the definition of F_R.
					HashMap<Term,Term> copies = new HashMap<Term,Term>();
					Function left = (Function) this.left.deepCopy(copies);
					Term right = this.right.deepCopy(copies);
					if (left.get(q).unifyWith(right.get(q))) {
						// We need to build the parent only if we are in verbose mode.
						ParentTrs parent = (verbose ?
								ParentTrsLoopUnit.getInstance(this, null, q, false) : null);
						UnfoldedRuleTrs unfoldedRule =
								new UnfoldedRuleTrsLoopUnit(
										left, right, iteration,
										parent, this.simpleCycle);
						if (add(parameters, IR, proof, unfoldedRule, Result))
							return Result;
					}

					// Part (2) of the definition of F_R.
					// We unfold this rule forwards with the rules of IR.
					for (RuleTrs R: IR) {
						if (currentThread.isInterrupted()) break;

						Collection<UnfoldedRuleTrsLoopUnit> unfoldedRules =
								this.unfoldForwardsWith(parameters, R, q, iteration);

						for (UnfoldedRuleTrsLoopUnit U : unfoldedRules) {
							if(add(parameters, IR, proof, U, Result))
								return Result;

							// The following is not part of the definition of F_R (in LOPSTR'18).
							// We also try to guide the unfolding of r_q towards l_q.
							U = U.deepCopy();
							if (U.getLeft().get(q).unifyWith(U.getRight().get(q)) &&
									add(parameters, IR, proof, U, Result))
								return Result;
						}
					}
				}
			}
		}

		// Then, we consider the positions that are greater than p.
		if (!currentThread.isInterrupted() && unfoldInner) {
			Term r_p = this.right.get(p);
			for (Position pp: r_p) {
				if (currentThread.isInterrupted()) break;

				// Position p has already been handled above, while
				// iterating through the prefixes of p. 
				if (!pp.isEmpty() && !r_p.get(pp).isVariable())
					// Part (2) of the definition of F_R.
					for (RuleTrs R: IR) {
						if (currentThread.isInterrupted()) break;

						Collection<UnfoldedRuleTrsLoopUnit> unfoldedRules =
								this.unfoldForwardsWith(parameters, R,
										p.append(pp), iteration);

						for (UnfoldedRuleTrsLoopUnit U : unfoldedRules)
							if (add(parameters, IR, proof, U, Result))
								return Result;
					}
			}
		}

		return Result;
	}

	/**
	 * Implements the B_R(s -> t, r, p) operation.
	 * 
	 * @param parameters parameters for unfolding
	 * @param p the position of a disagreement pair of t and r
	 * @param IR the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule backwards
	 * @return the resulting unfolded rules
	 */
	private Collection<UnfoldedRuleTrs> unfoldBackwards(
			Parameters parameters, Position p, Trs IR, int iteration, Proof proof) {

		// The list to return at the end.
		LinkedList<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		// A boolean indicating whether we have to unfold at positions
		// deeper than p i.e., positions that include p as a prefix.
		boolean unfoldInner = false;

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// A boolean indicating whether we are in verbose mode.
		boolean verbose = Options.getInstance().isInVerboseMode();

		// First, we iterate through the non-empty prefixes of p.
		for (Position q = p; !q.isEmpty(); q = q.properPrefix()) {
			if (currentThread.isInterrupted()) break;

			Term l_q = this.left.get(q);
			if (!l_q.isVariable()) {
				boolean unfold_q = IR.ascendants(l_q).contains(this.right.get(q));
				unfoldInner = unfoldInner || unfold_q;
				if (unfold_q) {
					// Part (1) of the definition of B_R.
					HashMap<Term,Term> copies = new HashMap<Term,Term>();
					Function left = (Function) this.left.deepCopy(copies);
					Term right = this.right.deepCopy(copies);
					if (left.get(q).unifyWith(right.get(q))) {
						// We need to build the parent only if we are in verbose mode.
						ParentTrs parent = (verbose ?
								ParentTrsLoopUnit.getInstance(this, null, q, true) : null);
						UnfoldedRuleTrs unfoldedRule =
								new UnfoldedRuleTrsLoopUnit(
										left, right, iteration,
										parent, this.simpleCycle);
						if (add(parameters, IR, proof, unfoldedRule, Result))
							return Result;
					}

					// Part (2) of the definition of B_R.
					// We unfold this rule backwards with the rules of IR.
					for (RuleTrs R: IR) {
						if (currentThread.isInterrupted()) break;

						Collection<UnfoldedRuleTrsLoopUnit> unfoldedRules =
								this.unfoldBackwardsWith(parameters, R, q, iteration);

						for (UnfoldedRuleTrsLoopUnit U : unfoldedRules) {
							if (add(parameters, IR, proof, U, Result))
								return Result;

							// The following is not part of the definition of B_R (in LOPSTR'18).
							// We also try to guide the unfolding of l_q towards r_q.
							U = U.deepCopy();
							if (U.getRight().get(q).unifyWith(U.getLeft().get(q)) &&
									add(parameters, IR, proof, U, Result))
								return Result;
						}
					}
				}
			}
		}

		// Then, we consider the positions that are greater than p.
		if (!currentThread.isInterrupted() && unfoldInner) {
			Term l_p = this.left.get(p);
			for (Position pp: l_p) {
				if (currentThread.isInterrupted()) break;

				// Position p has already been handled above, while
				// iterating through the prefixes of p. 
				if (!pp.isEmpty() && !l_p.get(pp).isVariable())
					// Part (2) of the definition of B_R.
					for (RuleTrs R: IR) {
						if (currentThread.isInterrupted()) break;

						Collection<UnfoldedRuleTrsLoopUnit> unfoldedRules =
								this.unfoldBackwardsWith(parameters, R,
										p.append(pp), iteration);

						for (UnfoldedRuleTrsLoopUnit U : unfoldedRules)
							if (add(parameters, IR, proof, U, Result))
								return Result;
					}
			}
		}

		return Result;
	}

	/**
	 * Returns a String representation of this triple
	 * relatively to the given set of variable symbols.
	 * 
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this triple: it stops at
	 * variable positions i.e., it does not consider the
	 * parent of a variable position.
	 * 
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this triple.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this triple
	 * @return a String representation of this triple
	 */
	@Override
	public String toString(Map<Variable,String> variables, boolean shallow) {
		return super.toString(variables, shallow) + " [unit]";
	}

	/**
	 * Returns a String representation of this triple.
	 *
	 * @return a String representation of this triple
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<Variable,String>(), false);
	}
}
