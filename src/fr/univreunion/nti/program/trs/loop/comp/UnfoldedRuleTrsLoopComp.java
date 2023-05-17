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

package fr.univreunion.nti.program.trs.loop.comp;

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Path;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.RecurrentPair;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.argument.ArgumentRecurrentPairTrs;
import fr.univreunion.nti.program.trs.loop.trans.UnfoldedRuleTrsLoopTrans;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An implementation of class <code>UnfoldedRuleTRS</code> used
 * in the technique based on dependency pairs (JAR version).
 * It implements a composed triple, i.e., a triple of the form
 * (N::N',\cN,\cL).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class UnfoldedRuleTrsLoopComp extends UnfoldedRuleTrs {

	/**
	 * The first rule (i.e., N) of this triple is defined
	 * by this.left and this.right.
	 * 
	 * Moreover, the path corresponding to this first rule
	 * is stored in this.path.
	 */


	/**
	 * The component \cN of this triple.
	 */
	private final Deque<RuleTrs> scc = new LinkedList<RuleTrs>();

	/**
	 * The component \cL of this triple.
	 */
	private final Set<RuleTrs> simpleCycle = new HashSet<RuleTrs>();

	/**
	 * The second rule of this triple i.e., N'.
	 */
	private final RuleTrs second;

	/**
	 * The path corresponding to the second rule (i.e., N')
	 * of this triple.
	 */
	private final Path pathSecond = new Path();

	/**
	 * Builds a composed triple from the specified parameters.
	 * If the two rules of the triple can be merged, then also
	 * builds a transitory triple resulting from merging these
	 * two rules.
	 * 
	 * @param left the left-hand side of the first rule of the
	 * composed triple
	 * @param right the right-hand side of the first rule of the
	 * composed triple
	 * @param iteration the iteration of the unfolding operator
	 * at which the composed triple is generated
	 * @param parent the parent of the composed triple
	 * @param pathFirst the path in the program being unfolded that
	 * corresponds to the first rule of the composed triple
	 * @param second the second rule of the composed triple
	 * @param pathSecond the path in the program being unfolded
	 * that corresponds to the second rule of this triple
	 * @param scc the component \cN of the composed triple
	 * @param simpleCycle the component \cL of the composed triple
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public synchronized static Collection<UnfoldedRuleTrs> getInstances(
			Function left, Term right,
			int iteration, ParentTrs parent, Path pathFirst,
			RuleTrs second, Path pathSecond,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		// The triples to return at the end.
		Collection<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		// We first build a composed triple consisting of the
		// specified two rules ("left -> right" and "second").
		Result.add(new UnfoldedRuleTrsLoopComp(
				left, right, iteration, parent, pathFirst,
				second, pathSecond, scc, simpleCycle));

		// We also check whether "right" unifies with the left-hand
		// side of "second". If the test succeeds, then we build a
		// transitory triple resulting from merging the two rules
		// of the composed triple built above.
		HashMap<Term,Term> copies = new HashMap<Term,Term>();
		Function leftCopy = (Function) left.deepCopy(copies);
		Term rightCopy = right.deepCopy(copies);

		RuleTrs secondCopy = second.deepCopy();

		if (rightCopy.unifyWith(secondCopy.getLeft())) {
			// This is a forward unfolding of the first rule of
			// this triple with its second rule. We compute the
			// corresponding path as follows.
			Path updatedPath = new Path();
			updatedPath.addAll(pathFirst);
			updatedPath.addAll(pathSecond);

			Result.addAll(UnfoldedRuleTrsLoopTrans.getUnfoldedInstances(
					leftCopy, secondCopy.getRight(),
					iteration, parent, updatedPath, scc, simpleCycle));
		}

		return Result;
	}

	/**
	 * Builds a composed triple from the specified parameters.
	 * 
	 * @param left the left-hand side of the first rule of this triple
	 * @param right the right-hand side of the first rule of this triple
	 * @param iteration the iteration of the unfolding operator
	 * at which this triple is generated
	 * @param parent the parent of this triple
	 * @param path the path in the program being unfolded that
	 * corresponds to the first rule of this triple
	 * @param second the second rule of this triple
	 * @param pathSecond the path in the program being unfolded
	 * that corresponds to the second rule of this triple
	 * @param scc the component \cN of this triple
	 * @param simpleCycle the component \cL of this triple
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	private UnfoldedRuleTrsLoopComp(Function left, Term right, 
			int iteration, ParentTrs parent, Path path,
			RuleTrs second, Path pathSecond,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		super(left, right, iteration, parent, path);

		if (second == null)
			throw new IllegalArgumentException(
					"cannot build a composed syntactic loop with a null second rule");

		this.scc.addAll(scc);
		this.simpleCycle.addAll(simpleCycle);

		this.second = second;
		this.pathSecond.addAll(pathSecond);
	}

	/**
	 * Returns the first rule (i.e., N) of this composed triple.
	 *  
	 * @return the first rule of this composed triple
	 */
	public RuleTrs getFirst() {
		return new RuleTrs(this.left, this.right);
	}

	/**
	 * Returns the second rule (i.e., N') of this composed triple.
	 *  
	 * @return the second rule of this composed triple
	 */
	public RuleTrs getSecond() {
		return this.second;
	}

	/**
	 * Returns the path (in the unfolded program) corresponding
	 * to the first rule of this triple.
	 * 
	 * @return the path (in the unfolded program) corresponding
	 * to the first rule of this triple
	 */
	public Path getPathFirst() {
		return this.path;
	}

	/**
	 * Returns the path (in the unfolded program) corresponding
	 * to the second rule of this triple.
	 * 
	 * @return the path (in the unfolded program) corresponding
	 * to the second rule of this triple
	 */
	public Path getPathSecond() {
		return this.pathSecond;
	}

	/**
	 * Returns a deep copy of this rule i.e., a copy
	 * where each subterm is also copied.
	 * 
	 * @return a deep copy of this rule
	 */
	@Override
	public UnfoldedRuleTrsLoopComp deepCopy() {
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
	public UnfoldedRuleTrsLoopComp deepCopy(int iteration, ParentTrs parent) {
		HashMap<Term, Term> copies = new HashMap<Term, Term>();

		return new UnfoldedRuleTrsLoopComp(
				(Function) this.left.deepCopy(copies),
				this.right.deepCopy(copies),
				iteration,
				parent,
				this.path,
				this.second.deepCopy(),
				this.pathSecond,
				this.scc,
				this.simpleCycle);
	}

	/**
	 * Returns the depth of this rule (max depth of
	 * its left-hand side, its right-hand side, the
	 * left-hand side of its second rule and the
	 * right-hand side of its second rule).
	 * 
	 * @return the depth of this rule
	 */
	@Override
	public int depth() {
		int depth_l1 = this.left.depth();
		int depth_r1 = this.right.depth();
		int max1 = (depth_l1 > depth_r1 ? depth_l1 : depth_r1);

		int depth_l2 = this.second.getLeft().depth();
		int depth_r2 = this.second.getRight().depth();
		int max2 = (depth_l2 > depth_r2 ? depth_l2 : depth_r2);

		return (max1 > max2 ? max1 : max2);
	}

	/**
	 * Implements a non-termination test over this rule.
	 * 
	 * @return a non-<code>null</code> non-termination argument
	 * if the test succeeds and <code>null</code> otherwise
	 */
	@Override
	public Argument nonTerminationTest() {		
		Argument A;

		// First, we try a shallow left-unify test.
		if ((A = shallowLeftUnifyTest(this)) != null)
			return A;

		// If the left-unify test fails, then we try to build
		// a recurrent pair for this rule.
		Function l1 = this.getLeft();
		Term r1 = this.getRight();
		Function l2 = this.second.getLeft();
		Term r2 = this.second.getRight();

		RecurrentPair recPair;
		if ((recPair = RecurrentPair.getInstance(l1, r1, l2, r2)) != null)
			// Here, a recurrent pair could be built.
			A = new ArgumentRecurrentPairTrs(recPair, this);

		return A;
	}

	/**
	 * THIS ONE WAS USED BEFORE WE IMPLEMENTED RECURRENT PAIRS.
	 * SEE ALSO elimAndProve BELOW.
	 * 
	 * Implements a non-termination test over this rule.
	 * 
	 * @return a non-<code>null</code> non-termination argument
	 * if the test succeeds and <code>null</code> otherwise
	 */
	/*
	@Override
	public Argument nonTerminationTest() {
		// return deepMatchAndUnifyTest(this);
		return shallowLeftUnifyTest(this);
	}
	 */

	/**
	 * Applies the <code>elim</code> operator to this triple.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param IR the TRS used for applying <code>elim</code>
	 * @return the triple resulting from applying <code>elim</code>
	 * to this triple
	 */
	@Override
	public Collection<UnfoldedRuleTrsLoopComp> elim(Parameters parameters, Trs IR) {
		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrsLoopComp> Result = new LinkedList<UnfoldedRuleTrsLoopComp>();

		int m = parameters.getMaxDepth();
		if (m < 0 || this.depth() <= m)
			// We only consider the rules that are not deeper than the pruning depth.
			if (!this.scc.isEmpty() || !IR.containsSimpleCycle(this.simpleCycle)) {
				Term t = this.second.getLeft();
				/*
						if (IR.descendants(this.right).contains(t) || 
								IR.ascendants(t).contains(this.right))
							Result.add(this);
				 */
				// Using ascendants and descendants as above is far too costly.
				// Hence, we prefer using connectivity:
				if (this.right.isConnectableTo(t, IR))
					Result.add(this);
			}

		return Result;
	}

	/**
	 * THIS ONE WAS USED BEFORE WE IMPLEMENTED RECURRENT PAIRS.
	 * SEE ALSO nonTerminationTest ABOVE.
	 * 
	 * Just applies the <code>elim</code> operator to this triple as
	 * composed triples cannot be non-termination witnesses.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param IR the TRS used for applying <code>elim</code>
	 * @param proof the proof to build
	 * @return the triples resulting from applying <code>elim</code>
	 * to this triple
	 */
	/*
	@Override
	public Collection<UnfoldedRuleTRS_Loop_Comp> elimAndProve(Parameters parameters,
			TRS IR, Proof proof) {

		return this.elim(parameters, IR);
	}
	 */

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
	public Collection<UnfoldedRuleTrs> unfoldForwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		// The rules that will be returned.
		Collection<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		// We try to unfold the right-hand side of this rule
		// forwards with the provided rule.
		HashMap<Term,Term> copies = new HashMap<Term, Term>();
		Term right = this.right.unfoldWith(
				R, p, false, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (right != null) {
			Function left = (Function) this.left.deepCopy(copies);

			ParentTrs parent = ParentTrsLoopComp.getInstance(this, R, p, false);

			Path path = new Path();
			path.addAll(this.path);
			path.addLast​(R);

			Result.addAll(UnfoldedRuleTrsLoopComp.getInstances(
					left, right, iteration, parent, path,
					this.second, this.pathSecond,
					this.scc, this.simpleCycle));
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
	public Collection<UnfoldedRuleTrs> unfoldBackwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		// The rule that will be returned.
		Collection<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();

		// We try to unfold the left-hand side of the
		// second rule backwards with the provided rule.
		HashMap<Term,Term> copies = new HashMap<Term, Term>();
		Term left = this.second.getLeft().unfoldWith(
				R, p, true, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (left != null) {
			Term right = this.second.getRight().deepCopy(copies);

			ParentTrs parent = ParentTrsLoopComp.getInstance(this, R, p, true);

			Path pathSecond = new Path(R);
			pathSecond.addAll(this.pathSecond);

			Result.addAll(UnfoldedRuleTrsLoopComp.getInstances(
					this.left, this.right, iteration, parent, this.path,
					new RuleTrs((Function) left, right), pathSecond,
					this.scc, this.simpleCycle));
		}

		return Result;
	}

	/**
	 * Applies the GU_R (guided unfolding) operator to this triple using
	 * the rules of <code>IR</code>. 
	 * 
	 * Also applies <code>nonTerminationTest</code> to the computed
	 * unfolded rules if <code>proof</code> is not <code>null</code>;
	 * if <code>nonTerminationTest</code> succeeds for an unfolded rule,
	 * then the corresponding proof argument is added to <code>proof</code>.
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
		// left-hand side of the second rule and the
		// right-hand side of this rule.
		Collection<Position> D = this.second.getLeft().dpos(this.right, false);

		// We iterate through these disagreement positions.
		for (Position p : D) {
			if (currentThread.isInterrupted()) break;

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
			if (strategy == StrategyLoop.LEFTMOST ||
					(strategy == StrategyLoop.LEFTMOST_NE && !Result.isEmpty()))
				break;
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

		// The term that guides the forward unfolding.
		Term l = this.second.getLeft();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// First, we iterate through the non-empty prefixes of p.
		for (Position q = p; !q.isEmpty(); q = q.properPrefix()) {
			if (currentThread.isInterrupted()) break;

			Term r_q = this.right.get(q);
			if (!r_q.isVariable()) {
				Term l_q = l.get(q);
				boolean unfold_q = IR.descendants(r_q).contains(l_q);
				unfoldInner = unfoldInner || unfold_q;
				if (unfold_q) {
					// Part (1) of the definition of F_R.
					ParentTrs parent = ParentTrsLoopComp.getInstance(this, null, q, false);
					UnfoldedRuleTrsLoopComp thisCopy = this.deepCopy(iteration, parent);

					if (thisCopy.getRight().get(q).unifyWith(
							thisCopy.second.getLeft().get(q)) &&
							add(parameters, IR, proof, thisCopy, Result))
						return Result;

					// Part (2) of the definition of F_R.
					// We unfold this rule forwards with the rules of IR.
					boolean isNotVar_l_q = !l_q.isVariable();
					for (RuleTrs R: IR) {
						if (currentThread.isInterrupted()) break;

						Collection<UnfoldedRuleTrs> unfoldedRules =
								this.unfoldForwardsWith(parameters, R, q, iteration);

						for (UnfoldedRuleTrs U : unfoldedRules) {
							if (add(parameters, IR, proof, U, Result))
								return Result;

							// The following is not part of the definition of F_R (in LOPSTR'18).
							// We also try to guide the unfolding of r_q towards l_q.
							// But we do this only if l_q is not a variable because otherwise we 
							// would generate a second occurrence of the unfolded rule.
							if ((U instanceof UnfoldedRuleTrsLoopComp) &&
									isNotVar_l_q) {
								UnfoldedRuleTrsLoopComp V = ((UnfoldedRuleTrsLoopComp) U).deepCopy();
								if (V.second.getLeft().get(q).unifyWith(V.getRight().get(q)) &&
										add(parameters, IR, proof, V, Result))
									return Result;							
							}
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

						Collection<UnfoldedRuleTrs> unfoldedRules =
								this.unfoldForwardsWith(parameters, R,
										p.append(pp), iteration);

						for (UnfoldedRuleTrs U : unfoldedRules)
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

		// The term to unfold backwards.
		Term l = this.second.getLeft();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// First, we iterate through the non-empty prefixes of p.
		for (Position q = p; !q.isEmpty(); q = q.properPrefix()) {
			if (currentThread.isInterrupted()) break;

			Term l_q = l.get(q);
			if (!l_q.isVariable()) {
				Term r_q = this.right.get(q);
				boolean unfold_q = IR.ascendants(l_q).contains(r_q);
				unfoldInner = unfoldInner || unfold_q;
				if (unfold_q) {
					// Part (1) of the definition of B_R.
					ParentTrs parent = ParentTrsLoopComp.getInstance(this, null, q, true);
					UnfoldedRuleTrsLoopComp thisCopy = this.deepCopy(iteration, parent);

					if (thisCopy.getRight().get(q).unifyWith(
							thisCopy.second.getLeft().get(q)) &&
							add(parameters, IR, proof, thisCopy, Result))
						return Result;

					// Part (2) of the definition of B_R.
					// We unfold this rule backwards with the rules of IR.	
					boolean isNotVar_r_q = !r_q.isVariable();
					for (RuleTrs R: IR) {
						if (currentThread.isInterrupted()) break;

						Collection<UnfoldedRuleTrs> unfoldedRules =
								this.unfoldBackwardsWith(parameters, R, q, iteration);

						for (UnfoldedRuleTrs U : unfoldedRules) {
							if (add(parameters, IR, proof, U, Result))
								return Result;

							// The following is not part of the definition of B_R (in LOPSTR'18).
							// We also try to guide the unfolding of l_q towards r_q.
							// But we do this only if r_q is not a variable because otherwise we 
							// would generate a second occurrence of the unfolded rule.
							if ((U instanceof UnfoldedRuleTrsLoopComp) &&
									isNotVar_r_q) {
								UnfoldedRuleTrsLoopComp V = ((UnfoldedRuleTrsLoopComp) U).deepCopy();
								if (V.second.getLeft().get(q).unifyWith(V.getRight().get(q)) &&
										add(parameters, IR, proof, V, Result))
									return Result;							
							}
						}
					}
				}
			}
		}

		// Then, we consider the positions that are greater than p.
		if (!currentThread.isInterrupted() && unfoldInner) {
			Term l_p = l.get(p);
			for (Position pp: l_p) {
				if (currentThread.isInterrupted()) break;

				// Position p has already been handled above, while
				// iterating through the prefixes of p. 
				if (!pp.isEmpty() && !l_p.get(pp).isVariable())
					// Part (2) of the definition of B_R.
					for (RuleTrs R: IR) {
						if (currentThread.isInterrupted()) break;

						Collection<UnfoldedRuleTrs> unfoldedRules =
								this.unfoldBackwardsWith(parameters, R,
										p.append(pp), iteration);

						for (UnfoldedRuleTrs U : unfoldedRules)
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
		return "[" + super.toString(variables, shallow) +
				", " + this.second.toString(variables, shallow) +
				"] [comp]";
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
