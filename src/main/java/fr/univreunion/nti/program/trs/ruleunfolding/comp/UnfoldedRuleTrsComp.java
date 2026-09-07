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

package fr.univreunion.nti.program.trs.ruleunfolding.comp;

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.recurrentpair.RecurrentPair;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.program.trs.argument.ArgumentRecurrentPairTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.trans.UnfoldedRuleTrsTrans;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An unfolded TRS rule used in the technique based on rule unfolding.
 * It implements a composed triple, i.e., a triple of the form
 * (N::N',\cN,\cL).
 *
 * <p>The first rule (i.e., N) of this triple is represented by the inherited
 * {@code left} and {@code right} fields.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class UnfoldedRuleTrsComp extends UnfoldedRuleTrs {

	/**
	 * The component \cN of this triple.
	 */
	private final Deque<RuleTrs> scc = new LinkedList<>();

	/**
	 * The component \cL of this triple.
	 */
	private final Set<RuleTrs> simpleCycle = new HashSet<>();

	/**
	 * The second rule of this triple, i.e., N'.
	 */
	private final RuleTrs second;

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
	 * @param second the second rule of the composed triple
	 * @param scc the component \cN of the composed triple
	 * @param simpleCycle the component \cL of the composed triple
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public static synchronized Collection<UnfoldedRuleTrs> getInstances(
			Function left, Term right,
			int iteration, ParentTrs parent, RuleTrs second,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		// The triples to return at the end.
		Collection<UnfoldedRuleTrs> result = new LinkedList<>();

		// We first build a composed triple consisting of the
		// specified two rules ("left -> right" and "second").
		result.add(new UnfoldedRuleTrsComp(
				left, right, iteration, parent,
				second, scc, simpleCycle));

		// We also check whether "right" unifies with the left-hand
		// side of "second". If the test succeeds, then we build a
		// transitory triple resulting from merging the two rules
		// of the composed triple built above.
		HashMap<Term,Term> copies = new HashMap<>();
		Function leftCopy = (Function) left.deepCopy(copies);
		Term rightCopy = right.deepCopy(copies);

		RuleTrs secondCopy = second.deepCopy();

		if (rightCopy.unifyWith(secondCopy.getLeft()))
			// This is a forward unfolding of the first rule of
			// this triple with its second rule.
			result.addAll(UnfoldedRuleTrsTrans.getUnfoldedInstances(
					leftCopy, secondCopy.getRight(),
					iteration, parent, scc, simpleCycle));

		return result;
	}

	/**
	 * Builds a composed triple from the specified parameters.
	 *
	 * @param left the left-hand side of the first rule of this triple
	 * @param right the right-hand side of the first rule of this triple
	 * @param iteration the iteration of the unfolding operator
	 * at which this triple is generated
	 * @param parent the parent of this triple
	 * @param second the second rule of this triple
	 * @param scc the component \cN of this triple
	 * @param simpleCycle the component \cL of this triple
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	private UnfoldedRuleTrsComp(Function left, Term right,
			int iteration, ParentTrs parent, RuleTrs second,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		super(left, right, iteration, parent);

		if (second == null)
			throw new IllegalArgumentException(
					"cannot build a composed syntactic loop with a null second rule");

		this.scc.addAll(scc);
		this.simpleCycle.addAll(simpleCycle);

		this.second = second;
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
	 * Returns a deep copy of this rule i.e., a copy
	 * where each subterm is also copied.
	 *
	 * @return a deep copy of this rule
	 */
	@Override
	public UnfoldedRuleTrsComp deepCopy() {
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
	public UnfoldedRuleTrsComp deepCopy(int iteration, ParentTrs parent) {
		HashMap<Term, Term> copies = new HashMap<>();

		return new UnfoldedRuleTrsComp(
				(Function) this.left.deepCopy(copies),
				this.right.deepCopy(copies),
				iteration,
				parent,
				this.second.deepCopy(),
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
		int firstLeftDepth = this.left.depth();
		int firstRightDepth = this.right.depth();
		int firstMaximum = Math.max(firstLeftDepth, firstRightDepth);

		int secondLeftDepth = this.second.getLeft().depth();
		int secondRightDepth = this.second.getRight().depth();
		int secondMaximum = Math.max(secondLeftDepth, secondRightDepth);

		return Math.max(firstMaximum, secondMaximum);
	}

	/**
	 * Implements a non-termination test over this rule.
	 *
	 * @return a non-<code>null</code> non-termination argument
	 * if the test succeeds and <code>null</code> otherwise
	 */
	@Override
	public Argument nonTerminationTest() {
		Argument argument;

		// First, we try a shallow left-unify test.
		if ((argument = shallowLeftUnifyTest(this)) != null)
			return argument;

		// If the left-unify test fails, then we try to build
		// a recurrent pair for this rule.
		Function l1 = this.getLeft();
		Term r1 = this.getRight();
		Function l2 = this.second.getLeft();
		Term r2 = this.second.getRight();

		RecurrentPair recPair;
		if ((recPair = RecurrentPair.tryBuild(l1, r1, l2, r2)) != null)
			// Here, a recurrent pair could be built.
			argument = new ArgumentRecurrentPairTrs(recPair, this);

		return argument;
	}

	/**
	 * Applies the <code>elim</code> operator to this triple.
	 *
	 * @param parameters parameters for applying <code>elim</code>
	 * @param trs the TRS used for applying <code>elim</code>
	 * @return the triple resulting from applying <code>elim</code>
	 * to this triple
	 */
	@Override
	public Collection<UnfoldedRuleTrs> elim(
			Parameters parameters, Trs trs, SimpleCycleRegistry simpleCycles) {
		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();

		int m = parameters.getMaxDepth();
		// We only consider rules that are not deeper than the pruning depth.
		// Using ascendants and descendants is far too costly, hence connectivity.
		if ((m < 0 || this.depth() <= m) &&
				(!this.scc.isEmpty() || !simpleCycles.contains(this.simpleCycle)) &&
				this.right.isConnectableTo(this.second.getLeft(), trs))
			result.add(this);

		return result;
	}

	/**
	 * Unfolds this rule forwards with the provided rule
	 * and at the provided position.
	 *
	 * @param parameters parameters for unfolding
	 * @param rule the rule to use for unfolding this rule
	 * @param p a position in this rule at which the
	 * unfolding takes place
	 * @param iteration the iteration of the unfolding
	 * operator at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	@Override
	public Collection<UnfoldedRuleTrs> unfoldForwardsWith(
			Parameters parameters, RuleTrs rule, Position p, int iteration) {

		// The rules that will be returned.
		Collection<UnfoldedRuleTrs> result = new LinkedList<>();

		// We try to unfold the right-hand side of this rule
		// forwards with the provided rule.
		HashMap<Term,Term> copies = new HashMap<>();
		Term right = this.right.unfoldWith(
				rule, p, false, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (right != null) {
			Function left = (Function) this.left.deepCopy(copies);

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (parameters.isInVerboseMode() ?
					ParentTrsComp.of(this, rule, p, false) : null);

			result.addAll(UnfoldedRuleTrsComp.getInstances(
					left, right, iteration, parent,
					this.second, this.scc, this.simpleCycle));
		}

		return result;
	}

	/**
	 * Unfolds this rule backwards with the provided rule
	 * and at the provided position.
	 *
	 * @param parameters parameters for unfolding
	 * @param rule the rule to use for unfolding this rule
	 * @param p a position in this rule at which the
	 * unfolding takes place
	 * @param iteration the iteration of the unfolding
	 * operator at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	@Override
	public Collection<UnfoldedRuleTrs> unfoldBackwardsWith(
			Parameters parameters, RuleTrs rule, Position p, int iteration) {

		// The rule that will be returned.
		Collection<UnfoldedRuleTrs> result = new LinkedList<>();

		// We try to unfold the left-hand side of the
		// second rule backwards with the provided rule.
		HashMap<Term,Term> copies = new HashMap<>();
		Term left = this.second.getLeft().unfoldWith(
				rule, p, true, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (left != null) {
			Term right = this.second.getRight().deepCopy(copies);

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (parameters.isInVerboseMode() ?
					ParentTrsComp.of(this, rule, p, true) : null);

			result.addAll(UnfoldedRuleTrsComp.getInstances(
					this.left, this.right, iteration, parent,
					new RuleTrs((Function) left, right),
					this.scc, this.simpleCycle));
		}

		return result;
	}

	/**
	 * Applies the GU_R (guided unfolding) operator to this triple using
	 * the rules of <code>trs</code>.
	 * <p>
	 * Also applies <code>nonTerminationTest</code> to the computed
	 * unfolded rules if <code>proof</code> is not <code>null</code>;
	 * if <code>nonTerminationTest</code> succeeds for an unfolded rule,
	 * then the corresponding proof argument is added to <code>proof</code>.
	 *
	 * @param parameters parameters for unfolding
	 * @param trs the TRS used for unfolding this triple and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this triple
	 * @return the resulting unfolded triples
	 */
	@Override
	public Collection<UnfoldedRuleTrs> unfold(
			Parameters parameters, Trs trs, SimpleCycleRegistry simpleCycles,
			int iteration, Proof proof) {

		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();

		StrategyLoop strategy = parameters.getStrategy();

		// We compute the disagreement positions of the
		// left-hand side of the second rule and the
		// right-hand side of this rule.
		Collection<Position> disagreementPositions =
				this.second.getLeft().dpos(this.right, false);

		Iterator<Position> positions = disagreementPositions.iterator();
		boolean stop = false;
		while (!Thread.currentThread().isInterrupted() && !stop && positions.hasNext()) {
			Position position = positions.next();
			stop = this.unfoldAtDisagreement(
					parameters, position, trs, simpleCycles, iteration, proof, result);
			stop = stop || strategy == StrategyLoop.LEFTMOST ||
					(strategy == StrategyLoop.LEFTMOST_NE && !result.isEmpty());
		}

		return result;
	}

	/**
	 * Applies the enabled guided-unfolding operations at one disagreement
	 * position and appends their results in generation order.
	 *
	 * @param parameters parameters controlling guided unfolding
	 * @param position the current disagreement position
	 * @param trs the TRS used for unfolding and elimination
	 * @param simpleCycles the registry of simple cycles already processed
	 * @param iteration the current unfolding iteration
	 * @param proof the proof receiving a nontermination argument, or
	 * <code>null</code> when no proof is being built
	 * @param result the ordered collection receiving generated rules
	 * @return <code>true</code> iff a generated rule completed the proof
	 */
	private boolean unfoldAtDisagreement(
			Parameters parameters, Position position, Trs trs,
			SimpleCycleRegistry simpleCycles, int iteration, Proof proof,
			LinkedList<UnfoldedRuleTrs> result) {

		if (parameters.isForwardUnfoldingEnabled() &&
				addAll(proof,
						this.unfoldForwards(
								parameters, position, trs, simpleCycles, iteration, proof),
						result))
			return true;

		return parameters.isBackwardUnfoldingEnabled() &&
				addAll(proof,
						this.unfoldBackwards(
								parameters, position, trs, simpleCycles, iteration, proof),
						result);
	}

	/**
	 * Implements the F_R(l -> r, s, p) operation.
	 *
	 * @param parameters parameters for unfolding
	 * @param p the position of a disagreement pair of r and s
	 * @param trs the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule forwards
	 * @return the resulting unfolded rules
	 */
	private Collection<UnfoldedRuleTrs> unfoldForwards(
			Parameters parameters, Position p, Trs trs,
			SimpleCycleRegistry simpleCycles, int iteration, Proof proof) {

		// The list to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();
		ForwardUnfoldingContext context = new ForwardUnfoldingContext(
				parameters, trs, simpleCycles, iteration, proof, result);

		// A boolean indicating whether we have to unfold at positions
		// deeper than p i.e., positions that include p as a prefix.
		boolean unfoldInner = false;

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// First, we iterate through the non-empty prefixes of p.
		for (Position q = p; !q.isEmpty(); q = q.properPrefix()) {
			if (currentThread.isInterrupted()) break;

			unfoldInner = this.unfoldForwardsAtPrefix(context, q) || unfoldInner;
			if (proof != null && proof.isSuccess()) return result;
		}

		// Then, we consider the positions that are greater than p.
		if (!currentThread.isInterrupted() && unfoldInner)
			this.unfoldForwardsBelowPosition(context, p);

		return result;
	}

	/**
	 * Applies the prefix-oriented parts of the forward guided-unfolding
	 * operation at the specified position.
	 *
	 * @param context the parameters, TRS, cycle registry, iteration, proof and
	 * result collection shared by this forward-unfolding operation
	 * @param position a non-empty prefix of the disagreement position
	 * @return <code>true</code> iff unfolding is enabled at
	 * <code>position</code>, in which case positions below the disagreement
	 * position must also be considered
	 */
	private boolean unfoldForwardsAtPrefix(
			ForwardUnfoldingContext context, Position position) {

		Term rightAtPosition = this.right.get(position);
		if (rightAtPosition.isVariable()) return false;

		Term guideAtPosition = this.second.getLeft().get(position);
		boolean unfoldAtPosition = context.trs().descendants(rightAtPosition)
				.contains(guideAtPosition);
		if (!unfoldAtPosition) return false;

		if (this.addForwardUnifiedCopy(context, position)) return true;
		this.unfoldForwardsWithTrsRules(
				context, position, !guideAtPosition.isVariable());

		return true;
	}

	/**
	 * Implements the unification part of the forward guided-unfolding operation.
	 *
	 * @param context the state shared by this forward-unfolding operation
	 * @param position the prefix currently considered
	 * @return <code>true</code> iff the generated copy completed the proof
	 */
	private boolean addForwardUnifiedCopy(
			ForwardUnfoldingContext context, Position position) {

		ParentTrs parent = context.parameters().isInVerboseMode() ?
				ParentTrsComp.of(this, null, position, false) : null;
		UnfoldedRuleTrsComp copy = this.deepCopy(context.iteration(), parent);
		if (!copy.getRight().get(position).unifyWith(
				copy.second.getLeft().get(position)))
			return false;

		return add(context.parameters(), context.trs(), context.simpleCycles(),
				context.proof(), copy, context.result());
	}

	/**
	 * Implements the TRS-rule part of the forward guided-unfolding operation.
	 *
	 * @param context the state shared by this forward-unfolding operation
	 * @param position the prefix currently considered
	 * @param createGuidedCopy whether a guided copy must be generated after each
	 * direct composed rule
	 */
	private void unfoldForwardsWithTrsRules(
			ForwardUnfoldingContext context, Position position,
			boolean createGuidedCopy) {

		for (RuleTrs rule : context.trs()) {
			if (Thread.currentThread().isInterrupted()) return;
			Collection<UnfoldedRuleTrs> unfoldedRules = this.unfoldForwardsWith(
					context.parameters(), rule, position, context.iteration());
			if (this.addForwardGeneratedRules(
					context, position, unfoldedRules, createGuidedCopy))
				return;
		}
	}

	/**
	 * Adds direct forward unfoldings and their optional guided copies in order.
	 *
	 * @param context the state shared by this forward-unfolding operation
	 * @param position the prefix currently considered
	 * @param unfoldedRules the direct forward unfoldings to process
	 * @param createGuidedCopy whether guided copies have to be generated
	 * @return <code>true</code> iff a processed rule completed the proof
	 */
	private boolean addForwardGeneratedRules(
			ForwardUnfoldingContext context, Position position,
			Collection<UnfoldedRuleTrs> unfoldedRules, boolean createGuidedCopy) {

		for (UnfoldedRuleTrs unfoldedRule : unfoldedRules) {
			if (add(context.parameters(), context.trs(), context.simpleCycles(),
					context.proof(), unfoldedRule, context.result()))
				return true;
			if (createGuidedCopy && unfoldedRule instanceof UnfoldedRuleTrsComp composedRule &&
					this.addForwardGuidedCopy(context, position, composedRule))
				return true;
		}
		return false;
	}

	/**
	 * Builds and adds the guided copy of one forward-unfolded composed rule.
	 *
	 * @param context the state shared by this forward-unfolding operation
	 * @param position the prefix currently considered
	 * @param composedRule the direct composed rule to copy and guide
	 * @return <code>true</code> iff the guided copy completed the proof
	 */
	private boolean addForwardGuidedCopy(
			ForwardUnfoldingContext context, Position position,
			UnfoldedRuleTrsComp composedRule) {

		UnfoldedRuleTrsComp guidedRule = composedRule.deepCopy();
		return guidedRule.second.getLeft().get(position).unifyWith(
				guidedRule.getRight().get(position)) &&
				add(context.parameters(), context.trs(), context.simpleCycles(),
						context.proof(), guidedRule, context.result());
	}

	/**
	 * Applies forward unfolding at strict subpositions of the specified
	 * disagreement position.
	 *
	 * @param context the parameters, TRS, cycle registry, iteration, proof and
	 * result collection shared by this forward-unfolding operation
	 * @param position the disagreement position whose strict subpositions have
	 * to be considered
	 */
	private void unfoldForwardsBelowPosition(
			ForwardUnfoldingContext context, Position position) {

		Term rightAtPosition = this.right.get(position);
		for (Position suffix : rightAtPosition) {
			if (Thread.currentThread().isInterrupted()) return;
			// The disagreement position itself was handled with its prefixes.
			if (!suffix.isEmpty() && !rightAtPosition.get(suffix).isVariable() &&
					this.unfoldForwardsAtSuffix(context, position.append(suffix)))
				return;
		}
	}

	/**
	 * Applies forward unfolding with every TRS rule at one strict subposition.
	 *
	 * @param context the state shared by this forward-unfolding operation
	 * @param position the strict subposition to unfold
	 * @return <code>true</code> iff processing must stop because of interruption
	 * or a completed proof
	 */
	private boolean unfoldForwardsAtSuffix(
			ForwardUnfoldingContext context, Position position) {

		for (RuleTrs rule : context.trs()) {
			if (Thread.currentThread().isInterrupted()) return true;
			Collection<UnfoldedRuleTrs> unfoldedRules = this.unfoldForwardsWith(
					context.parameters(), rule, position, context.iteration());
			for (UnfoldedRuleTrs unfoldedRule : unfoldedRules)
				if (add(context.parameters(), context.trs(), context.simpleCycles(),
						context.proof(), unfoldedRule, context.result()))
					return true;
		}
		return false;
	}

	/**
	 * State shared by the steps of one forward guided-unfolding operation.
	 *
	 * @param parameters parameters controlling unfolding and elimination
	 * @param trs the TRS used for unfolding and elimination
	 * @param simpleCycles the registry of simple cycles already processed
	 * @param iteration the current unfolding iteration
	 * @param proof the proof receiving a nontermination argument, or
	 * <code>null</code> when no proof is being built
	 * @param result the ordered collection receiving generated unfolded rules
	 */
	private record ForwardUnfoldingContext(
			Parameters parameters,
			Trs trs,
			SimpleCycleRegistry simpleCycles,
			int iteration,
			Proof proof,
			LinkedList<UnfoldedRuleTrs> result) {}

	/**
	 * Implements the B_R(s -> t, r, p) operation.
	 *
	 * @param parameters parameters for unfolding
	 * @param p the position of a disagreement pair of t and r
	 * @param trs the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule backwards
	 * @return the resulting unfolded rules
	 */
	private Collection<UnfoldedRuleTrs> unfoldBackwards(
			Parameters parameters, Position p, Trs trs,
			SimpleCycleRegistry simpleCycles, int iteration, Proof proof) {

		// The list to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();
		BackwardUnfoldingContext context = new BackwardUnfoldingContext(
				parameters, trs, simpleCycles, iteration, proof, result);

		// A boolean indicating whether we have to unfold at positions
		// deeper than p i.e., positions that include p as a prefix.
		boolean unfoldInner = false;

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// First, we iterate through the non-empty prefixes of p.
		for (Position q = p; !q.isEmpty(); q = q.properPrefix()) {
			if (currentThread.isInterrupted()) break;

			unfoldInner = this.unfoldBackwardsAtPrefix(context, q) || unfoldInner;
			if (proof != null && proof.isSuccess()) return result;
		}

		// Then, we consider the positions that are greater than p.
		if (!currentThread.isInterrupted() && unfoldInner)
			this.unfoldBackwardsBelowPosition(context, p);

		return result;
	}

	/**
	 * Applies the prefix-oriented parts of the backward guided-unfolding
	 * operation at the specified position.
	 *
	 * @param context the parameters, TRS, cycle registry, iteration, proof and
	 * result collection shared by this backward-unfolding operation
	 * @param position a non-empty prefix of the disagreement position
	 * @return <code>true</code> iff unfolding is enabled at
	 * <code>position</code>, in which case positions below the disagreement
	 * position must also be considered
	 */
	private boolean unfoldBackwardsAtPrefix(
			BackwardUnfoldingContext context, Position position) {

		Term leftAtPosition = this.second.getLeft().get(position);
		if (leftAtPosition.isVariable()) return false;

		Term guideAtPosition = this.right.get(position);
		boolean unfoldAtPosition = context.trs().ascendants(leftAtPosition)
				.contains(guideAtPosition);
		if (!unfoldAtPosition) return false;

		if (this.addBackwardUnifiedCopy(context, position)) return true;
		this.unfoldBackwardsWithTrsRules(
				context, position, !guideAtPosition.isVariable());

		return true;
	}

	/**
	 * Implements the unification part of the backward guided-unfolding operation.
	 *
	 * @param context the state shared by this backward-unfolding operation
	 * @param position the prefix currently considered
	 * @return <code>true</code> iff the generated copy completed the proof
	 */
	private boolean addBackwardUnifiedCopy(
			BackwardUnfoldingContext context, Position position) {

		ParentTrs parent = context.parameters().isInVerboseMode() ?
				ParentTrsComp.of(this, null, position, true) : null;
		UnfoldedRuleTrsComp copy = this.deepCopy(context.iteration(), parent);
		if (!copy.getRight().get(position).unifyWith(
				copy.second.getLeft().get(position)))
			return false;

		return add(context.parameters(), context.trs(), context.simpleCycles(),
				context.proof(), copy, context.result());
	}

	/**
	 * Implements the TRS-rule part of the backward guided-unfolding operation.
	 *
	 * @param context the state shared by this backward-unfolding operation
	 * @param position the prefix currently considered
	 * @param createGuidedCopy whether a guided copy must be generated after each
	 * direct composed rule
	 */
	private void unfoldBackwardsWithTrsRules(
			BackwardUnfoldingContext context, Position position,
			boolean createGuidedCopy) {

		for (RuleTrs rule : context.trs()) {
			if (Thread.currentThread().isInterrupted()) return;
			Collection<UnfoldedRuleTrs> unfoldedRules = this.unfoldBackwardsWith(
					context.parameters(), rule, position, context.iteration());
			if (this.addBackwardGeneratedRules(
					context, position, unfoldedRules, createGuidedCopy))
				return;
		}
	}

	/**
	 * Adds direct backward unfoldings and their optional guided copies in order.
	 *
	 * @param context the state shared by this backward-unfolding operation
	 * @param position the prefix currently considered
	 * @param unfoldedRules the direct backward unfoldings to process
	 * @param createGuidedCopy whether guided copies have to be generated
	 * @return <code>true</code> iff a processed rule completed the proof
	 */
	private boolean addBackwardGeneratedRules(
			BackwardUnfoldingContext context, Position position,
			Collection<UnfoldedRuleTrs> unfoldedRules, boolean createGuidedCopy) {

		for (UnfoldedRuleTrs unfoldedRule : unfoldedRules) {
			if (add(context.parameters(), context.trs(), context.simpleCycles(),
					context.proof(), unfoldedRule, context.result()))
				return true;
			if (createGuidedCopy && unfoldedRule instanceof UnfoldedRuleTrsComp composedRule &&
					this.addBackwardGuidedCopy(context, position, composedRule))
				return true;
		}
		return false;
	}

	/**
	 * Builds and adds the guided copy of one backward-unfolded composed rule.
	 *
	 * @param context the state shared by this backward-unfolding operation
	 * @param position the prefix currently considered
	 * @param composedRule the direct composed rule to copy and guide
	 * @return <code>true</code> iff the guided copy completed the proof
	 */
	private boolean addBackwardGuidedCopy(
			BackwardUnfoldingContext context, Position position,
			UnfoldedRuleTrsComp composedRule) {

		UnfoldedRuleTrsComp guidedRule = composedRule.deepCopy();
		return guidedRule.second.getLeft().get(position).unifyWith(
				guidedRule.getRight().get(position)) &&
				add(context.parameters(), context.trs(), context.simpleCycles(),
						context.proof(), guidedRule, context.result());
	}

	/**
	 * Applies backward unfolding at strict subpositions of the specified
	 * disagreement position.
	 *
	 * @param context the parameters, TRS, cycle registry, iteration, proof and
	 * result collection shared by this backward-unfolding operation
	 * @param position the disagreement position whose strict subpositions have
	 * to be considered
	 */
	private void unfoldBackwardsBelowPosition(
			BackwardUnfoldingContext context, Position position) {

		Term leftAtPosition = this.second.getLeft().get(position);
		for (Position suffix : leftAtPosition) {
			if (Thread.currentThread().isInterrupted()) return;
			// The disagreement position itself was handled with its prefixes.
			if (!suffix.isEmpty() && !leftAtPosition.get(suffix).isVariable() &&
					this.unfoldBackwardsAtSuffix(context, position.append(suffix)))
				return;
		}
	}

	/**
	 * Applies backward unfolding with every TRS rule at one strict subposition.
	 *
	 * @param context the state shared by this backward-unfolding operation
	 * @param position the strict subposition to unfold
	 * @return <code>true</code> iff processing must stop because of interruption
	 * or a completed proof
	 */
	private boolean unfoldBackwardsAtSuffix(
			BackwardUnfoldingContext context, Position position) {

		for (RuleTrs rule : context.trs()) {
			if (Thread.currentThread().isInterrupted()) return true;
			Collection<UnfoldedRuleTrs> unfoldedRules = this.unfoldBackwardsWith(
					context.parameters(), rule, position, context.iteration());
			for (UnfoldedRuleTrs unfoldedRule : unfoldedRules)
				if (add(context.parameters(), context.trs(), context.simpleCycles(),
						context.proof(), unfoldedRule, context.result()))
					return true;
		}
		return false;
	}

	/**
	 * State shared by the steps of one backward guided-unfolding operation.
	 *
	 * @param parameters parameters controlling unfolding and elimination
	 * @param trs the TRS used for unfolding and elimination
	 * @param simpleCycles the registry of simple cycles already processed
	 * @param iteration the current unfolding iteration
	 * @param proof the proof receiving a nontermination argument, or
	 * <code>null</code> when no proof is being built
	 * @param result the ordered collection receiving generated unfolded rules
	 */
	private record BackwardUnfoldingContext(
			Parameters parameters,
			Trs trs,
			SimpleCycleRegistry simpleCycles,
			int iteration,
			Proof proof,
			LinkedList<UnfoldedRuleTrs> result) {}

	/**
	 * Returns a String representation of this triple
	 * relatively to the given set of variable symbols.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this triple: it stops at
	 * variable positions i.e., it does not consider the
	 * parent of a variable position.
	 * <p>
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
		return this.toString(new HashMap<>(), false);
	}
}
