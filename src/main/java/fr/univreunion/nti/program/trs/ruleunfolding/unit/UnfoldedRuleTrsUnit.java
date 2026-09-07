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

package fr.univreunion.nti.program.trs.ruleunfolding.unit;

import java.util.AbstractMap;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An unfolded TRS rule used in the technique based on rule unfolding.
 * It implements a unit triple ie a triple of the form (N,_,_).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class UnfoldedRuleTrsUnit extends UnfoldedRuleTrs {

	/**
	 * An identity-keyed map optimized for the small variable-copy workspaces
	 * created while unfolding unit rules. The first three mappings are stored
	 * inline; larger, unexpected workspaces are promoted to an
	 * {@link IdentityHashMap}.
	 */
	private static final class CopyWorkspace extends AbstractMap<Term, Term> {

		private Term firstKey;
		private Term firstValue;
		private Term secondKey;
		private Term secondValue;
		private Term thirdKey;
		private Term thirdValue;
		private int inlineSize;
		private IdentityHashMap<Term, Term> overflow;

		@Override
		public Term get(Object key) {
			if (this.overflow != null) return this.overflow.get(key);

			for (int i = 0; i < this.inlineSize; i++)
				if (this.keyAt(i) == key) return this.valueAt(i);

			return null;
		}

		@Override
		public boolean containsKey(Object key) {
			if (this.overflow != null) return this.overflow.containsKey(key);

			for (int i = 0; i < this.inlineSize; i++)
				if (this.keyAt(i) == key) return true;

			return false;
		}

		@Override
		public Term put(Term key, Term value) {
			if (this.overflow != null) return this.overflow.put(key, value);

			for (int i = 0; i < this.inlineSize; i++)
				if (this.keyAt(i) == key) {
					Term previousValue = this.valueAt(i);
					this.setValueAt(i, value);
					return previousValue;
				}

			if (this.inlineSize < 3) {
				this.setEntryAt(this.inlineSize++, key, value);
				return null;
			}

			this.promote();
			return this.overflow.put(key, value);
		}

		@Override
		public Term computeIfAbsent(Term key,
				java.util.function.Function<? super Term, ? extends Term>
						mappingFunction) {

			Term value = this.get(key);
			if (value != null) return value;

			Term newValue = mappingFunction.apply(key);
			if (newValue != null) this.put(key, newValue);
			return newValue;
		}

		@Override
		public int size() {
			return this.overflow == null ?
					this.inlineSize : this.overflow.size();
		}

		@Override
		public Set<Entry<Term, Term>> entrySet() {
			if (this.overflow == null) this.promote();
			return this.overflow.entrySet();
		}

		private Term keyAt(int index) {
			return switch (index) {
			case 0 -> this.firstKey;
			case 1 -> this.secondKey;
			case 2 -> this.thirdKey;
			default -> throw new IndexOutOfBoundsException(index);
			};
		}

		private Term valueAt(int index) {
			return switch (index) {
			case 0 -> this.firstValue;
			case 1 -> this.secondValue;
			case 2 -> this.thirdValue;
			default -> throw new IndexOutOfBoundsException(index);
			};
		}

		private void setEntryAt(int index, Term key, Term value) {
			switch (index) {
			case 0 -> {
				this.firstKey = key;
				this.firstValue = value;
			}
			case 1 -> {
				this.secondKey = key;
				this.secondValue = value;
			}
			case 2 -> {
				this.thirdKey = key;
				this.thirdValue = value;
			}
			default -> throw new IndexOutOfBoundsException(index);
			}
		}

		private void setValueAt(int index, Term value) {
			switch (index) {
			case 0 -> this.firstValue = value;
			case 1 -> this.secondValue = value;
			case 2 -> this.thirdValue = value;
			default -> throw new IndexOutOfBoundsException(index);
			}
		}

		private void promote() {
			IdentityHashMap<Term, Term> promoted = new IdentityHashMap<>(4);
			for (int i = 0; i < this.inlineSize; i++)
				promoted.put(this.keyAt(i), this.valueAt(i));

			this.overflow = promoted;
			this.firstKey = this.firstValue = null;
			this.secondKey = this.secondValue = null;
			this.thirdKey = this.thirdValue = null;
			this.inlineSize = 0;
		}
	}

	/**
	 * The component \cL of this triple.
	 */
	private final Set<RuleTrs> simpleCycle = new HashSet<>();

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
	public UnfoldedRuleTrsUnit(Function left, Term right,
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
	public UnfoldedRuleTrsUnit deepCopy() {
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
	public UnfoldedRuleTrsUnit deepCopy(int iteration, ParentTrs parent) {
		CopyWorkspace copies = new CopyWorkspace();

		return new UnfoldedRuleTrsUnit(
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
		return shallowLeftUnifyTest(this);
	}

	/**
	 * Applies the <code>elim</code> operator to this triple.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param trs the TRS used for applying <code>elim</code>
	 * @return the triples resulting from applying <code>elim</code>
	 * to this triple
	 */
	@Override
	public Collection<UnfoldedRuleTrs> elim(
			Parameters parameters, Trs trs, SimpleCycleRegistry simpleCycles) {
		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();

		int m = parameters.getMaxDepth();
		// We only consider the rules that are not deeper than the pruning depth.
		// Using ascendants and descendants is far too costly, hence connectivity.
		if ((m < 0 || this.depth() <= m) &&
				!this.left.embeds(this.right) &&
				this.right.isConnectableTo(this.left, trs))
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
		CopyWorkspace copies = new CopyWorkspace();
		Term right = this.right.unfoldWith(
				rule, p, false, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (right != null) {
			Term left = this.left.deepCopy(copies);

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (parameters.isInVerboseMode() ?
					ParentTrsUnit.of(this, rule, p, false) : null);

			result.add(new UnfoldedRuleTrsUnit(
					(Function) left, right, iteration,
					parent,
					this.simpleCycle));
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

		// We try to unfold the left-hand side of this rule
		// backwards with the provided rule.
		CopyWorkspace copies = new CopyWorkspace();
		Term left = this.left.unfoldWith(
				rule, p, true, parameters.isVariableUnfoldingEnabled(), copies);

		// If success, then we build the resulting rules.
		if (left != null) {
			Term right = this.right.deepCopy(copies);

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (parameters.isInVerboseMode() ?
					ParentTrsUnit.of(this, rule, p, true) : null);

			result.add(new UnfoldedRuleTrsUnit(
					(Function) left, right, iteration,
					parent,
					this.simpleCycle));
		}
		return result;
	}

	/**
	 * Applies the GU_R (guided unfolding) operator to this triple using
	 * the rules of <code>trs</code>.
	 * <p>
	 * Also applies <code>nonTerminationTest</code> to the computed
	 * unfolded triples if <code>proof</code> is not <code>null</code>;
	 * if <code>nonTerminationTest</code> succeeds for an unfolded
	 * triple, then the corresponding proof argument is added to
	 * <code>proof</code>.
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
		// left-hand side and the right-hand side of this rule.
		Collection<Position> disagreementPositions = this.left.dpos(
				this.right, parameters.isVariableUnfoldingEnabled());

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
	 * Applies the enabled guided-unfolding operation at one disagreement
	 * position and appends its results in generation order.
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

		if (this.left.get(position).isVariable() &&
				this.right.get(position).isVariable())
			return addAll(proof,
					this.unfoldForwardsAtVariableDisagreement(
							parameters, position, trs, simpleCycles, iteration, proof),
					result);

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
	 * Implements the F_R(l -> r, s, p) operation for the situation
	 * where the leftmost disagreement pair consists of two variables.
	 * 
	 * @param parameters parameters for unfolding
	 * @param p the position of a disagreement pair of r and s
	 * @param trs the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule forwards
	 * @return the resulting unfolded rules
	 */
	private Collection<UnfoldedRuleTrs> unfoldForwardsAtVariableDisagreement(
			Parameters parameters, Position p, Trs trs,
			SimpleCycleRegistry simpleCycles, int iteration, Proof proof) {

		// The list to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<>();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		for (RuleTrs rule: trs) {
			if (currentThread.isInterrupted()) break;

			Collection<UnfoldedRuleTrs> unfoldedRules =
					this.unfoldForwardsWith(parameters, rule, p, iteration);

			for (UnfoldedRuleTrs unfoldedRule : unfoldedRules)
				if (add(parameters, trs, simpleCycles, proof, unfoldedRule, result))
					return result;
		}

		return result;
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

		boolean unfoldAtPosition = context.trs().descendants(rightAtPosition)
				.contains(this.left.get(position));
		if (!unfoldAtPosition) return false;

		if (this.addForwardUnifiedCopy(context, position)) return true;
		this.unfoldForwardsWithTrsRules(context, position);

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

		CopyWorkspace copies = new CopyWorkspace();
		Function left = (Function) this.left.deepCopy(copies);
		Term right = this.right.deepCopy(copies);
		if (!left.get(position).unifyWith(right.get(position))) return false;

		ParentTrs parent = context.parameters().isInVerboseMode() ?
				ParentTrsUnit.of(this, null, position, false) : null;
		UnfoldedRuleTrs unfoldedRule = new UnfoldedRuleTrsUnit(
				left, right, context.iteration(), parent, this.simpleCycle);
		return add(context.parameters(), context.trs(), context.simpleCycles(),
				context.proof(), unfoldedRule, context.result());
	}

	/**
	 * Implements the TRS-rule part of the forward guided-unfolding operation.
	 *
	 * @param context the state shared by this forward-unfolding operation
	 * @param position the prefix currently considered
	 */
	private void unfoldForwardsWithTrsRules(
			ForwardUnfoldingContext context, Position position) {

		for (RuleTrs rule : context.trs()) {
			if (Thread.currentThread().isInterrupted()) return;
			Collection<UnfoldedRuleTrs> unfoldedRules = this.unfoldForwardsWith(
					context.parameters(), rule, position, context.iteration());
			if (this.addForwardGeneratedRules(context, position, unfoldedRules))
				return;
		}
	}

	/**
	 * Adds direct forward unfoldings and their guided copies in generation order.
	 *
	 * @param context the state shared by this forward-unfolding operation
	 * @param position the prefix currently considered
	 * @param unfoldedRules the direct forward unfoldings to process
	 * @return <code>true</code> iff a processed rule completed the proof
	 */
	private boolean addForwardGeneratedRules(
			ForwardUnfoldingContext context, Position position,
			Collection<UnfoldedRuleTrs> unfoldedRules) {

		for (UnfoldedRuleTrs unfoldedRule : unfoldedRules) {
			if (add(context.parameters(), context.trs(), context.simpleCycles(),
					context.proof(), unfoldedRule, context.result()))
				return true;

			// This guided copy is an extension of F_R from LOPSTR'18.
			UnfoldedRuleTrs guidedRule = unfoldedRule.deepCopy();
			if (guidedRule.getLeft().get(position).unifyWith(
					guidedRule.getRight().get(position)) &&
					add(context.parameters(), context.trs(), context.simpleCycles(),
							context.proof(), guidedRule, context.result()))
				return true;
		}
		return false;
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

		Term leftAtPosition = this.left.get(position);
		if (leftAtPosition.isVariable()) return false;

		boolean unfoldAtPosition = context.trs().ascendants(leftAtPosition)
				.contains(this.right.get(position));
		if (!unfoldAtPosition) return false;

		if (this.addBackwardUnifiedCopy(context, position)) return true;
		this.unfoldBackwardsWithTrsRules(context, position);

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

		CopyWorkspace copies = new CopyWorkspace();
		Function left = (Function) this.left.deepCopy(copies);
		Term right = this.right.deepCopy(copies);
		if (!left.get(position).unifyWith(right.get(position))) return false;

		ParentTrs parent = context.parameters().isInVerboseMode() ?
				ParentTrsUnit.of(this, null, position, true) : null;
		UnfoldedRuleTrs unfoldedRule = new UnfoldedRuleTrsUnit(
				left, right, context.iteration(), parent, this.simpleCycle);
		return add(context.parameters(), context.trs(), context.simpleCycles(),
				context.proof(), unfoldedRule, context.result());
	}

	/**
	 * Implements the TRS-rule part of the backward guided-unfolding operation.
	 *
	 * @param context the state shared by this backward-unfolding operation
	 * @param position the prefix currently considered
	 */
	private void unfoldBackwardsWithTrsRules(
			BackwardUnfoldingContext context, Position position) {

		for (RuleTrs rule : context.trs()) {
			if (Thread.currentThread().isInterrupted()) return;
			Collection<UnfoldedRuleTrs> unfoldedRules = this.unfoldBackwardsWith(
					context.parameters(), rule, position, context.iteration());
			if (this.addBackwardGeneratedRules(context, position, unfoldedRules))
				return;
		}
	}

	/**
	 * Adds direct backward unfoldings and their guided copies in generation order.
	 *
	 * @param context the state shared by this backward-unfolding operation
	 * @param position the prefix currently considered
	 * @param unfoldedRules the direct backward unfoldings to process
	 * @return <code>true</code> iff a processed rule completed the proof
	 */
	private boolean addBackwardGeneratedRules(
			BackwardUnfoldingContext context, Position position,
			Collection<UnfoldedRuleTrs> unfoldedRules) {

		for (UnfoldedRuleTrs unfoldedRule : unfoldedRules) {
			if (add(context.parameters(), context.trs(), context.simpleCycles(),
					context.proof(), unfoldedRule, context.result()))
				return true;

			// This guided copy is an extension of B_R from LOPSTR'18.
			UnfoldedRuleTrs guidedRule = unfoldedRule.deepCopy();
			if (guidedRule.getRight().get(position).unifyWith(
					guidedRule.getLeft().get(position)) &&
					add(context.parameters(), context.trs(), context.simpleCycles(),
							context.proof(), guidedRule, context.result()))
				return true;
		}
		return false;
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

		Term leftAtPosition = this.left.get(position);
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
		return super.toString(variables, shallow) + " [unit]";
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
