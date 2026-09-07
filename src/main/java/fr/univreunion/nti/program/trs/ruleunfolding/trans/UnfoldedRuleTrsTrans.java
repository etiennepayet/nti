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

package fr.univreunion.nti.program.trs.ruleunfolding.trans;

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
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
import fr.univreunion.nti.program.trs.ruleunfolding.comp.UnfoldedRuleTrsComp;
import fr.univreunion.nti.program.trs.ruleunfolding.unit.UnfoldedRuleTrsUnit;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An unfolded TRS rule used in the technique based on rule unfolding.
 * It implements a transitory triple ie a triple of the form (N,\cN,\cL).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class UnfoldedRuleTrsTrans extends UnfoldedRuleTrs {

	/**
	 * The component \cN of this triple.
	 */
	private final Deque<RuleTrs> scc = new LinkedList<>();

	/**
	 * The component \cL of this triple.
	 */
	private final Set<RuleTrs> simpleCycle = new HashSet<>();

	/**
	 * Builds a transitory triple from the specified parameters
	 * and applies the GU_R (guided unfolding) operator to it.
	 * 
	 * @param left the left-hand side of the first rule of the
	 * transitory triple
	 * @param right the right-hand side of the first rule of the
	 * transitory triple
	 * @param iteration the iteration of the unfolding operator
	 * at which the transitory triple is generated
	 * @param parent the parent of the transitory triple
	 * @param scc the component \cN of the transitory triple
	 * @param simpleCycle the component \cL of the transitory triple
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 * @return the triples resulting from unfolding the transitory
	 * triple
	 */
	public static synchronized Collection<UnfoldedRuleTrs> getUnfoldedInstances(
			Function left, Term right, int iteration, ParentTrs parent,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		UnfoldedRuleTrsTrans rule = new UnfoldedRuleTrsTrans(
				left, right, iteration, parent, scc, simpleCycle);

		Collection<UnfoldedRuleTrs> result = new LinkedList<>();
		result.add(rule);
		return result;
	}

	/**
	 * Builds a transitory triple from the specified parameters.
	 * 
	 * @param left the left-hand side of the unique rule of this triple
	 * @param right the right-hand side of the unique rule of this triple
	 * @param iteration the iteration of the unfolding operator
	 * at which this triple is generated
	 * @param parent the parent of this triple
	 * @param scc the component \cN of this triple
	 * @param simpleCycle the component \cL of this triple
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	private UnfoldedRuleTrsTrans(
			Function left, Term right, int iteration, ParentTrs parent,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		super(left, right, iteration, parent);

		this.scc.addAll(scc);
		this.simpleCycle.addAll(simpleCycle);
	}

	/**
	 * Returns a deep copy of this rule i.e., a copy
	 * where each subterm is also copied.
	 * 
	 * @return a deep copy of this rule
	 */
	@Override
	public UnfoldedRuleTrsTrans deepCopy() {
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
	public UnfoldedRuleTrsTrans deepCopy(int iteration, ParentTrs parent) {
		HashMap<Term, Term> copies = new HashMap<>();

		return new UnfoldedRuleTrsTrans(
				(Function) this.left.deepCopy(copies),
				this.right.deepCopy(copies),
				iteration,
				parent,
				this.scc,
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
		if ((m < 0 || this.depth() <= m) &&
				(!this.scc.isEmpty() ||
						(!this.left.embeds(this.right) &&
								this.right.isConnectableTo(this.left, trs) &&
								!simpleCycles.contains(this.simpleCycle))))
			result.add(this);

		return result;
	}

	/**
	 * Unsupported operation, as such a rule does
	 * not need to be unfolded forwards.
     */
	@Override
	public Collection<UnfoldedRuleTrs> unfoldForwardsWith(
			Parameters parameters, RuleTrs rule, Position p, int iteration) {

		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation, as such a rule does
	 * not need to be unfolded backwards.
	 */
	@Override
	public Collection<UnfoldedRuleTrs> unfoldBackwardsWith(
			Parameters parameters, RuleTrs rule, Position p, int iteration) {

		throw new UnsupportedOperationException();
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

		UnfoldingContext context = new UnfoldingContext(
				parameters, trs, simpleCycles, iteration, proof,
				new LinkedList<>());

		int n = this.scc.size();
		for (int i = 0; !Thread.currentThread().isInterrupted() && i < n; i++) {
			RuleTrs rule = this.scc.removeFirst();
			this.simpleCycle.add(rule);
			if (this.unfoldWith(context, rule))
				return context.result();

			this.simpleCycle.remove(rule);
			this.scc.addLast(rule);
		}

		if (!Thread.currentThread().isInterrupted() &&
				!simpleCycles.contains(this.simpleCycle))
			this.convertToUnit(context);

		return context.result();
	}

	/**
	 * Builds the composed triples obtained by combining this transitory triple
	 * with the specified SCC rule.
	 *
	 * @param context the state shared by this unfolding operation
	 * @param rule the current rule removed from the head of the SCC
	 * @return <code>true</code> iff a generated triple completed the proof
	 */
	private boolean unfoldWith(UnfoldingContext context, RuleTrs rule) {
		ParentTrs parent = context.parameters().isInVerboseMode() ?
				ParentTrsTrans.of(this, rule, null, false) : null;
		HashMap<Term, Term> copies = new HashMap<>();

		// First, we build a composed triple with [this, rule].
		Collection<UnfoldedRuleTrs> unfoldedRules =
				UnfoldedRuleTrsComp.getInstances(
						(Function) this.left.deepCopy(copies),
						this.right.deepCopy(copies), context.iteration(), parent,
						rule.deepCopy(), this.scc, this.simpleCycle);
		if (addAll(context, unfoldedRules))
			return true;

		// With strategy ALL, we also build a composed triple with [rule, this].
		if (context.parameters().getStrategy() == StrategyLoop.ALL) {
			copies.clear();
			unfoldedRules = UnfoldedRuleTrsComp.getInstances(
					(Function) rule.getLeft().deepCopy(copies),
					rule.getRight().deepCopy(copies), context.iteration(), parent,
					this.deepCopy(), this.scc, this.simpleCycle);
			return addAll(context, unfoldedRules);
		}

		return false;
	}

	/**
	 * Eliminates and appends the specified generated rules in their collection
	 * order, stopping as soon as one of them completes the proof.
	 *
	 * @param context the state shared by this unfolding operation
	 * @param unfoldedRules the generated rules to eliminate and append
	 * @return <code>true</code> iff a generated rule completed the proof
	 */
	private static boolean addAll(
			UnfoldingContext context, Collection<UnfoldedRuleTrs> unfoldedRules) {

		for (UnfoldedRuleTrs unfoldedRule : unfoldedRules)
			if (add(context.parameters(), context.trs(), context.simpleCycles(),
					context.proof(), unfoldedRule, context.result()))
				return true;

		return false;
	}

	/**
	 * Converts this exhausted transitory triple into a unit rule and registers
	 * its simple cycle when elimination retains that rule.
	 *
	 * @param context the state shared by this unfolding operation
	 */
	private void convertToUnit(UnfoldingContext context) {
		ParentTrs parent = context.parameters().isInVerboseMode() ?
				ParentTrsTrans.of(this, null, null, false) : null;
		HashMap<Term, Term> copies = new HashMap<>();
		UnfoldedRuleTrs unfoldedRule = new UnfoldedRuleTrsUnit(
				(Function) this.left.deepCopy(copies),
				this.right.deepCopy(copies), context.iteration(), parent,
				this.simpleCycle);

		int previousSize = context.result().size();
		if (add(context.parameters(), context.trs(), context.simpleCycles(),
				context.proof(), unfoldedRule, context.result()))
			return;
		// If the result has changed, unfoldedRule is well-formed. Hence, its
		// simple cycle can safely be registered.
		if (previousSize < context.result().size())
			context.simpleCycles().add(this.simpleCycle);
	}

	/**
	 * State shared by the steps of one transitory-rule unfolding operation.
	 *
	 * @param parameters parameters for unfolding and elimination
	 * @param trs the TRS used for unfolding and elimination
	 * @param simpleCycles the registry of already retained simple cycles
	 * @param iteration the current unfolding iteration
	 * @param proof the proof to build, or <code>null</code> when no proof is requested
	 * @param result the ordered collection receiving retained generated rules
	 */
	private record UnfoldingContext(
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
		return super.toString(variables, shallow) + " [trans]";
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
