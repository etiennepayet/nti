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

package fr.univreunion.nti.program.trs.loop.trans;

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
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.loop.comp.UnfoldedRuleTrsLoopComp;
import fr.univreunion.nti.program.trs.loop.unit.UnfoldedRuleTrsLoopUnit;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An implementation of class <code>UnfoldedRuleTRS</code> used
 * in the technique based on dependency pairs (JAR version).
 * It implements a transitory triple ie a triple of the form (N,\cN,\cL).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class UnfoldedRuleTrsLoopTrans extends UnfoldedRuleTrs {

	/**
	 * The component \cN of this triple.
	 */
	private final Deque<RuleTrs> scc = new LinkedList<RuleTrs>();

	/**
	 * The component \cL of this triple.
	 */
	private final Set<RuleTrs> simpleCycle = new HashSet<RuleTrs>();

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
	 * @param path the path in the program being unfolded that
	 * corresponds to the transitory triple
	 * @param scc the component \cN of the transitory triple
	 * @param simpleCycle the component \cL of the transitory triple
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 * @return the triples resulting from unfolding the transitory
	 * triple
	 */
	public synchronized static Collection<UnfoldedRuleTrs> getUnfoldedInstances(
			Function left, Term right, int iteration,
			ParentTrs parent, Path path,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		UnfoldedRuleTrsLoopTrans R = new UnfoldedRuleTrsLoopTrans(
				left, right, iteration, parent, path, scc, simpleCycle);

		Collection<UnfoldedRuleTrs> Result = new LinkedList<UnfoldedRuleTrs>();
		Result.add(R);
		return Result;
	}

	/**
	 * Builds a transitory triple from the specified parameters.
	 * 
	 * @param left the left-hand side of the unique rule of this triple
	 * @param right the right-hand side of the unique rule of this triple
	 * @param iteration the iteration of the unfolding operator
	 * at which this triple is generated
	 * @param parent the parent of this triple
	 * @param path the path in the program being unfolded that
	 * corresponds to this triple
	 * @param scc the component \cN of this triple
	 * @param simpleCycle the component \cL of this triple
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	private UnfoldedRuleTrsLoopTrans(Function left, Term right,
			int iteration, ParentTrs parent, Path path,
			Collection<RuleTrs> scc, Collection<RuleTrs> simpleCycle) {

		super(left, right, iteration, parent, path);

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
	public UnfoldedRuleTrsLoopTrans deepCopy() {
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
	public UnfoldedRuleTrsLoopTrans deepCopy(int iteration, ParentTrs parent) {
		HashMap<Term, Term> copies = new HashMap<Term, Term>();

		return new UnfoldedRuleTrsLoopTrans(
				(Function) this.left.deepCopy(copies),
				this.right.deepCopy(copies),
				iteration,
				parent,
				this.path,
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
	public Collection<UnfoldedRuleTrsLoopTrans> elim(Parameters parameters, Trs IR) {
		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrsLoopTrans> Result = new LinkedList<UnfoldedRuleTrsLoopTrans>();

		int m = parameters.getMaxDepth();
		if (m < 0 || this.depth() <= m)
			// We only consider the rules that are not deeper than the pruning depth.
			if (!this.scc.isEmpty() ||
					(!this.left.embeds(this.right) &&
							this.right.isConnectableTo(this.left, IR) &&
							!IR.containsSimpleCycle(this.simpleCycle)))
				Result.add(this);

		return Result;
	}

	/**
	 * Unsupported operation, as such a rule does
	 * not need to be unfolded forwards.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Collection<UnfoldedRuleTrsLoopTrans> unfoldForwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation, as such a rule does
	 * not need to be unfolded backwards.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Collection<UnfoldedRuleTrsLoopTrans> unfoldBackwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		throw new UnsupportedOperationException();
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

		int n = this.scc.size();
		for (int i = 0; !currentThread.isInterrupted() && i < n; i++) {
			RuleTrs R = this.scc.removeFirst();
			this.simpleCycle.add(R);
			//
			ParentTrs parent = ParentTrsLoopTrans.getInstance(this, R, null, false);
			HashMap<Term,Term> copies = new HashMap<Term,Term>();
			Collection<UnfoldedRuleTrs> unfoldedRules =
					UnfoldedRuleTrsLoopComp.getInstances(
							(Function) this.left.deepCopy(copies),
							this.right.deepCopy(copies),
							iteration,
							parent,
							this.path,
							R.deepCopy(),
							new Path(R),
							this.scc,
							this.simpleCycle);
			for (UnfoldedRuleTrs U : unfoldedRules)
				if (add(parameters, IR, proof, U, Result))
					return Result;
			//
			this.simpleCycle.remove(R);
			this.scc.addLast(R);
		}

		if (!currentThread.isInterrupted() && !IR.containsSimpleCycle(this.simpleCycle)) {
			ParentTrs parent = ParentTrsLoopTrans.getInstance(this, null, null, false);
			HashMap<Term,Term> copies = new HashMap<Term,Term>();
			UnfoldedRuleTrs unfoldedRule = new UnfoldedRuleTrsLoopUnit(
					(Function) this.left.deepCopy(copies),
					this.right.deepCopy(copies),
					iteration,
					parent,
					this.path,
					this.simpleCycle);

			n = Result.size();
			if (add(parameters, IR, proof, unfoldedRule, Result))
				return Result;
			// If Result has changed, then unfoldedRule has been added to it
			// ie unfoldedRule is well-formed. Hence, we can safely add
			// this.simpleCycle (ie \cL) to the result.
			if (n < Result.size()) IR.addSimpleCycle(this.simpleCycle);
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
		return super.toString(variables, shallow) + " [trans]";
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
