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

package fr.univreunion.nti.program.lp;

import java.util.HashMap;
import java.util.LinkedList;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A binary logic program rule, ie a logic program
 * rule whose body contains exactly one atom.
 * 
 * A binary logic program rule results from unfolding
 * an ordinary logic program rule. It is used for proving
 * non-termination of a logic program (it occurs in
 * looping pairs constructed during the proofs).
 * 
 * An object of this class is mutable (because a term
 * is mutable).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class BinaryRuleLp extends UnfoldedRuleLp {

	/**
	 * Constructs a binary logic program rule from the given head,
	 * body atom, iteration and parents.
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
	 * Returns the predicate symbol of the head
	 * of this rule.
	 * 
	 * @return the predicate symbol of the head
	 * of this rule
	 */
	public FunctionSymbol getHeadPredSymbol() {
		return this.head.getRootSymbol();
	}

	/**
	 * Returns the predicate symbol of the body
	 * atom of this rule.
	 * 
	 * @return the predicate symbol of the body
	 * atom of this rule
	 */
	public FunctionSymbol getBodyPredSymbol() {
		return this.body[0].getRootSymbol();
	}

	/**
	 * Checks if the argument of the head of this rule at
	 * the given index is ground.
	 * 
	 * @param i the given argument index
	 * @return <code>true</code> if the argument of the
	 * head of this rule at index <code>i</code> is ground
	 * and <code>false</code> otherwise
	 */
	public boolean isGroundHeadArgument(int i) {
		return this.head.getChild(i).isGround();
	}

	/**
	 * Checks if the body atom of this rule is
	 * <code>tau</code>-more general than the head,
	 * where <code>tau</code> is a given set of positions.
	 * 
	 * @param tau a set of positions
	 * @return <code>true</code> if the body atom is
	 * <code>tau</code>-more general than the head and
	 * <code>false</code> otherwise
	 */
	public boolean isUnitLoop(SoP tau) {
		return Function.tauMoreGeneral(this.body[0], this.head, tau, new Substitution());
	}

	/**
	 * Checks whether this rule is "pluggable" into the given rule
	 * with the given set of positions <code>tau</code>, ie if
	 * the body atom of this rule is <code>tau</code>-more general
	 * than the head of the given rule.
	 * 
	 * @param R the given rule 
	 * @param tau the given set of positions
	 * @return <code>true</code> if this rule is "pluggable"
	 * into <code>R</code> with <code>tau</code> and
	 * <code>false</code> otherwise
	 */
	public boolean canBePluggedInto(BinaryRuleLp R, SoP tau) {
		return Function.tauMoreGeneral(this.body[0], R.head, tau, new Substitution());
	}

	/**
	 * Returns the argument positions of the head of this rule
	 * that violate condition DN1.
	 * 
	 * @return the argument positions of the head of this rule
	 * that violate condition DN1
	 */
	public LinkedList<Integer> violateDN1() {
		LinkedList<Integer> Result = new LinkedList<Integer>();

		Term s_i, s_j;
		int n = this.head.getRootSymbol().getArity();
		for (int i = 0; i < n; i++)
			for (int j = 0; j < n; j++) {
				s_i = this.head.getChild(i);
				s_j = this.head.getChild(j);
				if (j != i && !s_i.isVariableDisjointWith(s_j))
					Result.add(i);
			}

		return Result;
	}

	/**
	 * Let <code>p/n</code> be the predicate symbol of the head
	 * of this rule. This method returns an array of size
	 * <code>n</code> which is such that: for each integer <code>i</code>
	 * in <code>[0,n-1]</code>, the cell at index <code>i</code>
	 * contains a value that <code>tau(p)(i)</code> should have
	 * to satisfy DN2 (where <code>tau</code> is the given set
	 * of positions).
	 * 
	 * @param tau the given set of positions
	 * @return an array representing the value that
	 * <code>tau(p)</code> should have in order to satisfy
	 * DN2
	 */
	public Term[] violateDN2(SoP tau) {
		FunctionSymbol p = this.head.getRootSymbol();
		Term[] DN2 = new Term[p.getArity()];

		Term tau_i, s_i;
		for (int i = 0; i < DN2.length; i++) {
			tau_i = tau.get(p, i);
			if (tau_i != null) {
				s_i = this.head.getChild(i);
				if (s_i.isMoreGeneralThan(tau_i))
					DN2[i] = tau_i;
				else if (tau_i.isMoreGeneralThan(s_i))
					DN2[i] = s_i;
				else
					DN2[i] = null;
			}
			else
				DN2[i] = null;
		}

		return DN2;
	}

	/**
	 * Returns the argument positions of the body of this rule
	 * that violate condition DN3 relatively to the given set
	 * of positions.
	 * 
	 * @param tau the given set of positions
	 * @return the argument positions of the body of this rule
	 * that violate condition DN3
	 */
	public LinkedList<Integer> violateDN3(SoP tau) {
		LinkedList<Integer> Result = new LinkedList<Integer>();

		Term tau_j, t_j;
		FunctionSymbol q = this.body[0].getRootSymbol();
		int m = q.getArity();
		for (int j = 0; j < m; j++) {
			tau_j = tau.get(q, j);
			t_j = this.body[0].getChild(j);
			if (tau_j != null &&
					!tau_j.isMoreGeneralThan(t_j))
				Result.add(j);
		}

		return Result;
	}

	/**
	 * Returns the argument positions of the head of this rule
	 * that violate condition DN4 relatively to the given set
	 * of positions.
	 * 
	 * @param tau the given set of positions
	 * @return the argument positions of the head of this rule
	 * that violate condition DN4
	 */
	public LinkedList<Integer> violateDN4(SoP tau) {
		LinkedList<Integer> Result = new LinkedList<Integer>();

		Term s_i, t_j;

		FunctionSymbol p = this.head.getRootSymbol();
		FunctionSymbol q = this.body[0].getRootSymbol();
		int n = p.getArity();
		int m = q.getArity();
		for (int i = 0; i < n; i++)
			if (tau.inDomain(p, i)) {
				s_i = this.head.getChild(i);
				for (int j = 0; j < m; j++)
					if (!tau.inDomain(q, j)) {
						t_j = this.body[0].getChild(j);
						if (!s_i.isVariableDisjointWith(t_j))
							Result.add(i);
					}
			}

		return Result;
	}

	/**
	 * Returns a simple String representation of this binary rule.
	 *
	 * @return a simple String representation of this binary rule
	 */
	public String toSimpleString() {
		// A set of pairs (V,s) where s is
		// the symbol associated to variable V.
		HashMap<Variable,String> variables = new HashMap<Variable,String>();

		return this.head.toString(variables, false) +
				" :- " +
				this.body[0].toString(variables, false); 
	}
}
