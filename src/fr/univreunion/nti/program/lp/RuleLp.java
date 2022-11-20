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

package fr.univreunion.nti.program.lp;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;

import fr.univreunion.nti.program.Path;
import fr.univreunion.nti.program.Rule;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A logic program rule.
 * 
 * An object of this class is mutable
 * (because a term is mutable).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RuleLp extends Rule {

	/**
	 * The head of the rule.
	 */
	protected final Function head;

	/**
	 * The body of the rule.
	 */
	protected final Function[] body;

	/**
	 * Constructs a logic program rule from the given head,
	 * body and appearance number in the analyzed file.
	 * 
	 * Called by the parser when reading the analyzed file.
	 * 
	 * @param head the head of the rule
	 * @param body the body of the rule
	 * @param numberInFile the appearance number of the rule
	 * in the analyzed file
	 * @throws IllegalArgumentException if the given head
	 * is <code>null</code> or if the given body or
	 * a given body atom is <code>null</code>
	 */
	public RuleLp(Function head, Function[] body, Integer numberInFile) {
		super(numberInFile);
		
		if (head == null)
			throw new IllegalArgumentException(
					"construction of an LP rule with a null head");
		if (body == null)
			throw new IllegalArgumentException(
					"construction of an LP rule with a null body");

		this.head = head;

		this.body = new Function[body.length];
		int index = 0;
		for (Function A: body)
			if (A != null)
				this.body[index++] = A;
			else
				throw new IllegalArgumentException(
						"construction of an LP rule with a null body atom");		
	}
	
	/**
	 * Constructs a logic program rule from the given head
	 * and body. The appearance number of the rule is set
	 * to <code>null</code>.
	 * 
	 * @param head the head of the rule 
	 * @param body the body of the rule 
	 * @throws IllegalArgumentException if the given head
	 * is <code>null</code> or if the given body or
	 * a given body atom is <code>null</code>
	 */
	public RuleLp(Function head, Function[] body) {
		this(head, body, null);
	}

	/**
	 * Constructs a logic program fact from the given head.
	 * The appearance number of the fact is set to
	 * <code>null</code>.
	 * 
	 * @param head the head of the fact
	 * @throws IllegalArgumentException if the given
	 * head is <code>null</code>
	 */
	public RuleLp(Function head) {
		this(head, new Function[0], null);
	}

	/**
	 * Returns the head of this rule.
	 * 
	 * @return the head of this rule
	 */
	public Function getHead() {
		return this.head;
	}

	/**
	 * Returns the atom at the given position
	 * in the body of this rule.
	 * 
	 * @param i a position in the body of this
	 * rule
	 * @return the atom at the given position
	 * in the body of this rule
	 */
	public Function getBody(int i) {
		return this.body[i];
	}

	/**
	 * Unfolds this rule once using the given collection of rules.
	 * 
	 * @param X a collection of rules for unfolding this rule
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 * @throws IllegalArgumentException if the given iteration
	 * is negative or zero
	 */
	public Collection<UnfoldedRuleLp> unfold(Collection<UnfoldedRuleLp> X, int iteration) {

		if (iteration <= 0)
			throw new IllegalArgumentException(
					"unfolding a rule with a negative iteration");

		LinkedList<UnfoldedRuleLp> Result = new LinkedList<UnfoldedRuleLp>();

		if (this.body.length == 0) {
			// Here, this rule is a fact. We add it to the
			// result only if we are at iteration 1.
			if (iteration == 1) 
				Result.add(UnfoldedRuleLp.getInstance(this.head, 1, new Path(this)));
		}
		else {
			// Here, this rule has a non-empty body.

			// Below, we implement the slight modification of T^{\beta}_P
			// that we have introduced in JAR'21. Generated binary rules
			// are associated with their iteration number. We generate
			// a new rule in Result only when we have used a rule of
			// the immediately preceding iteration (see condition
			// n \in {n_1,...,n_i} in JAR'21). Hence the instructions
			// 'if (R.getIteration() == iteration - 1)...' and
			// 'if (max == iteration - 1)...' below before adding
			// something to Result.

			LinkedList<UnfoldedRuleLp> temp = new LinkedList<UnfoldedRuleLp>();
			temp.add(UnfoldedRuleLp.getInstance(this.head, this.body, 0, new Path(this)));

			int lastIndex = this.body.length - 1;
			for (int i = 0; i <= lastIndex; i++) {
				LinkedList<UnfoldedRuleLp> unfoldedWithFacts = temp;
				temp = new LinkedList<UnfoldedRuleLp>();

				for (UnfoldedRuleLp R : unfoldedWithFacts) {
					// First, unfold R with id but only if the
					// resulting rule belongs to the current iteration.
					if (R.getIteration() == iteration - 1) {
						HashMap<Term,Term> copies = new HashMap<Term,Term>();
						Function H = (Function) R.head.deepCopy(copies);
						Function[] B = { (Function) R.body[i].deepCopy(copies) };
						Result.add(UnfoldedRuleLp.getInstance(H, B, iteration, R.getPath()));
					}
					// Then, unfold R with the rules of X.
					for (UnfoldedRuleLp R_X : X) {
						int max = Math.max(R.getIteration(), R_X.getIteration());
						UnfoldedRuleLp Rcopy = R.deepCopy();
						UnfoldedRuleLp R_Xcopy = R_X.deepCopy();

						if (Rcopy.body[i].unifyWith(R_Xcopy.head)) {
							Path path = new Path();
							path.addAll(R.getPath());
							path.addAll(R_X.getPath());
							if (R_X.body.length == 0) {
								// R_X is a fact:
								if (i < lastIndex)
									// i is not the last index: the i-th atom in the body
									// of R cannot be unfolded with a fact
									temp.addLast(UnfoldedRuleLp.getInstance(
											Rcopy.head, Rcopy.body, max, path));
								else {
									// the last atom in the body of R can be
									// unfolded with a fact; this results
									// in a new fact
									if (max == iteration - 1)
										Result.add(UnfoldedRuleLp.getInstance(
												Rcopy.head, iteration, path));
								}
							}
							else {
								// R_X is not a fact:
								if (max == iteration - 1) {
									Function[] B = { R_Xcopy.body[0] };
									Result.add(UnfoldedRuleLp.getInstance(
											Rcopy.head, B, iteration, path));
								}
							}
						}
					}
				}
			}
		}

		return Result;
	}

	/**
	 * Returns a String representation of this rule.
	 *
	 * @return a String representation of this rule
	 */
	public String toString() {
		// A set of pairs (V,s) where s is
		// the symbol associated to variable V.
		HashMap<Variable,String> variables = new HashMap<Variable,String>();

		StringBuffer s = new StringBuffer(this.head.toString(variables, false));

		if (this.body.length > 0) {
			s.append(" :- ");
			int k = this.body.length - 1;
			for (Term A: this.body) {
				s.append(A.toString(variables, false));
				if (k-- > 0)
					s.append(", ");
			}
		}
		s.append(".");

		return s.toString();
	}
}
