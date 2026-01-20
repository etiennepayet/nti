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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.program.lp.nonloop.PatternRuleLp;
import fr.univreunion.nti.program.lp.nonloop.PatternRuleLpInProgress;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.PatternTerm;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A logic program rule.
 * 
 * An object of this class is mutable
 * (because a term is mutable).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RuleLp {

	/**
	 * The head of the rule.
	 */
	protected final Function head;

	/**
	 * The body of the rule.
	 */
	protected final Function[] body;

	/**
	 * Constructs a logic program rule from the given
	 * head and body.
	 * 
	 * Called by the parser when reading the analyzed file.
	 * 
	 * @param head the head of the rule
	 * @param body the body of the rule
	 * @throws IllegalArgumentException if the given head
	 * is <code>null</code> or if the given body or
	 * a given body atom is <code>null</code>
	 */
	public RuleLp(Function head, Function[] body) {

		if (head == null)
			throw new IllegalArgumentException(
					"construction of an LP rule with a null head");
		if (body == null)
			throw new IllegalArgumentException(
					"construction of an LP rule with a null body");

		this.head = head;

		this.body = new Function[body.length];
		int index = 0;
		for (Function a: body)
			if (a != null)
				this.body[index++] = a;
			else
				throw new IllegalArgumentException(
						"construction of an LP rule with a null body atom");		
	}

	/**
	 * Constructs a logic program fact from the
	 * given head.
	 * 
	 * @param head the head of the fact
	 * @throws IllegalArgumentException if the given
	 * head is <code>null</code>
	 */
	public RuleLp(Function head) {
		this(head, new Function[0]);
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
	 * Returns the number of atoms in
	 * body of this rule.
	 * 
	 * @return the number of atoms in
	 * body of this rule
	 */
	public int getBodyLength() {
		return this.body.length;
	}

	/**
	 * Checks whether this rule is a fact,
	 * i.e., its body is empty.
	 * 
	 * @return <code>true</code> iff this
	 * rule is a fact
	 */
	public boolean isFact() {
		return this.body.length == 0;
	}

	/**
	 * Checks whether this rule is binary,
	 * i.e., its body contains exactly one
	 * atom.
	 * 
	 * @return <code>true</code> iff this
	 * rule is binary
	 */
	public boolean isBinary() {
		return this.body.length == 1;
	}


	/**
	 * Unfolds this rule once using the given collection of rules.
	 * 
	 * Applies the T^{\beta}_P operator of [Codish&Taboch, 99]
	 * to this rule.
	 * 
	 * @param x a collection of rules for unfolding this rule
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 * @throws IllegalArgumentException if the given iteration
	 * is negative or zero
	 */
	public Collection<UnfoldedRuleLp> unfold(Collection<UnfoldedRuleLp> x, int iteration) {

		if (iteration <= 0)
			throw new IllegalArgumentException(
					"unfolding a rule with a negative iteration");

		// The thread running this unfolding.
		Thread currentThread = Thread.currentThread();

		LinkedList<UnfoldedRuleLp> result = new LinkedList<>();

		if (this.body.length == 0) {
			// Here, this rule is a fact. We add it to the
			// result only if we are at iteration 1.
			if (iteration == 1) 
				result.add(UnfoldedRuleLp.getInstance(this.head, 1));
		}
		else {
			// Here, this rule has a non-empty body.

			// Below, we implement a slight modification of T^{\beta}_P.
			// Generated binary rules are associated with their iteration
			// number. We generate a new rule in 'result' only when we
			// have used a rule of the immediately preceding iteration.
			// Hence the instructions
			// 'if (r.getIteration() == iteration - 1)...' and
			// 'if (max == iteration - 1)...'
			// below before adding something to result.

			LinkedList<UnfoldedRuleLp> temp = new LinkedList<>();
			temp.add(UnfoldedRuleLp.getInstance(this.head, this.body, 0));

			int lastIndex = this.body.length - 1;
			for (int i = 0; i <= lastIndex; i++) {
				if (currentThread.isInterrupted()) break;

				LinkedList<UnfoldedRuleLp> unfoldedWithFacts = temp;
				temp = new LinkedList<>();

				// Suppose that this rule has the form h <- b_1,...,b_n.
				// The invariant of this for loop is: at that point,
				// b_1,...,b_{i-1} have been unfolded with facts and
				// the list 'unfoldedWithFacts' contains all the
				// corresponding instantiations of this rule. Therefore,
				// all elements of 'unfoldedWithFacts' have the form 
				// h' <- b'_1,...,b'_n where
				// (h',b'_1,...,b'_n) = (h,b_1,...,b_n)\theta for a
				// substitution \theta which is the mgu computed so far.

				for (UnfoldedRuleLp r : unfoldedWithFacts) {
					if (currentThread.isInterrupted()) break;

					// First, unfold r with id but only if the
					// resulting rule belongs to the current iteration.
					if (r.getIteration() == iteration - 1) {
						HashMap<Term,Term> copies = new HashMap<>();
						Function h = (Function) r.head.deepCopy(copies);
						Function[] b = { (Function) r.body[i].deepCopy(copies) };
						result.add(UnfoldedRuleLp.getInstance(h, b, iteration));
					}
					// Then, unfold r with the rules of x.
					for (UnfoldedRuleLp r_x : x) {
						if (currentThread.isInterrupted()) break;

						int max = Math.max(r.getIteration(), r_x.getIteration());
						UnfoldedRuleLp rCopy = r.deepCopy();
						UnfoldedRuleLp r_xCopy = r_x.deepCopy();

						if (rCopy.body[i].unifyWith(r_xCopy.head)) {
							if (r_x.body.length == 0) { // r_x is a fact:
								if (i < lastIndex)
									// i is not the last index: the i-th atom in the body
									// of r cannot be unfolded with a fact.
									temp.addLast(UnfoldedRuleLp.getInstance(
											rCopy.head, rCopy.body, max));
								else if (max == iteration - 1)
									// The last atom in the body of r can be
									// unfolded with a fact. This results
									// in a new fact.
									result.add(UnfoldedRuleLp.getInstance(
											rCopy.head, iteration));
							}
							else if (max == iteration - 1) {
								Function[] B = { r_xCopy.body[0] };
								result.add(UnfoldedRuleLp.getInstance(
										rCopy.head, B, iteration));
							}
						}
					}
				}
			}
		}

		return result;
	}

	/**
	 * Unfolds this rule once using the given collections of rules.
	 * 
	 * Applies the T^{\pi}_{P,B} operator of [Payet, LOPSTR'25]
	 * to this rule.
	 * 
	 * It is supposed that the provided collections consist of
	 * pattern rules (p,q) where both p and q are simple pattern
	 * terms (see Def. 9 of [Payet, LOPSTR'25]).
	 * 
	 * @param x a collection of rules for unfolding this rule
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 * @throws IllegalArgumentException if the given iteration
	 * is negative or zero
	 */
	public Collection<PatternRuleLp> unfoldPattern(Collection<PatternRuleLp> x, int iteration) {

		if (iteration <= 0)
			throw new IllegalArgumentException(
					"unfolding a rule with a negative iteration");

		// The thread running this unfolding.
		Thread currentThread = Thread.currentThread();

		LinkedList<PatternRuleLp> result = new LinkedList<>();

		// Below, we implement a slight modification of T^{\pi}_{P,B}.
		// Generated pattern rules are associated with their iteration
		// number. We generate a new rule in 'result' only when we
		// have used a rule of the immediately preceding iteration.
		// Hence the instructions
		// 'if (r.getIteration() == iteration - 1)...' and
		// 'if (max == iteration - 1)...'
		// below before adding something to result.

		LinkedList<PatternRuleLpInProgress> temp = new LinkedList<>();
		temp.add(new PatternRuleLpInProgress(0));

		int lastIndex = this.body.length - 1;
		for (int i = 0; i <= lastIndex; i++) {
			if (currentThread.isInterrupted()) break;

			LinkedList<PatternRuleLpInProgress> unfoldedWithFacts = temp;
			temp = new LinkedList<>();

			// Suppose that this rule has the form h <- b_1,...,b_n.
			// The invariant of this for loop is: at that point,
			// b_1,...,b_{i-1} have been unfolded with facts and
			// the list 'unfoldedWithFacts' contains all the
			// corresponding mgu's.

			for (PatternRuleLpInProgress r : unfoldedWithFacts) {
				if (currentThread.isInterrupted()) break;

				PatternSubstitution theta = r.getPatternSubs();
				if (theta != null) {
					// First, unfold this rule with id but only if the
					// resulting rule belongs to the current iteration.
					if (r.getIteration() == iteration - 1) {
						HashMap<Term,Term> copies = new HashMap<>();
						Function h = (Function) this.head.deepCopy(copies);
						Function b = (Function) this.body[i].deepCopy(copies);
						theta = theta.deepCopy(copies);
						result.add(PatternRuleLp.getInstance(
								h, theta, b, theta, iteration));
					}
					// Then, unfold this rule with the rules of 'x'.
					for (PatternRuleLp r_x : x) {
						if (currentThread.isInterrupted()) break;

						result.addAll(this.unfoldPatternAtIndex(i, r_x.deepCopy(), r, temp, lastIndex, iteration));
					}
				}
			}
		}

		return result;
	}

	/**
	 * Unfolds the atom at index <code>i</code> in the body of
	 * this rule using the pattern rule <code>r_unfold</code>.
	 * 
	 * @param i the index of the current atom to consider in
	 * the body of this rule
	 * @param r_unfold the rule that we have to use to unfold
	 * @param r the mgu computed so far during the unfolding
	 * @param temp a collection of mgus computed so far
	 * @param lastIndex the index of the last atom in the
	 * body of this rule
	 * @param iteration the current iteration of the unfolding
	 * operator
	 * @return a collection of unfolded rules
	 */
	private Collection<PatternRuleLp> unfoldPatternAtIndex(int i,
			PatternRuleLp r_unfold,
			PatternRuleLpInProgress r,
			LinkedList<PatternRuleLpInProgress> temp,
			int lastIndex, int iteration) {

		// The thread running this unfolding.
		Thread currentThread = Thread.currentThread();

		// The collection to return at the end.
		LinkedList<PatternRuleLp> result = new LinkedList<>();

		int max = Math.max(r.getIteration(), r_unfold.getIteration());

		// The current atom in the body of this rule.
		PatternSubstitution r_patsub = r.getPatternSubs();
		PatternTerm body_i = SimplePatternTerm.getInstance(this.body[i], r_patsub);

		// We unify the current atom in the body of
		// this rule with the left-hand side of the
		// rule used to unfold.
		Collection<? extends PatternSubstitution> mgus = body_i.unifyWith(r_unfold);

		if (!mgus.isEmpty())
			for (PatternSubstitution mgu : mgus) {
				if (currentThread.isInterrupted()) break;

				mgu = r_patsub.composeWith(mgu);
				if (r_unfold.isFact()) {
					if (i < lastIndex)
						// i is not the last index: the i-th atom in the body
						// of this rule cannot be unfolded with a fact.
						temp.addLast(new PatternRuleLpInProgress(mgu, max));
					else if (max == iteration - 1) {
						// The last atom in the body of this rule can be
						// unfolded with a fact. This results in a new fact.
						HashMap<Term,Term> copies = new HashMap<>();
						result.add(PatternRuleLp.getInstance(
								(Function) this.head.deepCopy(copies),
								mgu.deepCopy(copies),
								iteration));
					}
				}
				else if (max == iteration - 1) {
					PatternTerm right = r_unfold.getRight();
					PatternSubstitution theta = right.getPatternSubs().composeWith(mgu);
					if (theta != null) {
						HashMap<Term, Term> copies = new HashMap<>();
						result.add(PatternRuleLp.getInstance(
								(Function) this.head.deepCopy(copies),
								mgu.deepCopy(copies),
								(Function) right.getBaseTerm().deepCopy(copies),
								theta.deepCopy(copies),
								iteration));
					}
				}
			}

		return result;
	}

	/**
	 * Returns a string representation of this
	 * rule relatively to the given set of
	 * variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	public String toString(Map<Variable,String> variables) {
		StringBuffer s = new StringBuffer(this.head.toString(variables, false));

		int k = this.body.length;
		if (k > 0) {
			s.append(" :- ");
			for (Term A: this.body) {
				s.append(A.toString(variables, false));
				if (--k > 0)
					s.append(", ");
			}
		}
		s.append(".");

		return s.toString();
	}

	/**
	 * Returns a String representation of this rule.
	 *
	 * @return a String representation of this rule
	 */
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
