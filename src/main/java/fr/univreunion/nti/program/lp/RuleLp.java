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

package fr.univreunion.nti.program.lp;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.lp.binaryunfolding.RuleLpBinaryUnfolder;
import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.program.lp.patternunfolding.RuleLpPatternUnfolder;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A logic program rule.
 * <p>
 * An object of this class is mutable
 * (because a term is mutable).
 *
 * <p>The binary unfolding operator is from M. Codish and C. Taboch,
 * <a href="https://doi.org/10.1016/S0743-1066(99)00006-0">A Semantic
 * Basis for the Termination Analysis of Logic Programs</a>, Journal of
 * Logic Programming 41(1), 103--123, 1999. The pattern unfolding operator
 * is from E. Payet,
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10">Recurrent Pairs
 * Revisited</a>, LOPSTR 2025, LNCS 16117, 154--164, 2026.
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
	 * <p>
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
	 * <p>
	 * Applies the T^{\beta}_P operator of Codish and Taboch (1999), cited
	 * in the class documentation, to this rule.
	 * 
	 * @param unfoldingRules a collection of rules for unfolding this rule
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 * @throws IllegalArgumentException if the given iteration
	 * is negative or zero
	 */
	public Collection<UnfoldedRuleLp> unfold(
			Collection<UnfoldedRuleLp> unfoldingRules, int iteration) {

		return RuleLpBinaryUnfolder.unfold(this, unfoldingRules, iteration);
	}

	/**
	 * Unfolds this rule once using the given collection of rules.
	 * <p>
	 * Applies the T^{\pi}_{P,B} operator of Payet (LOPSTR 2025), cited in
	 * the class documentation, to this rule.
	 * <p>
	 * It is supposed that the provided collections consist of
	 * pattern rules (p,q) where both p and q are simple pattern
	 * terms (see Definition 9 of that article).
	 * 
	 * @param unfoldingRules a collection of rules for unfolding this rule
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 * @throws IllegalArgumentException if the given iteration
	 * is negative or zero
	 */
	public Collection<PatternRuleLp> unfoldPattern(
			Collection<PatternRuleLp> unfoldingRules, int iteration) {

		return RuleLpPatternUnfolder.unfold(this, unfoldingRules, iteration);
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
		StringBuilder s = new StringBuilder(this.head.toString(variables, false));

		int k = this.body.length;
		if (k > 0) {
			s.append(" :- ");
			for (Term atom: this.body) {
				s.append(atom.toString(variables, false));
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
