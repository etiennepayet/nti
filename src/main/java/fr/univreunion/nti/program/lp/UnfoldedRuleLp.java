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

import java.util.HashMap;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;

/**
 * A rule which results from unfolding a logic program rule.
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class UnfoldedRuleLp extends RuleLp {

	/**
	 * The iteration of the unfolding operator
	 * at which this rule is generated.
	 */
	private final int iteration;
	
	/**
	 * Constructs an unfolded LP rule from the specified head,
	 * body and iteration.
	 * <p>
	 * If the specified body contains exactly one atom, then
	 * the returned rule is a <code>BinaryRuleLp</code>.
	 * 
	 * @param head the head of the rule 
	 * @param body the body of the rule 
	 * @param iteration the iteration of the unfolding operator
	 * at which the rule was generated
	 * @throws IllegalArgumentException if the given head
	 * is <code>null</code> or if the given body or
	 * a given body atom is <code>null</code>
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public static UnfoldedRuleLp of(
			Function head, Function[] body, int iteration) {

		if (body != null && body.length == 1)
			return new BinaryRuleLp(head, body[0], iteration);

		return new UnfoldedRuleLp(head, body, iteration);
	}

	/**
	 * Constructs an unfolded LP fact from the specified head
	 * and iteration.
	 * <p>
	 * The returned unfolded rule has an empty body.
	 * 
	 * @param head the head of the fact
	 * @param iteration the iteration of the unfolding operator
	 * at which the fact was generated
	 * @throws IllegalArgumentException if the given
	 * head is <code>null</code>
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public static UnfoldedRuleLp fact(
			Function head, int iteration) {

		return new UnfoldedRuleLp(head, iteration);
	}

	/**
	 * Constructs an unfolded LP rule from the given head,
	 * body and iteration.
	 * 
	 * @param head the head of the rule 
	 * @param body the body of the rule 
	 * @param iteration the iteration of the unfolding operator
	 * at which the rule was generated
	 * @throws IllegalArgumentException if the given head
	 * is <code>null</code> or if the given body or
	 * a given body atom is <code>null</code>
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	protected UnfoldedRuleLp(
			Function head, Function[] body, int iteration) {
		
		super(head, body);

		if (iteration < 0)
			throw new IllegalArgumentException(
					"construction of an unfolded LP rule with a negative iteration");

		this.iteration = iteration;
	}

	/**
	 * Constructs an unfolded LP fact from the given head and iteration.
	 * 
	 * @param head the head of the fact
	 * @param iteration the iteration of the unfolding operator
	 * at which this fact was generated
	 * @throws IllegalArgumentException if the given head 
	 * is <code>null</code>
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	protected UnfoldedRuleLp(Function head, int iteration) {
		super(head);

		if (iteration < 0)
			throw new IllegalArgumentException(
					"construction of an unfolded LP rule with a negative iteration");

		this.iteration = iteration;
	}

	/**
	 * Returns the iteration of the unfolding operator
	 * at which this rule is generated.
	 * 
	 * @return the iteration of the unfolding operator
	 * at which this rule is generated
	 */
	public int getIteration() {
		return this.iteration;
	}
	
	/**
	 * Returns a deep copy of this rule i.e., a copy where
	 * each subterm is also copied. The iteration of the
	 * generated copy is set to the specified iteration.
	 * 
	 * @param iteration the iteration attribute of the
	 * generated copy
	 * @return a deep copy of this rule
	 */
	public UnfoldedRuleLp deepCopy(int iteration) {
		HashMap<Term,Term> copies = new HashMap<>();

		Function[] copiedBody = new Function[this.body.length];
		int bodyIndex = 0;
		for (Function atom : this.body)
			copiedBody[bodyIndex++] = (Function) atom.deepCopy(copies);

		return UnfoldedRuleLp.of((Function) this.head.deepCopy(copies),
				copiedBody, iteration);
	}

	/**
	 * Returns a deep copy of this rule i.e., a copy where
	 * each subterm is also copied.
	 * 
	 * @return a deep copy of this rule
	 */
	public UnfoldedRuleLp deepCopy() {
		return this.deepCopy(this.iteration);
	}
}
