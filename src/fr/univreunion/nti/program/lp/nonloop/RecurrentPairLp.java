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

package fr.univreunion.nti.program.lp.nonloop;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.RecurrentPair;
import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A recurrent pair in LP for proving the existence of
 * a binary chain (see Sect. 5 of [Payet, JAR'24]).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RecurrentPairLp implements NonTerminationWitness {

	/**
	 * The rule R1 of this recurrent pair.
	 */
	private final BinaryRuleLp R1;

	/**
	 * The rule R2 of this recurrent pair.
	 */
	private final BinaryRuleLp R2;

	/**
	 * A recurrent pair constructed from R1 and R2.
	 */
	private final RecurrentPair recPair;

	/**
	 * Builds an incomplete recurrent pair containing
	 * only the rule R2.
	 * 
	 * This recurrent pair will have to be completed
	 * later using method <code>add</code>.
	 * 
	 * @param R2 the rule R2 of this recurrent pair
	 * @throws IllegalArgumentException if <code>R2</code>
	 * is <code>null</code>
	 */
	public RecurrentPairLp(BinaryRuleLp R2) {
		if (R2 == null)
			throw new IllegalArgumentException(
					"construction of a recurrent pair with a null rule");

		this.R1 = null;
		this.R2 = R2;
		this.recPair = null;
	}

	/**
	 * Constructs a recurrent pair whose binary rules
	 * are the provided ones.
	 * 
	 * The provided rules are supposed to be
	 * non-<code>null</code>.
	 * 
	 * @param R1 (non-<code>null</code>)
	 * the first rule of this recurrent pair
	 * @param R2 (non-<code>null</code>)
	 * the second rule of this recurrent pair
	 * @throws NullPointerException if <code>R1</code>
	 * or <code>R2</code> is <code>null</code>
	 */
	private RecurrentPairLp(BinaryRuleLp R1, BinaryRuleLp R2) {

		this.R1 = R1;
		this.R2 = R2;

		// We try to build a recurrent pair from R1 and R2.
		Function H1 = R1.getHead();
		Term B1 = R1.getBody(0);
		Function H2 = R2.getHead();
		Term B2 = R2.getBody(0);
		this.recPair = RecurrentPair.getInstance(H1, B1, H2, B2);
	}

	/**
	 * Builds a complete recurrent pair from this
	 * one and the provided binary rule.
	 * 
	 * If this recurrent pair is already complete
	 * then just returns this recurrent pair.
	 * 
	 * @param R1 a binary logic program rule
	 * @result a new recurrent pair or this
	 * recurrent pair
	 * @throws IllegalArgumentException if <code>R1</code>
	 * is <code>null</code>
	 */
	@Override
	public RecurrentPairLp add(BinaryRuleLp R1) {

		if (R1 == null)
			throw new IllegalArgumentException(
					"construction of a recurrent pair with a null rule");

		// Here, necessarily R2 != null
		// (see public constructor above).

		if (this.R1 == null) {
			RecurrentPairLp pair = new RecurrentPairLp(R1, this.R2);
			if (pair.recPair != null) return pair;
		}

		return this;
	}

	/**
	 * Checks whether this pair is a witness for
	 * the existence of a binary chain for the
	 * given mode.
	 * 
	 * @param m a mode for which a binary chain
	 * is to be found
	 * @return a (non-<code>null</code>) atomic
	 * query starting a binary chain corresponding
	 * to <code>m</code> or <code>null</code>,
	 * if this pair is not a witness of the
	 * existence of a binary chain for
	 * <code>m</code>
	 */
	@Override
	public Function provesNonTerminationOf(Mode m) {
		if (this.recPair != null) {
			Function nonterminating = this.recPair.getNonTerminatingTerm();
			if (nonterminating != null) {
				if (nonterminating.getRootSymbol() == m.getPredSymbol()) {
					for (int i: m)
						if (!nonterminating.get(i).isGround())
							return null;
					return nonterminating;
				}
			}
		}

		return null;
	}

	/**
	 * Returns a short String representation of this witness.
	 * 
	 * @return a short String representation of this witness
	 */
	@Override
	public String getShortDescription() {
		return "(extracted from a recurrent pair [Payet, JAR'24+LOPSTR'25])";
	}

	/**
	 * Returns a string representation of this
	 * recurrent pair.
	 * 
	 * @return a string representation of this
	 * recurrent pair
	 */
	@Override
	public String toString() {
		if (this.recPair != null) {
			Map<Variable,String> variables = new HashMap<Variable,String>();
			return
					"Recurrent pair: <[" +
					this.recPair.getLeft1().toString(variables, false) +
					" :- " + this.recPair.getRight1().toString(variables, false) +
					", " + this.recPair.getLeft2().toString(variables, false) +
					" :- " + this.recPair.getRight2().toString(variables, false) +
					", c1 = " + this.recPair.getContextC1().toString(variables, false) +
					", c2 = " + this.recPair.getContextC2().toString(variables, false) +
					", s = " + this.recPair.getS().toString(variables, false) +
					", t = " + this.recPair.getT().toString(variables, false) +
					", (m1,m2) = (" + this.recPair.getM1() +
					"," + this.recPair.getM2() + 
					"), (n1,n2,n3,n4) = (" + this.recPair.getN1() +
					"," + this.recPair.getN2() +
					"," + this.recPair.getN3() +
					"," + this.recPair.getN4() +
					"), non-terminating query = " +
					this.recPair.getNonTerminatingTerm() +
					"> (Def.3 + Cor. 1 of [Payet, LOPSTR'25])";
			// return this.recPair.toString();
		}

		return super.toString();
	}
}
