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

package fr.univreunion.nti.program.lp.loop;

import fr.univreunion.nti.program.RecurrentPair;
import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;

/**
 * A recurrent pair in LP for proving the
 * existence of a binary loop.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RecurrentPairLp implements LoopWitness {

	/**
	 * The rule pi1 of this DPP.
	 */
	private final BinaryRuleLp pi1;

	/**
	 * The rule pi2 of this DPP.
	 */
	private final BinaryRuleLp pi2;

	/**
	 * A recurrent pair constructed from this DPP.
	 */
	private final RecurrentPair recPair;

	/**
	 * A binary-looping atomic query provided by this DPP
	 * and extracted from <code>recPair</code>.
	 */
	private final Function binaryLooping;

	/**
	 * Builds an incomplete DPP containing only
	 * the rule pi2.
	 * 
	 * This DPP will have to be completed later
	 * using method <code>add</code>.
	 * 
	 * @param pi2 the rule pi2 of this DPP
	 * @throws IllegalArgumentException if <code>pi2</code>
	 * is <code>null</code>
	 */
	public RecurrentPairLp(BinaryRuleLp pi2) {
		if (pi2 == null)
			throw new IllegalArgumentException(
					"construction of a DPP with a null rule");

		this.pi1 = null;
		this.pi2 = pi2;
		this.recPair = null;
		this.binaryLooping = null;
	}

	/**
	 * Constructs a DPP whose binary rules are the
	 * provided ones.
	 * 
	 * The provided rules are supposed to be
	 * non-<code>null</code>.
	 * 
	 * @param pi1 (non-<code>null</code>)
	 * the first rule of this DPP
	 * @param pi2 (non-<code>null</code>)
	 * the second rule of this DPP
	 * @throws NullPointerException if <code>pi1</code>
	 * or <code>pi2</code> is <code>null</code>
	 */
	private RecurrentPairLp(BinaryRuleLp pi1, BinaryRuleLp pi2) {

		Function binaryLooping = null;
		RecurrentPair recPair = null;

		// We try to build a recurrent pair from this DPP.
		Function H1 = pi1.getHead();
		Term B1 = pi1.getBody(0);
		Function H2 = pi2.getHead();
		Term B2 = pi2.getBody(0);
		// First, we try with the DPP ['pi1', 'pi2'].
		recPair = RecurrentPair.getInstance(H1, B1, H2, B2);
		// If the DPP ['pi1', 'pi2'] provided nothing,
		// we try with the DPP ['pi2', 'pi1'].
		if (recPair == null) {
			BinaryRuleLp pi = pi1;
			pi1 = pi2;
			pi2 = pi;
			recPair = RecurrentPair.getInstance(H2, B2, H1, B1);
		}

		if (recPair != null)
			// Here, a recurrent pair could be built. We
			// get a binary-looping atomic query from it.
			binaryLooping = recPair.getNonTerminatingGoal();

		this.pi1 = pi1;
		this.pi2 = pi2;
		this.binaryLooping = binaryLooping;
		this.recPair = recPair;
	}

	/**
	 * Builds a complete DPP from this one and
	 * the provided binary rule.
	 * 
	 * If this DPP is already complete then just
	 * returns this DPP.
	 * 
	 * @param pi1 a binary logic program rule
	 * @result a new DPP or this DPP
	 * @throws IllegalArgumentException if <code>pi1</code>
	 * is <code>null</code>
	 */
	@Override
	public RecurrentPairLp add(BinaryRuleLp pi1) {

		if (pi1 == null)
			throw new IllegalArgumentException(
					"construction of a DPP with a null rule");

		// Here, necessarily pi2 != null
		// (see public constructor above).

		if (this.pi1 == null) {
			RecurrentPairLp dpp = new RecurrentPairLp(pi1, this.pi2);
			if (dpp.recPair != null) return dpp;
		}

		return this;
	}

	/**
	 * Checks whether this pair is a witness for
	 * the existence of a binary loop for the
	 * given mode.
	 * 
	 * @param m a mode for which a binary loop is
	 * to be found
	 * @return a (non-<code>null</code>) query 
	 * starting a binary loop and corresponding
	 * to <code>m</code> or <code>null</code>,
	 * if this pair is not a witness of the
	 * existence of a binary loop for
	 * <code>m</code>
	 */
	@Override
	public Function provesLoopingnessOf(Mode m) {
		if (this.binaryLooping != null) {
			if (this.binaryLooping.getRootSymbol() == m.getPredSymbol()) {
				for (Integer i: m)
					if (!this.binaryLooping.get(new Position(i)).isGround())
						return null;
				return this.binaryLooping;
			}
		}
		return null;
	}

	/**
	 * Returns a String representation of the kind
	 * of loopingness witnessed by this object.
	 * 
	 * @return a String representation of the kind
	 * of loopingness witnessed by this object
	 */
	@Override
	public String getLoopKind() {
		return "binary loop";
	}

	/**
	 * Returns a short String representation of this witness.
	 * 
	 * @return a short String representation of this witness
	 */
	@Override
	public String getShortDescription() {
		return "(extracted from a recurrent pair)\n" +
				"  The stem to the loop is " + 
				this.pi1.getPath() +
				" and the loop is " + this.pi2.getPath();
	}

	/**
	 * Returns a string representation of this DPP.
	 * 
	 * @return a string representation of this DPP
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer();

		s.append("Recurrent pair: ");
		s.append(this.recPair);
		s.append(" for the DPP: <");
		s.append(this.pi1.toSimpleString());
		s.append(", ");
		s.append(this.pi2.toSimpleString());
		s.append(">");

		return s.toString();
	}
}
