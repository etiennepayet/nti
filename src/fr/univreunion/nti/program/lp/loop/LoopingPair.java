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

import java.util.LinkedList;
import java.util.List;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.SoP;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A looping pair i.e, a pair of the form (BinSeq, tau)
 * where binseq is a sequence of binary logic program
 * rules and tau is a DN set of positions for binseq.
 * 
 * Looping pairs are used for inferring single loops.
 *   
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LoopingPair implements LoopWitness {

	/**
	 * The binary sequence of this pair, ie a 
	 * sequence of binary logic program rules.
	 */
	private final LinkedList<BinaryRuleLp> binseq =
			new LinkedList<BinaryRuleLp>();

	/**
	 * The set of positions of this pair. This set
	 * of positions is supposed to be DN for the
	 * binary sequence of this pair.
	 */
	private final SoP tau;

	/**
	 * Constructs a looping pair whose binary sequence
	 * consists of the given rules and whose set of
	 * positions is the given one (this method does not
	 * check that the given set of positions is DN for
	 * the given binary sequence).
	 * 
	 * @param binseq the rules of the constructed pair
	 * @param tau the set of positions of the constructed pair
	 */
	public LoopingPair(List<BinaryRuleLp> binseq, SoP tau) {
		this.binseq.addAll(binseq);
		this.tau = tau;
	}

	/**
	 * Suppose this pair has the form <code>(BinSeq, tau)</code>.
	 * If the body atom of the given binary rule <code>R</code> is
	 * <code>tau</code>-more general than the head of the first
	 * rule of <code>BinSeq</code>, then a new looping pair
	 * <code>(BinSeq', tau')</code> is constructed and returned:
	 * <code>BinSeq'=[R].BinSeq</code> and <code>tau'</code>
	 * is a set of positions that is DN for <code>BinSeq'</code>.
	 * If the body atom of <code>R</code> is not <code>tau</code>-more
	 * general than the head of the first rule of <code>BinSeq</code>,
	 * then this looping pair is returned.
	 * 
	 * @param R a binary logic program rule
	 * @result a new looping pair if the body atom of <code>R</code> is
	 * <code>tau</code>-more general than the head of the first rule of
	 * <code>BinSeq</code> and this looping pair otherwise
	 */
	@Override
	public LoopingPair add(BinaryRuleLp R) {
		if (R.canBePluggedInto(this.binseq.getFirst(), this.tau)) {
			LinkedList<BinaryRuleLp> L = new LinkedList<BinaryRuleLp>();
			L.addAll(this.binseq);
			L.addFirst(R);
			return new LoopingPair(L, new SoP(R, L, this.tau));
		}
		return this;
	}

	/**
	 * Checks whether this pair is a witness of the
	 * existence of a single loop for the given mode,
	 * ie if the positions that are distinguished by
	 * the set of positions of this pair include
	 * the given mode.
	 * 
	 * @param m a mode for which a single loop is to
	 * be found
	 * @return a (non-<code>null</code>) query
	 * starting a single loop and corresponding to
	 * <code>m</code> or <code>null</code>, if this
	 * pair is not a witness of the existence of a
	 * single loop for <code>m</code>
	 */
	@Override
	public Function provesLoopingnessOf(Mode m) {
		if (this.binseq.isEmpty())
			return null;

		BinaryRuleLp R = this.binseq.getFirst();
		Function H = R.getHead();
		FunctionSymbol p = H.getRootSymbol();
		if (p == m.getPredSymbol()) {
			for (Integer i: m)
				if (!this.tau.inDomain(p, i) && !R.isGroundHeadArgument(i))
					return null;
			return H.ground(m, this.tau);
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
		return "single loop";
	}

	/**
	 * Returns a short String representation of this witness.
	 * 
	 * @return a short String representation of this witness
	 */
	@Override
	public String getShortDescription() {
		return "(extracted from a looping pair)";
		/*
		Path path = new Path();
		for (BinaryRuleLp R : this.binseq)
			path.addAll(R.getPath());

		return "(extracted from a looping pair)\n" +
				"  The single loop is " + path;
		 */
	}

	/**
	 * Returns a string representation of this looping pair.
	 * 
	 * @return a string representation of this looping pair
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer("Looping pair: binseq = <");
		int k = this.binseq.size();
		for (BinaryRuleLp R: this.binseq) {
			s.append(R.toSimpleString());
			if (--k > 0) s.append(", ");
		}
		s.append(">, DN set of positions = ");
		s.append(this.tau);

		return s.toString();
	}
}
