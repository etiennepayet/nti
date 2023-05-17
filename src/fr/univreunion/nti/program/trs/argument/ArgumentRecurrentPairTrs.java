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

package fr.univreunion.nti.program.trs.argument;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.RecurrentPair;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.loop.comp.UnfoldedRuleTrsLoopComp;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A nontermination proof argument in term rewriting.
 * It is produced by a recurrent pair.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentRecurrentPairTrs implements Argument {

	/**
	 * The recurrent pair that provides this argument.
	 */
	private final RecurrentPair recPair;

	/**
	 * The unfolded rule that provides this argument.
	 */
	private final UnfoldedRuleTrsLoopComp unfolded;

	/**
	 * Builds a nontermination argument.
	 * 
	 * @param recPair the recurrent pair that
	 * provides this argument
	 * @param unfolded the unfolded rule that
	 * provides this argument
	 */
	public ArgumentRecurrentPairTrs(RecurrentPair recPair, 
			UnfoldedRuleTrsLoopComp unfolded) {

		this.recPair = recPair;
		this.unfolded = unfolded;
	}

	/**
	 * Returns a detailed String representation of
	 * this argument (usually used while printing
	 * proofs in verbose mode).
	 * 
	 * @param indentation the number of single spaces
	 * to print at the beginning of each line of the
	 * detailed representation
	 * @return a detailed String representation of
	 * this argument
	 */
	@Override
	public String getDetails(int indentation) {
		StringBuffer s = new StringBuffer();

		for (int i = 0; i < indentation; i++) s.append(" ");
		s.append("Here is the successful unfolding. Let IR be the TRS under analysis.\n");

		int n = this.unfolded.getIteration();

		ParentTrs parent;
		if ((parent = this.unfolded.getParent()) != null) {
			s.append(parent.toString(indentation) + "\n");
			for (int i = 0; i < indentation; i++) s.append(" ");
			s.append("==> L" + n + " = " + this.unfolded);
		}
		else {
			for (int i = 0; i < indentation; i++) s.append(" ");
			s.append("L" + n + " = " + this.unfolded);
		}
		s.append(" is in U_IR^" + n + ".");

		return s.toString();
	}

	/**
	 * Returns a String representation of the kind
	 * of witness provided by this argument.
	 * 
	 * @return a String representation of the kind
	 * of witness provided by this argument
	 */
	@Override
	public String getWitnessKind() {
		// return "binary loop";
		return "recurrent pair";
	}

	/**
	 * Returns a string representation of this argument.
	 * 
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		Map<Variable,String> variables = new HashMap<Variable,String>();
		String certificate = this.recPair.getNonTerminatingTerm().
				toFunction().toString(variables, false);
		Term s = this.recPair.getS();
		Term t = this.recPair.getT();

		return
				// "* Certificate: " + certificate + " from a " + this.getWitnessKind() +
				// "\n* Description:\n" + 
				"* Certificate: " + certificate + " is non-terminating\n" +
				"* Description:\n" + 
				"The following recurrent pair was generated while unfolding\n" +
				"the dependency pairs of the analyzed TRS [iteration = " +
				this.unfolded.getIteration() + "]:\n" +
				"r1 = " + this.recPair.getLeft1().toString(variables, false) +
				" -> " + this.recPair.getRight1().toString(variables, false) +
				"\nr2 = " + this.recPair.getLeft2().toString(variables, false) +
				" -> " + this.recPair.getRight2().toString(variables, false) +
				"\n(i,j) = (" + this.recPair.getI() + "," + this.recPair.getJ() + ")" +
				"\nc = " + this.recPair.getContext().toString(variables, false) +
				(s == t ? "\ns = t = " + s.toString(variables, false) :
					"\ns = " + s.toString(variables, false) +
					"\nt = " + t.toString(variables, false)) +
				"\n(n1,n2,n3) = (" + this.recPair.getN1() +
				"," + this.recPair.getN2() +
				"," + this.recPair.getN3() + ")";
	}
}
