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
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.loop.comp.UnfoldedRuleTrsLoopComp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Variable;

/**
 * A nontermination proof argument in term rewriting.
 * It is produced when searching for a binary loop
 * using recurrent pairs.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentRecurrentPairTrs implements Argument {

	/**
	 * The term that starts a binary loop.
	 */
	private final Function binaryLooping;

	/**
	 * The recurrent pair that provides this argument.
	 */
	private final UnfoldedRuleTrsLoopComp recPair;
		
	/**
	 * Builds a nontermination argument.
	 * 
	 * @param binaryLooping the term that starts a binary loop
	 * @param recPair the recurrent pair from which the
	 * binary-looping term was generated
	 */
	public ArgumentRecurrentPairTrs(Function binaryLooping, 
			UnfoldedRuleTrsLoopComp recPair) {
		
		this.binaryLooping = binaryLooping;
		this.recPair = recPair;
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
		
		int n = this.recPair.getIteration();
		
		ParentTrs parent;
		if ((parent = this.recPair.getParent()) != null) {
			s.append(parent.toString(indentation) + "\n");
			for (int i = 0; i < indentation; i++) s.append(" ");
			s.append("==> L" + n + " = " + this.recPair);
		}
		else {
			for (int i = 0; i < indentation; i++) s.append(" ");
			s.append("L" + n + " = " + this.recPair);
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
		return "binary loop";
	}
	
	/**
	 * Returns a string representation of this argument.
	 * 
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		Map<Variable,String> variables = new HashMap<Variable,String>();
		String certificate = this.binaryLooping.toFunction().toString(variables, false);
			
		return
				"* Certificate: " + certificate + " from a " + this.getWitnessKind() +
				"\n* Description:\n" + 
				"The following two rules were generated while unfolding\n" +
				"the dependency pairs of the analyzed TRS [iteration = " +
				this.recPair.getIteration() + "]:\n" +
				"r  = " + this.recPair.getFirst().toString(variables, false) +
				"\nr' = " + this.recPair.getSecond().toString(variables, false) +
				"\nThey form a recurrent pair (Def. 3.12 of\n" +
				"[Payet, Non-termination in TRS and LP]).\nSo, the term " +
				certificate +
				"\nstarts an infinite rewrite sequence w.r.t. the analyzed TRS.";
	}
}
