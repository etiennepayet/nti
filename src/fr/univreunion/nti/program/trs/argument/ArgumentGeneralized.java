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
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Variable;

/**
 * A non-termination argument produced when searching for
 * a generalized rewrite rule. It embeds the rewrite
 * rule that provides this argument.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentGeneralized implements Argument {

	/**
	 * The rule that provides this argument.
	 */
	private final RuleTrs R;

	/**
	 * Builds a non-termination argument
	 * provided by the specified generalized
	 * rewrite rule.
	 *
	 * @param R the generalized rewrite rule that
	 * provides this argument
	 */
	public ArgumentGeneralized(RuleTrs R) {
		this.R = R;
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
		return "";
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
		return "generalized rule";
	}
	
	/**
	 * Returns a string representation of this argument.
	 * 
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		Map<Variable,String> variables = new HashMap<Variable,String>();
		String certificate = this.R.getLeft().toString(variables, false);
		
		return
				// "* Certificate: " + certificate + " from a " + this.getWitnessKind() +
				// "\n* Description:\n" +
				"* Certificate: " + certificate + " is non-terminating\n" +
				"* Description:\n" + 
				"The following generalized rule was detected\n" +
				"in the analyzed TRS:\n" +
				this.R.toString(variables, false) +
				"\nHence, the term " + certificate +
				"\nstarts an infinite rewrite sequence w.r.t.\nthe analyzed TRS.";
	}
}
