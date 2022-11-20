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

package fr.univreunion.nti.program.trs.argfiltering;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A pair of terms resulting from applying an argument filtering
 * to rewrite rules or dependency pairs. Used in the dependency
 * pair framework.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PairOfTerms {

	/**
	 * The rule that produces this pair.
	 */
	private RuleTrs R;

	/**
	 * The result of applying the argument filtering
	 * to the left-hand side of R.
	 */
	private Term left;

	/**
	 * The result of applying the argument filtering
	 * to the right-hand side of R.
	 */
	private Term right;

	/**
	 * Builds a pair of terms resulting from applying an
	 * argument filtering to the specified rule, which
	 * yields the specified terms.
	 */
	public PairOfTerms(RuleTrs R, Term left, Term right) {
		this.R = R;
		this.left = left;
		this.right = right;
	}
	
	/**
	 * Returns the rule that produced this pair.
	 * 
	 * @return the rule that produced this pair
	 */
	public RuleTrs getRule() {
		return this.R;
	}
	
	/**
	 * Returns the left-hand side of this pair.
	 * 
	 * @return the left-hand side of this pair
	 */
	public Term getLeft() {
		return this.left;
	}
	
	/**
	 * Returns the right-hand side of this pair.
	 * 
	 * @return the right-hand side of this pair
	 */
	public Term getRight() {
		return this.right;
	}
	
	/**
	 * Returns a String representation of this pair.
	 * 
	 * @return a String representation of this pair
	 */
	@Override
	public String toString() {
		Map<Variable, String> variables = new HashMap<Variable, String>();
		return
				this.left.toString(variables, false) +
				" -> " +
				this.right.toString(variables, false);
	}
}
