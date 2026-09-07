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
 * @param rule the rule that produces this pair
 * @param left the result of applying the argument filtering
 * to the left-hand side of the rule
 * @param right the result of applying the argument filtering
 * to the right-hand side of the rule
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public record PairOfTerms(RuleTrs rule, Term left, Term right) {

	/**
	 * Preserves the identity equality of the former class.
	 */
	@Override
	public boolean equals(Object other) {
		return this == other;
	}

	/**
	 * Preserves the identity hash code of the former class.
	 */
	@Override
	public int hashCode() {
		return System.identityHashCode(this);
	}
	
	/**
	 * Returns a String representation of this pair.
	 * 
	 * @return a String representation of this pair
	 */
	@Override
	public String toString() {
		Map<Variable, String> variables = new HashMap<>();
		return
				this.left.toString(variables, false) +
				" -> " +
				this.right.toString(variables, false);
	}
}
