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

package fr.univreunion.nti.program.trs.reducpair;

import fr.univreunion.nti.program.trs.polynomial.PolynomialConst;

/**
 * A polynomial order.
 *
 * <p>The constraint-solving method is from J. Giesl,
 * <a href="https://doi.org/10.1007/3-540-59200-8_77">Generating Polynomial
 * Orderings for Termination Proofs</a>, RTA 1995, LNCS 914, 426--431.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PolyOrder implements ReducPair {

	/**
	 * The polynomial interpretation that 
	 * induces this order.
	 */
	private final PolyInterpretation interpretation;

	/**
	 * The variable used in [Giesl, RTA'95] for solving
	 * polynomial constraints.
	 */
	private final PolynomialConst mu;

	/**
	 * Builds a polynomial interpretation from the
	 * specified elements.
	 * 
	 * @param interpretation a polynomial interpretation
	 * @param mu the variable used in [Giesl, RTA'95]
	 * for solving polynomial constraints
	 */
	public PolyOrder(PolyInterpretation interpretation,
			PolynomialConst mu) {
		
		this.interpretation = interpretation;
		this.mu = mu;
	}
	
	/**
	 * Returns the polynomial interpretation that
	 * induces this order.
	 * 
	 * @return the polynomial interpretation that
	 * induces this order
	 */
	public PolyInterpretation getInterpretation() {
		return this.interpretation;
	}
	
	/**
	 * Returns the variable used in [Giesl, RTA'95]
	 * for solving polynomial constraints and that
	 * induces this order.
	 * 
	 * @return the variable used in [Giesl, RTA'95]
	 * for solving polynomial constraints and that
	 * induces this order
	 */
	public PolynomialConst getMu() {
		return this.mu;
	}

	/**
	 * Returns a string representation of this object.
	 * 
	 * @param indentation the number of single spaces
	 * to print at the beginning of each line
	 * @return a string representation of this object
	 */
	@Override
	public String toString(int indentation) {
		String indent = " ".repeat(Math.max(0, indentation));

		return indent + "Polynomial order induced by the interpretation: " + this.interpretation
				+ "\n" + indent + "and the value mu = " + this.mu + " (see [Giesl, RTA'95])";
	}
}
