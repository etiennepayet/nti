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

import java.util.Map;

import fr.univreunion.nti.program.trs.polynomial.PolynomialConst;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A weight function, i.e., a mapping from function and tuple
 * symbols to non-negative real numbers.
 * <p>
 * Used in the Knuth-Bendix order technique for proving
 * termination of TRSs.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class WeightFunction extends PolyInterpretation {

	/**
	 * The weight associated with all the variables.
	 */
	private final PolynomialConst w = new PolynomialConst();

	/**
	 * Returns an array that consists of the weight
	 * that this function associates with the
	 * provided symbol.
	 * <p>
	 * If the provided symbol is not referenced in
	 * this object yet, then a new weight is created
	 * for it.
	 * 
	 * @param f a function or tuple symbol
	 * @return an array that consists of the weight
	 * that this function associates with the
	 * provided symbol
	 */
	@Override
	public PolynomialConst[] get(FunctionSymbol f) {
		return this.interpretation.computeIfAbsent(f, this::createWeight);
	}

	/**
	 * Creates a weight for a previously unreferenced symbol and updates the
	 * corresponding coefficient count.
	 *
	 * @param symbol the symbol whose weight is created
	 * @return the newly created weight
	 */
	private PolynomialConst[] createWeight(FunctionSymbol symbol) {
		PolynomialConst[] weight = { new PolynomialConst() };

		if (symbol.isTupleSymbol()) this.nbTupleCoefficients += weight.length;
		else this.nbFunctionCoefficients += weight.length;

		return weight;
	}

	/**
	 * Returns the weight associated with all the variables.
	 * 
	 * @return the weight associated with all the variables
	 */
	public PolynomialConst getVariableWeight() {
		return this.w;
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		StringBuilder s = new StringBuilder("{");

		// The weight associated with all the variables.
		s.append("variables:");
		s.append(this.w);

		// The weights associated with the function
		// and tuples symbols.
		for (Map.Entry<FunctionSymbol, PolynomialConst[]> e : this.interpretation.entrySet()) {
			s.append(", ");
			s.append(e.getKey().toString());
			s.append(":");
			Integer v = e.getValue()[0].getValue(); 
			s.append(v == null ? "?" : v.toString());
		}

		s.append("}");

		return s.toString();
	}
}
