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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.trs.polynomial.Polynomial;
import fr.univreunion.nti.program.trs.polynomial.PolynomialConst;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Variable;

/**
 * A polynomial interpretation, i.e., a mapping from function
 * and tuple symbols to polynomials.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PolyInterpretation {

	/**
	 * The mapping from function/tuple symbols to polynomials,
	 * given as arrays of coefficients.
	 * The array of coefficients associated with each symbol is
	 * never empty.
	 */
	protected final Map<FunctionSymbol, PolynomialConst[]> interpretation =
            new HashMap<>();

	/**
	 * The number of coefficients stored in this
	 * object and associated with function symbols.
	 */
	protected int nbFunctionCoefficients = 0;

	/**
	 * The number of coefficients stored in this
	 * object and associated with tuple symbols.
	 */
	protected int nbTupleCoefficients = 0;

	/**
	 * Builds an empty interpretation.
	 */
	public PolyInterpretation() {}

	/**
	 * Copy constructor.
	 *
	 * @param source the interpretation to
	 * copy into this object.
	 */
	public PolyInterpretation(PolyInterpretation source) {

		for (Map.Entry<FunctionSymbol, PolynomialConst[]> entry : source.interpretation.entrySet()) {
			PolynomialConst[] sourceCoefficients = entry.getValue();
			PolynomialConst[] copiedCoefficients =
					new PolynomialConst[sourceCoefficients.length];
			for (int i = 0; i < sourceCoefficients.length; i++)
				copiedCoefficients[i] = new PolynomialConst(sourceCoefficients[i].getValue());
			this.interpretation.put(entry.getKey(), copiedCoefficients);
		}

		this.nbFunctionCoefficients = source.nbFunctionCoefficients;
		this.nbTupleCoefficients = source.nbTupleCoefficients;
	}

	/**
	 * Returns a collection consisting of the coefficients of
	 * all the polynomials stored in this interpretation.
	 *
	 * @return a collection consisting of the coefficients of
	 * all the polynomials stored in this interpretation
	 */
	public Collection<PolynomialConst> getAllCoefficients() {

		// The collection to return at the end.
		Collection<PolynomialConst> coefficients = new ArrayList<>();

		for (Map.Entry<FunctionSymbol, PolynomialConst[]> entry : this.interpretation.entrySet())
			Collections.addAll(coefficients, entry.getValue());

		return coefficients;
	}

	/**
	 * Returns the number of polynomial coefficients
	 * stored in this object and associated with
	 * function symbols.
	 *
	 * @return the number of polynomial coefficients
	 * stored in this object and associated with
	 * function symbols
	 */
	public int getNbFunctionCoefficients() {
		return this.nbFunctionCoefficients;
	}

	/**
	 * Returns the coefficients of the polynomial
	 * associated with the provided symbol.
	 * <p>
	 * If the provided symbol is not referenced in
	 * this object yet, then a new polynomial is
	 * created for it.
	 *
	 * @param symbol a function or tuple symbol
	 * @return the coefficients of the polynomial
	 * associated with the provided symbol
	 */
	public PolynomialConst[] get(FunctionSymbol symbol) {

		// The coefficients that will be returned.
		PolynomialConst[] coefficients;

		if ((coefficients = this.interpretation.get(symbol)) == null) {
			// If the provided symbol does not have any
			// coefficients yet, we create some for it.
			// If the symbol has arity n, then it has
			// 2^n = (1 << n) coefficients.
			coefficients = new PolynomialConst[1 << symbol.getArity()];
			for (int i = 0; i < coefficients.length; i++)
				// Each coefficient has an undefined value.
				coefficients[i] = new PolynomialConst();
			this.interpretation.put(symbol, coefficients);

			if (symbol.isTupleSymbol()) this.nbTupleCoefficients += coefficients.length;
			else this.nbFunctionCoefficients += coefficients.length;
		}

		return coefficients;
	}

	/**
	 * Returns an iterator over the function/tuple symbols
	 * in the domain of this object.
	 */
	public Iterator<FunctionSymbol> symbolsIterator() {
		return this.interpretation.keySet().iterator();
	}

	/**
	 * Returns a string representation of the polynomial
	 * associated with the specified symbol.
	 */
	private String toStringSymbol(FunctionSymbol symbol) {
		// We build a term of the form f(X1,...,Xn)
		// and compute its corresponding polynomial.

		// The variables X1,...,Xn.
		List<Variable> arguments = new ArrayList<>();

		// The term f(X1,...,Xn).
		for (int i = 0; i < symbol.getArity(); i++)
			arguments.add(new Variable());
		Function function = new Function(symbol, arguments);

		// The polynomial associated with f(X1,...,Xn),
		// in simplified form.
		Polynomial polynomial = function.toPolynomial(this).simplify();

		return function + ":[" + polynomial + "]";
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		StringBuilder s = new StringBuilder("{");

		boolean notFirst = false;
		for (Map.Entry<FunctionSymbol, PolynomialConst[]> e :
			this.interpretation.entrySet()) {

			if (notFirst) s.append(", ");
			else notFirst = true;

			s.append(this.toStringSymbol(e.getKey()));
		}

		s.append("}");

		return s.toString();
	}
}
