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

package fr.univreunion.nti.program.trs.reducpair;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
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
			new HashMap<FunctionSymbol, PolynomialConst[]>();

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
	 * @param C the interpretation to
	 * copy into this object.
	 */
	public PolyInterpretation(PolyInterpretation C) {

		for (Map.Entry<FunctionSymbol, PolynomialConst[]> e : C.interpretation.entrySet()) {
			PolynomialConst[] coefficients_e = e.getValue();
			PolynomialConst[] coefficients_e_copy = new PolynomialConst[coefficients_e.length];
			for (int i = 0; i < coefficients_e.length; i++)
				coefficients_e_copy[i] = new PolynomialConst(coefficients_e[i].getValue());
			this.interpretation.put(e.getKey(), coefficients_e_copy);
		}

		this.nbFunctionCoefficients = C.nbFunctionCoefficients;
		this.nbTupleCoefficients = C.nbTupleCoefficients;
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
		Collection<PolynomialConst> L = new LinkedList<PolynomialConst>();

		for (Map.Entry<FunctionSymbol, PolynomialConst[]> e : this.interpretation.entrySet())
			for (PolynomialConst c : e.getValue())
				L.add(c);

		return L;
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
	 * 
	 * If the provided symbol is not referenced in
	 * this object yet, then a new polynomial is
	 * created for it.
	 * 
	 * @param f a function or tuple symbol
	 * @return the coefficients of the polynomial
	 * associated with the provided symbol
	 */
	public PolynomialConst[] get(FunctionSymbol f) {

		// The coefficients that will be returned.
		PolynomialConst[] C;

		if ((C = this.interpretation.get(f)) == null) {
			// If the provided symbol does not have any
			// coefficients yet, we create some for it.
			// If the symbol has arity n, then it has
			// 2^n = (1 << n) coefficients.
			C = new PolynomialConst[1 << f.getArity()];
			for (int i = 0; i < C.length; i++)
				// Each coefficient has an undefined value.
				C[i] = new PolynomialConst();
			this.interpretation.put(f, C);

			if (f.isTupleSymbol()) this.nbTupleCoefficients += C.length;
			else this.nbFunctionCoefficients += C.length; 
		}

		return C;
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
	private String toStringSymbol(FunctionSymbol f) {
		// We build a term of the form f(X1,...,Xn)
		// and compute its corresponding polynomial.

		// The variables X1,...,Xn.
		List<Variable> Args = new LinkedList<Variable>();

		// The term f(X1,...,Xn).
		for (int i = 0; i < f.getArity(); i++)
			Args.add(new Variable());
		Function F_f = new Function(f, Args);

		// The polynomial associated with f(X1,...,Xn),
		// in simplified form.
		Polynomial P_f = F_f.toPolynomial(this).simplify();

		return F_f + ":[" + P_f + "]";
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer("{");

		boolean notfirst = false;
		for (Map.Entry<FunctionSymbol, PolynomialConst[]> e : 
			this.interpretation.entrySet()) {

			if (notfirst) s.append(", ");
			else notfirst = true;

			s.append(this.toStringSymbol(e.getKey()));
		}

		s.append("}");

		return s.toString();
	}
}
