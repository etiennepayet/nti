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

package fr.univreunion.nti.program.trs.polynomial;

import java.util.Collection;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.term.Variable;

/**
 * A variable occurring in a polynomial.
 *
 * <p>The constraint-solving operations support the method of J. Giesl,
 * <a href="https://doi.org/10.1007/3-540-59200-8_77">Generating Polynomial
 * Orderings for Termination Proofs</a>, RTA 1995, LNCS 914, 426--431.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PolynomialVar implements Polynomial {

	/**
	 * The variable of this polynomial.
	 */
	private final Variable variable;

	/**
	 * Builds a variable polynomial.
	 * 
	 * @param variable the variable of this polynomial
	 * @throws NullPointerException if the provided
	 * variable is <code>Null</code>
	 */
	public PolynomialVar(Variable variable) {
		if (variable == null)
			throw new NullPointerException("creation of a polynomial variable from Null");

		this.variable = variable;
	}

	/**
	 * Computes the partial derivative of this polynomial
	 * with respect to the given variable.
	 * 
	 * @param v a variable for computing the partial derivative
	 * of this polynomial
	 * @return the partial derivative of this polynomial
	 * with respect to the given variable
	 */
	@Override
	public Polynomial partialDerivative(Variable v) {
		if (this.variable == v)
			return PolynomialConst.ONE;

		return PolynomialConst.ZERO;
	}

	/**
	 * Returns the polynomial resulting from replacing, in this 
	 * polynomial, all the specified variables with
	 * <code>mu</code>.
	 * 
	 * @param variables the variables to be replaced with
	 * <code>mu</code>
	 * @param mu the variable used in [Giesl, RTA'95] for
	 * solving polynomial constraints
	 * @return the polynomial resulting from replacing all
	 * the specified variables with <code>mu</code>
	 */
	@Override
	public Polynomial replaceWithMu(Deque<Variable> variables, PolynomialConst mu) {
		// The polynomial to return at the end.
		Polynomial result;

		if (variables.isEmpty()) {
			variables.add(this.variable);
			result = mu;
		}
		else if (variables.contains(this.variable))
			result = mu;
		else
			result = this;

		return result;
	}

	/**
	 * Returns the value of this <code>polynomial</code> as
	 * an <code>Integer</code>.
	 * 
	 * @param interpretation an interpretation of the variables of
	 * this polynomial
	 * @return the value of this <code>polynomial</code> as
	 * an <code>Integer</code>
	 */
	@Override
	public Integer integerValue(Map<Variable,Integer> interpretation) {
		if (interpretation == null)
			return null;

		return interpretation.get(this.variable);
	}

	/**
	 * Simplifies this polynomial using the current
	 * values of its coefficients.
	 * 
	 * @return this polynomial, as it is already
	 * in simplified form
	 */
	@Override
	public Polynomial simplify() {
		return this;
	}

	/**
	 * Checks whether this polynomial contains the given
	 * variable.
	 * 
	 * @param variable a variable
	 * @return <code>true</code> iff this polynomial
	 * contains <code>variable</code>
	 */
	@Override
	public boolean contains(Variable variable) {
		return this.variable == variable;
	}

	/**
	 * Returns a collection consisting of the monomials
	 * of this polynomial.
	 * 
	 * @return a collection consisting of the monomials
	 * of this polynomial
	 */
	@Override
	public Collection<Polynomial> getMonomials() {
		LinkedList<Polynomial> monomials = new LinkedList<>();
		monomials.add(this);

		return monomials;
	}

	/**
	 * Tries to check whether <code>P &ge; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &ge; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &ge; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean gez() {
		return false;
	}
	
	/**
	 * Tries to check whether <code>P &gt; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &gt; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &gt; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean gtz() {
		return false;
	}
	
	/**
	 * Tries to check whether <code>P &le; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &le; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &le; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean lez() {
		return false;
	}
	
	/**
	 * Tries to check whether <code>P &lt; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &lt; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &lt; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean ltz() {
		return false;
	}
	
	/**
	 * If this polynomial is the subtraction of two
	 * constant polynomials, then returns an array
	 * containing these two constant polynomials.
	 * Otherwise, returns <code>null</code>.
	 * 
	 * @return an array containing two constant
	 * polynomials, or <code>null</code>
	 */
	@Override
	public PolynomialConst[] subOperands() {
		return null;
	}

	/**
	 * Returns a string representation of this polynomial
	 * relatively to the given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(variable,s)</code>
	 * where <code>s</code> is the string associated to
	 * <code>variable</code>
	 * @return a string representation of this polynomial
	 */
	@Override
	public String toString(Map<Variable,String> variables) {
		return this.variable.toString(variables, false);
	}

	/**
	 * Returns a string representation of this polynomial.
	 * 
	 * @return a string representation of this polynomial
	 */
	@Override
	public String toString() {
		return this.variable.toString();
	}
}
