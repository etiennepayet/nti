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

package fr.univreunion.nti.program.trs.polynomial;

import java.util.Collection;
import java.util.Deque;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.term.Variable;

/**
 * A constant polynomial with defined or undefined value.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PolynomialConst implements Polynomial {

	/**
	 * An instance counter.
	 */
	private static int ID = 0;

	/**
	 * The constant 0.
	 */
	public static final PolynomialConst ZERO = new PolynomialConst(0);

	/**
	 * The constant 1.
	 */
	public static final PolynomialConst ONE = new PolynomialConst(1);

	/**
	 * An identifier for this constant polynomial.
	 */
	private final int id;

	/**
	 * The value of this constant polynomial.
	 */
	private Integer value;

	/**
	 * Resets the instance counter.
	 */
	public static void resetIDs() {
		ID = 0;
	}
	
	/**
	 * Builds a constant polynomial with an undefined value.
	 * Used for creating variable coefficients in polynomials.
	 */
	public PolynomialConst() {
		this.value = null;
		this.id = ID++;
	}

	/**
	 * Builds a constant polynomial.
	 * 
	 * @param v the value of this constant polynomial
	 */
	public PolynomialConst(Integer v) {
		this.value = v;
		this.id = ID++;
	}

	
	/**
	 * Returns the identifier of this constant polynomial.
	 * 
	 * @return the identifier of this constant polynomial
	 */
	public int getID() {
		return this.id;
	}
	
	/**
	 * Returns the value of this polynomial if it is defined,
	 * or <code>null</code> otherwise.
	 * 
	 * @return the value of this polynomial if it is defined,
	 * or <code>null</code> otherwise
	 */
	public Integer getValue() {
		return this.value;
	}

	/**
	 * Sets the value of this polynomial to the
	 * specified value.
	 * 
	 * @param i the new value of this polynomial
	 */
	public void setValue(Integer i) {
		this.value = i;
	}

	/**
	 * Increments the value of this polynomial
	 * by 1. If the value of this polynomial is
	 * undefined, then does nothing.
	 */
	public void incValue() {
		if (this.value != null)
			this.value++;
	}

	/**
	 * Computes the partial derivative of this polynomial
	 * with respect to the given variable. Always returns
	 * 0 as this polynomial is constant.
	 * 
	 * @param v a variable for computing the partial derivative
	 * of this polynomial
	 * @return 0
	 */
	@Override
	public Polynomial partialDerivative(Variable v) {
		return PolynomialConst.ZERO;
	}

	/**
	 * Returns the polynomial resulting from replacing, in this 
	 * polynomial, all the variables of <code>L</code> with
	 * <code>mu</code>. As this polynomial does not contain
	 * any variable, this method always returns this polynomial.
	 * 
	 * @param L a list of variables to be replaced with
	 * <code>mu</code>
	 * @param mu the variable used in [Giesl, RTA'95] for
	 * solving polynomial constraints
	 * @return this polynomial
	 */
	@Override
	public Polynomial replaceWithMu(Deque<Variable> L, PolynomialConst mu) {
		return this;
	}

	/**
	 * Returns the value of this <code>polynomial</code> as an
	 * <code>Integer</code>. Same as method <code>getValue</code>.
	 * 
	 * @param I an interpretation of the variables of
	 * this polynomial
	 * @return the value of this <code>polynomial</code> as
	 * an <code>Integer</code>
	 */
	@Override
	public Integer integerValue(Map<Variable,Integer> I) {
		return this.value;
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
	 * @param V a variable
	 * @return <code>false</code>, always, as any constant
	 * polynomial does not contain any variable
	 */
	@Override
	public boolean contains(Variable V) {
		return false;
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
		LinkedList<Polynomial> L = new LinkedList<Polynomial>();
		L.add(this);

		return L;
	}

	/**
	 * Tries to check whether <code>P &ge; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * 
	 * If <code>true</code> is returned, then it is sure
	 * that <code>P &ge; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is sure that
	 * <code>P &ge; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean gez() {
		// If this.value == null, then this object
		// is a constant polynomial that will be
		// instantiated with a non-negative integer.
		return this.value == null || this.value >= 0;
	}
	
	/**
	 * Tries to check whether <code>P &gt; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * 
	 * If <code>true</code> is returned, then it is sure
	 * that <code>P &gt; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is sure that
	 * <code>P &gt; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean gtz() {
		return this.value != null && this.value > 0;
	}
	
	/**
	 * Tries to check whether <code>P &le; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * 
	 * If <code>true</code> is returned, then it is sure
	 * that <code>P &le; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is sure that
	 * <code>P &le; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean lez() {
		return this.value != null && this.value <= 0;
	}
	
	/**
	 * Tries to check whether <code>P &lt; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * 
	 * If <code>true</code> is returned, then it is sure
	 * that <code>P &lt; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is sure that
	 * <code>P &lt; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean ltz() {
		return this.value != null && this.value < 0;
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
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of this polynomial
	 */
	@Override
	public String toString(Map<Variable,String> variables) {
		return this.toString();
	}

	/**
	 * Returns a string representation of this polynomial.
	 * 
	 * @return a string representation of this polynomial
	 */
	@Override
	public String toString() {
		// return (this.value == null ? "C_@" + Integer.toHexString(this.hashCode()) : this.value.toString());
		// return "C" + this.id + "=" + (this.value == null ? "?" : this.value);
		return (this.value == null ? "C" + this.id : this.value.toString());
	}
}
