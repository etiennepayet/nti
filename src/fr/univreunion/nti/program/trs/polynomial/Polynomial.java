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
import java.util.Map;

import fr.univreunion.nti.term.Variable;

/**
 * A polynomial.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public interface Polynomial {
		
	/**
	 * Computes the partial derivative of this polynomial
	 * with respect to the given variable.
	 * 
	 * @param v a variable for computing the partial derivative
	 * of this polynomial
	 * @return the partial derivative of this polynomial
	 * with respect to the given variable
	 */
	public Polynomial partialDerivative(Variable v);
	
	/**
	 * Returns the polynomial resulting from replacing, in this 
	 * polynomial, all the variables of <code>L</code> with
	 * <code>mu</code>.
	 * 
	 * @param L a list of variables to be replaced with
	 * <code>mu</code>
	 * @param mu the variable used in [Giesl, RTA'95] for
	 * solving polynomial constraints
	 * @return the polynomial resulting from replacing all
	 * the variables of <code>L</code> with <code>mu</code>
	 */
	public Polynomial replaceWithMu(Deque<Variable> L, PolynomialConst mu);
	
	/**
	 * Returns the value of this <code>polynomial</code> as
	 * an <code>Integer</code>.
	 * 
	 * @param I an interpretation of the variables of
	 * this polynomial
	 * @return the value of this <code>polynomial</code> as
	 * an <code>Integer</code>
	 */
	public Integer integerValue(Map<Variable,Integer> I);
	
	/**
	 * Simplifies this polynomial using the current
	 * values of its coefficients.
	 * 
	 * @return a simplified version of this polynomial,
	 * which takes into account the current value of
	 * its coefficients
	 */
	public Polynomial simplify();
	
	/**
	 * Checks whether this polynomial contains the given
	 * variable.
	 * 
	 * @param V a variable
	 * @return <code>true</code> iff this polynomial
	 * contains <code>V</code>
	 */
	public boolean contains(Variable V);
	
	/**
	 * Returns a collection consisting of the monomials
	 * of this polynomial.
	 * 
	 * @return a collection consisting of the monomials
	 * of this polynomial
	 */
	public Collection<Polynomial> getMonomials();
	
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
	public boolean gez();
	
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
	public boolean gtz();
	
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
	public boolean lez();
	
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
	public boolean ltz();
	
	/**
	 * If this polynomial is the subtraction of two
	 * constant polynomials, then returns an array
	 * containing these two constant polynomials.
	 * Otherwise, returns <code>null</code>.
	 * 
	 * @return an array containing two constant
	 * polynomials, or <code>null</code>
	 */
	public PolynomialConst[] subOperands();
	
	/**
	 * Returns a string representation of this polynomial
	 * relatively to the given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of this polynomial
	 */
	public String toString(Map<Variable,String> variables);
}
