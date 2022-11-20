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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.term.Variable;

/**
 * A composed polynomial i.e., a polynomial
 * which results from adding of multiplying
 * two polynomials.
 * 
 * An object of this class is immutable.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PolynomialComp implements Polynomial {

	/**
	 * The root arithmetic operator of this polynomial.
	 * 
	 * As the arity of every arithmetic operator is equal
	 * to 2, this polynomial has a left operand and a right
	 * operand.  
	 */
	private final ArithOperator rootOperator;

	/**
	 * The left operand of this polynomial.
	 */
	private final Polynomial left;

	/**
	 * The right operand of this polynomial.
	 */
	private final Polynomial right;

	/**
	 * Static factory method. Builds a polynomial 
	 * from the specified operator and operands.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * the polynomial
	 * @param left the left operand of the root operator
	 * of the polynomial
	 * @param right the right operand of the root operator
	 * of the polynomial
	 * @return a polynomial constructed from the given
	 * operator and operands
	 */
	public synchronized static Polynomial getInstance(ArithOperator rootOperator,
			Polynomial left, Polynomial right) {

		return new PolynomialComp(rootOperator, left, right).simplify();
	}

	/**
	 * Static factory method. Builds a polynomial 
	 * from the specified operator and operands.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * the polynomial
	 * @param operands the operands of the root operator
	 * of the polynomial
	 * @return a polynomial constructed from the given
	 * operator and operands
	 */
	public synchronized static Polynomial getInstance(ArithOperator rootOperator,
			List<Polynomial> operands) {

		if (operands == null || operands.size() == 0)
			throw new IllegalArgumentException();

		return getInstanceAux(rootOperator, operands, operands.iterator());
	}

	/**
	 * Static factory method. Builds a polynomial 
	 * from the specified operator and operands,
	 * starting from the operand at the specified
	 * index.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * the polynomial
	 * @param operands the operands of the root operator
	 * of the polynomial
	 * @param i an index in the specified operand arrays
	 * @return a polynomial constructed from the given
	 * operator and operands
	 */
	private synchronized static Polynomial getInstanceAux(ArithOperator rootOperator,
			List<Polynomial> operands, Iterator<Polynomial> it) {

		// Here, we know that 'it' has a next element because
		// it is the case when this method is called for the
		// first time in 'getInstance' and it is also the case
		// when this method is recursively called below.

		Polynomial P = it.next();

		if (it.hasNext())
			return getInstance(rootOperator, P,
					getInstanceAux(rootOperator, operands, it));

		return P;
	}

	/**
	 * Builds a polynomial.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * this polynomial
	 * @param left the left operand of this polynomial
	 * @param right the right operand of this polynomial
	 */
	private PolynomialComp(ArithOperator rootOperator, Polynomial left, Polynomial right) {
		this.rootOperator = rootOperator;
		this.left = left;
		this.right = right;
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

		// If both operands of this polynomial are constant polynomials,
		// then this polynomial is a constant polynomial and its partial
		// derivative is 0.
		if (this.left instanceof PolynomialConst && this.right instanceof PolynomialConst)
			return PolynomialConst.ZERO;

		// From here, at least one of the operands of this polynomial
		// is not a constant polynomial.

		if (this.rootOperator == ArithOperator.TIMES) {
			if (this.left instanceof PolynomialConst)
				return PolynomialComp.getInstance(ArithOperator.TIMES,
						this.left, this.right.partialDerivative(v));
			if (this.right instanceof PolynomialConst)
				return PolynomialComp.getInstance(ArithOperator.TIMES,
						this.left.partialDerivative(v), this.right);
			return PolynomialComp.getInstance(ArithOperator.PLUS,
					PolynomialComp.getInstance(ArithOperator.TIMES, this.left.partialDerivative(v), this.right),
					PolynomialComp.getInstance(ArithOperator.TIMES, this.left, this.right.partialDerivative(v)));
		}

		// Here, the root operator of this polynomial is + or -.
		if (this.rootOperator == ArithOperator.PLUS && this.left instanceof PolynomialConst)
			return this.right.partialDerivative(v);
		if (this.right instanceof PolynomialConst)
			return this.left.partialDerivative(v);
		return PolynomialComp.getInstance(this.rootOperator,
				this.left.partialDerivative(v),
				this.right.partialDerivative(v));
	}

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
	@Override
	public Polynomial replaceWithMu(Deque<Variable> L, PolynomialConst mu) {
		return new PolynomialComp(this.rootOperator,
				this.left.replaceWithMu(L, mu),
				this.right.replaceWithMu(L, mu));
	}

	/**
	 * Returns the value of this <code>polynomial</code> as
	 * an <code>Integer</code>.
	 * 
	 * @param I an interpretation of the variables of
	 * this polynomial
	 * @return the value of this <code>polynomial</code> as
	 * an <code>Integer</code>
	 */
	@Override
	public Integer integerValue(Map<Variable,Integer> I) {
		Integer iLeft = this.left.integerValue(I);
		if (iLeft == null)
			return null;

		Integer iRight = this.right.integerValue(I);
		if (iRight == null)
			return null;

		if (this.rootOperator == ArithOperator.MINUS)
			return iLeft - iRight;
		else if (this.rootOperator == ArithOperator.PLUS)
			return iLeft + iRight;
		return iLeft * iRight;
	}

	/**
	 * Simplifies this polynomial using the current
	 * values of its coefficients.
	 * 
	 * @return a simplified version of this polynomial,
	 * which takes into account the current value of
	 * its coefficients
	 */
	@Override
	public Polynomial simplify() {
		// If this polynomial has an integer value
		// then we return this value.
		Integer i  = this.integerValue(null);
		if (i != null)
			return new PolynomialConst(i);

		// Otherwise, we simplify its left and right operands.
		Polynomial simplifiedLeft  = this.left.simplify();
		Polynomial simplifiedRight = this.right.simplify();

		if (this.rootOperator == ArithOperator.TIMES) {				
			Integer iLeft = simplifiedLeft.integerValue(null);
			if (iLeft != null) {
				if (iLeft == 0)
					return PolynomialConst.ZERO;
				if (iLeft == 1)
					return simplifiedRight;
			}
			Integer iRight = simplifiedRight.integerValue(null);
			if (iRight != null) {
				if (iRight == 0)
					return PolynomialConst.ZERO;
				if (iRight == 1)
					return simplifiedLeft;
			}
		}
		else if (this.rootOperator == ArithOperator.PLUS) {
			Integer iLeft = simplifiedLeft.integerValue(null);
			if (iLeft != null && iLeft == 0)
				return simplifiedRight;
			Integer iRight = simplifiedRight.integerValue(null);
			if (iRight != null && iRight == 0)
				return simplifiedLeft;
		}
		else {
			// Here, the operator is MINUS.
			Integer iRight = simplifiedRight.integerValue(null);
			if (iRight != null && iRight == 0)
				return simplifiedLeft;
		}

		return new PolynomialComp(this.rootOperator, simplifiedLeft, simplifiedRight);
	}

	/**
	 * Checks whether this polynomial contains the given
	 * variable.
	 * 
	 * @param V a variable
	 * @return <code>true</code> iff this polynomial
	 * contains <code>V</code>
	 */
	@Override
	public boolean contains(Variable V) {
		return this.left.contains(V) || this.right.contains(V);
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
		// The list to return at the end
		LinkedList<Polynomial> L = new LinkedList<Polynomial>();

		if (this.rootOperator == ArithOperator.PLUS || this.rootOperator == ArithOperator.MINUS) {
			L.addAll(this.left.getMonomials());
			L.addAll(this.right.getMonomials());
		}
		else
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
		// Given the way we build constraints, this polynomial
		// has the form P1 op P2 where op is its root operator
		// and the minus operator does not occur in P1 and P2.
		// Hence, as constant polynomials are instantiated with
		// non-negative integers, we necessarily have P1 >= 0 and
		// P2 >= 0.

		// We check whether this polynomial has the form
		// P1 + P2 or P1 - P1 or P1 x P2.
		return (this.left == this.right) ||
				(this.rootOperator != ArithOperator.MINUS);
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
		// We do not know.
		return false;
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
		// Given the way we build constraints, this polynomial
		// has the form P1 op P2 where op is its root operator
		// and the minus operator does not occur in P1 and P2.
		// Hence, as constant polynomials are instantiated with
		// non-negative integers, we necessarily have P1 >= 0 and
		// P2 >= 0.

		if (this.rootOperator == ArithOperator.MINUS)
			// If op is the minus operator, then we check whether
			// P1 = P2 (i.e., this polynomial has the form P1 - P1)
			// or whether P1 = 0 (i.e., this polynomial has the form
			// 0 - P2).
			return (this.left == this.right) ||
					(this.left == PolynomialConst.ZERO);

		// From here, op is not the minus operator, i.e., this
		// polynomial has the form P1 + P2 or P1 x P2 with
		// P1 >= 0 and P2 >= 0. Hence, we do not know.

		return false;
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
		// We do not know.
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

		if (this.rootOperator == ArithOperator.MINUS &&
				this.left instanceof PolynomialConst && 
				this.right instanceof PolynomialConst)
			
			return new PolynomialConst[] {
					(PolynomialConst) this.left,
					(PolynomialConst) this.right };

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
		// Parentheses around the left operand.
		String par1 = "", par2 = "";
		// Parentheses around the right operand.
		String par3 = "", par4 = "";

		if (this.rootOperator == ArithOperator.TIMES) {
			if (this.left instanceof PolynomialComp) {
				PolynomialComp left_Comp = (PolynomialComp) this.left;
				if (left_Comp.rootOperator != ArithOperator.TIMES) {
					par1 = "(";
					par2 = ")";
				}
			}
			if (this.right instanceof PolynomialComp) {
				PolynomialComp right_Comp = (PolynomialComp) this.right;
				if (right_Comp.rootOperator != ArithOperator.TIMES) {
					par3 = "(";
					par4 = ")";
				}
			}
		}

		if (this.rootOperator == ArithOperator.MINUS && (this.right instanceof PolynomialComp)) {
			PolynomialComp right_Comp = (PolynomialComp) this.right;
			if (right_Comp.rootOperator != ArithOperator.TIMES) {
				par3 = "(";
				par4 = ")";
			}
		}

		return par1 + this.left.toString(variables) + par2 +
				" " + this.rootOperator + " " +
				par3 + this.right.toString(variables) + par4;	
	}

	/**
	 * Returns a string representation of this polynomial.
	 * 
	 * @return a string representation of this polynomial
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<Variable,String>());
	}
}
