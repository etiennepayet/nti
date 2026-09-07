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

package fr.univreunion.nti.term.leftunif;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An equation between two terms.
 * <p>
 * Used in the left-unification decision procedure
 * (Algorithms A-1 &amp; A-2) of D. Kapur, D. R. Musser, P. Narendran,
 * and J. Stillman,
 * <a href="https://doi.org/10.1016/0304-3975(91)90189-9">Semi-Unification</a>,
 * Theoretical Computer Science 81(2), 169--187, 1991.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LuEquation {

	/**
	 * A global value which is used for stopping
	 * the left-unification decision procedure.
	 * <p>
	 * It is automatically incremented each time
	 * a new equation is built.
	 */
	private static int currentTime = 0;

	/**
	 * Returns the value of the current time.
	 *
	 * @return the value of the current time
	 */
	public static synchronized int getCurrentTime() {
		return currentTime;
	}

	/**
	 * Increments the current time.
	 */
	protected static synchronized void incCurrentTime() {
		currentTime++;
	}

	/**
	 * Set the current time to 0.
	 */
	public static synchronized void resetTime() {
		currentTime = 0;
	}

	/**
	 * The left-hand side of the equation.
	 * The substitution rho is supposed to
	 * be already distributed through this
	 * term.
	 */
	private Term left;

	/**
	 * The right-hand side of the equation.
	 * The substitution rho is supposed to
	 * be already distributed through this
	 * term.
	 */
	private Term right;

	/**
	 * Returns <code>true</code> iff term
	 * <code>s</code> is smaller than term
	 * <code>t</code>.
	 * <p>
	 * Used for orienting equations in the
	 * left-unification decision procedure.
	 * <p>
	 * A variable is never smaller than a term which
	 * is not a variable. Moreover, for two variables
	 * we have: rho^i(X) < rho^j(Y) iff
	 * hashCode(X) < hashCode(Y) or (X = Y and i < j).
	 *
	 * @param s a term
	 * @param t a term
	 * @return <code>true</code> iff <code>s</code>
	 * is smaller than <code>t</code>
	 */
	private static synchronized boolean smallerThan(Term s, Term t) {
		if (!(s instanceof Variable leftVariable))
			return true;

		if (!(t instanceof Variable rightVariable))
			return false;

		int leftRho = 0;

		int rightRho = 0;

		if (s instanceof LuVariable luVariable) {
			leftRho = luVariable.getRho();
			leftVariable = luVariable.getVariable();
		}
		if (t instanceof LuVariable luVariable) {
			rightRho = luVariable.getRho();
			rightVariable = luVariable.getVariable();
		}

		return (leftVariable == rightVariable && leftRho <= rightRho) ||
				leftVariable.hashCode() < rightVariable.hashCode();
	}

	/**
	 * Builds an equation and increments the
	 * current time.
	 * <p>
	 * The substitution rho is supposed to be
	 * already distributed through the specified
	 * left-hand and right-hand sides.
	 *
	 * @param left the left-hand side of the
	 * equation
	 * @param right the right-hand side of the
	 * equation
	 */
	public LuEquation(Term left, Term right) {
		// rho is supposed to be already distributed
		// through left and right.

		// We orient the equation in order to
		// obtain a rewrite rule.
		if (smallerThan(right, left)) {
			this.left = left;
			this.right = right;
		}
		else {
			this.left = right;
			this.right = left;
		}

		LuEquation.incCurrentTime();
	}

	/**
	 * Returns the left-hand side of this equation.
	 *
	 * @return the left-hand side of this equation
	 */
	public Term getLeft() {
		return this.left;
	}

	/**
	 * Returns the right-hand side of this equation.
	 *
	 * @return the right-hand side of this equation
	 */
	public Term getRight() {
		return this.right;
	}

	/**
	 * Applies the distributivity and cancellation
	 * rules to this equation and returns the resulting
	 * list of equations. If a root conflict or an
	 * equation of the form rho^i(x) = f(...rho^(i+j)(x)...)
	 * occurs, then <code>null</code> is returned.
	 * <p>
	 * The substitution rho is supposed to be already
	 * distributed through this equation.
	 *
	 * @return the list of equations resulting from
	 * applying the distributivity and cancellation
	 * rules to this equation, or <code>null</code>
	 * if a problem occurs
	 */
	public List<LuEquation> distributeAndCancel() {
		if (this.left == this.right) {
			// In such a situation, we return
			// an empty list, meaning that we
			// remove this equation.
			return new LinkedList<>();
		}

		if ((this.left instanceof Function leftFunction) && (this.right instanceof Function rightFunction)) {
			return distributeAndCancelFunctions(leftFunction, rightFunction);
		}

		if (this.right instanceof Variable rightVariable) {
			// As this equation is oriented, if right is
			// a variable then so is left, necessarily.
			Variable leftVariable = (Variable) this.left;

			List<LuEquation> equations = new LinkedList<>();

			// If leftVariable and rightVariable are the same variable,
			// we return an empty list, meaning that we
			// remove this equation. Otherwise, we keep
			// this equation.
			if (!leftVariable.sameAs(rightVariable))
				equations.add(this);
			return equations;
		}

		if (!right.contains(left)) {
			// Here, left is a variable and right is not.
			// Hence, we have to check whether this equation
			// has the form rho^i(x) = f(...rho^(i+j)(x)...).
			List<LuEquation> equations = new LinkedList<>();
			equations.add(this);
			return equations;
		}

		return null;
	}

	/**
	 * Applies the distributivity and cancellation rules
	 * to an equation between two function terms.
	 *
	 * @param leftFunction the left-hand side function
	 * @param rightFunction the right-hand side function
	 * @return the list of resulting equations, or <code>null</code>
	 * if a problem occurs
	 */
	private List<LuEquation> distributeAndCancelFunctions(
			Function leftFunction, Function rightFunction) {

		FunctionSymbol f = leftFunction.getRootSymbol();
		if (f != rightFunction.getRootSymbol())
			return null;

		List<LuEquation> equations = new LinkedList<>();
		int arity = f.getArity();
		for (int i = 0; i < arity; i++) {
			Term leftChild = leftFunction.getChild(i);
			Term rightChild = rightFunction.getChild(i);
			// Check whether an equation of the form
			// rho^i(x) = f(...rho^(i+j)(x)...) occurs.
			if (hasVariableAgainstContainingTerm(leftChild, rightChild))
				return null;
			// No problem occurs, hence recursively
			// call this method on the new equation.
			List<LuEquation> childEquations = (new LuEquation(leftChild, rightChild)).distributeAndCancel();
			if (childEquations == null)
				return null;
			equations.addAll(childEquations);
		}
		return equations;
	}

	/**
	 * Returns <code>true</code> iff an equation between
	 * the given terms has the form
	 * rho^i(x) = f(...rho^(i+j)(x)...).
	 *
	 * @param left a term
	 * @param right a term
	 * @return <code>true</code> iff one side is a variable
	 * contained in the other, non-variable side
	 */
	private static boolean hasVariableAgainstContainingTerm(Term left, Term right) {
		return (left instanceof Variable &&
				!(right instanceof Variable) &&
				right.contains(left)) ||
				(right instanceof Variable &&
						!(left instanceof Variable) &&
						left.contains(right));
	}

	/**
	 * Reduces this equation in place with the provided
	 * equation (all the occurrences of the left-hand
	 * side of the provided equation are replaced with
	 * its right-hand side).
	 * <p>
	 * Both this equation and the provided one are
	 * supposed to be in normal form: the substitution
	 * rho is distributed through both of them and their
	 * left-hand side either is a variable or has the
	 * form rho^i(a variable).
	 * <p>
	 * This equation is also in normal form after being
	 * reduced by this method.
	 * <p>
	 * If this equation has changed after its reduction
	 * then the current time is incremented.
	 *
	 * @param equation an oriented equation
	 */
	public void reduceWith(LuEquation equation) {
		Term reducedLeft = this.left.reduceWithLeftUnificationRule(equation);
		Term reducedRight = this.right.reduceWithLeftUnificationRule(equation);

		if (this.left.hasChanged() || this.right.hasChanged())
			LuEquation.incCurrentTime();

		if (smallerThan(reducedRight, reducedLeft)) {
			this.left = reducedLeft;
			this.right = reducedRight;
		}
		else {
			this.left = reducedRight;
			this.right = reducedLeft;
		}
	}

	/**
	 * Returns a string representation of this equation
	 * relatively to the given set of variable symbols.
	 *
	 * @return a string representation of this equation
	 */
	public String toString(Map<Variable, String> variables) {
		return this.left.toString(variables, false) +
				" = " +
				this.right.toString(variables, false);
	}
}
