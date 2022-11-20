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
 * 
 * Used in the left-unification decision procedure
 * (Algorithms A-1 & A-2, Kapur et al., TCS 1991).
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LuEquation {

	/**
	 * A global value which is used for stopping
	 * the left-unification decision procedure.
	 * 
	 * It is automatically incremented each time
	 * a new equation is built.
	 */
	private static int currentTime = 0;

	/**
	 * Returns the value of the current time.
	 * 
	 * @return the value of the current time
	 */
	public synchronized static int getCurrentTime() {
		return currentTime;
	}
	
	/**
	 * Increments the current time.
	 */
	protected synchronized static void incCurrentTime() {
		currentTime++;
	}

	/**
	 * Set the current time to 0.
	 */
	public synchronized static void resetTime() {
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
	 * 
	 * Used for orienting equations in the 
	 * left-unification decision procedure.
	 * 
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
	private synchronized static boolean smallerThan(Term s, Term t) {
		if (s instanceof Variable) {
			if (t instanceof Variable) {
				int rho_s = 0;
				Variable X_s = (Variable) s;

				int rho_t = 0;
				Variable X_t = (Variable) t;

				if (s instanceof LuVariable) {
					LuVariable V = (LuVariable) s;
					rho_s = V.getRho();
					X_s = V.getVariable();
				}
				if (t instanceof LuVariable) {
					LuVariable V = (LuVariable) t;
					rho_t = V.getRho();
					X_t = V.getVariable();
				}

				return (X_s == X_t && rho_s <= rho_t) ||
						X_s.hashCode() < X_t.hashCode();		
			}

			return false;
		}

		return true;
	}

	/**
	 * Builds an equation and increments the
	 * current time.
	 * 
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
	 * Applies the distributivity and cancellativity
	 * rules to this equation and returns the resulting
	 * list of equations. If a root conflict or an
	 * equation of the form rho^i(x) = f(...rho^(i+j)(x)...)
	 * occurs, then <code>null</code> is returned.
	 * 
	 * The substitution rho is supposed to be already
	 * distributed through this equation.
	 * 
	 * @return the list of equations resulting from
	 * applying the distributivity and cancellativity
	 * rules to this equation, or <code>null</code>
	 * if a problem occurs
	 */
	public List<LuEquation> distributeAndCancel() {
		// The list to return at the end.
		List<LuEquation> L = null;

		if (this.left == this.right) {
			// In such a situation, we return
			// an empty list, meaning that we
			// remove this equation.
			L = new LinkedList<LuEquation>();
		}

		else if ((this.left instanceof Function) && (this.right instanceof Function)) {
			Function f_left  = (Function) this.left;
			Function f_right = (Function) this.right;
			FunctionSymbol f = f_left.getRootSymbol();
			if (f == f_right.getRootSymbol()) {
				L = new LinkedList<LuEquation>();
				int arity = f.getArity();
				for (int i = 0; i < arity; i++) {
					Term l_i = f_left.getChild(i);
					Term r_i = f_right.getChild(i);
					// Check whether an equation of the form
					// rho^i(x) = f(...rho^(i+j)(x)...) occurs.
					if ((l_i instanceof Variable) &&
							!(r_i instanceof Variable) &&
							r_i.contains((Variable) l_i))
						return null;
					if ((r_i instanceof Variable) &&
							!(l_i instanceof Variable) &&
							l_i.contains((Variable) r_i))
						return null;
					// No problem occurs, hence recursively
					// call this method on the new equation.
					List<LuEquation> L_i = (new LuEquation(l_i, r_i)).distributeAndCancel();
					if (L_i == null) return null;
					L.addAll(L_i);
				}
			}
		}

		else if (this.right instanceof Variable) {
			// As this equation is oriented, if right is
			// a variable then so is left, necessarily.
			Variable V_left  = (Variable) this.left;
			Variable V_right = (Variable) this.right;

			L = new LinkedList<LuEquation>();

			// If V_left and V_right are the same variable,
			// we return an empty list, meaning that we
			// remove this equation. Otherwise, we keep
			// this equation.
			if (!V_left.sameAs(V_right)) L.add(this);
		}

		else if (!right.contains((Variable) left)) {
			// Here, left is a variable and right is not.
			// Hence, we have to check whether this equation
			// has the form rho^i(x) = f(...rho^(i+j)(x)...).
			L = new LinkedList<LuEquation>();
			L.add(this);
		}

		return L;
	}

	/**
	 * Reduces this equation in place with the provided
	 * equation (all the occurrences of the left-hand
	 * side of the provided equation are replaced with
	 * its right-hand side).
	 * 
	 * Both this equation and the provided one are
	 * supposed to be in normal form: the substitution
	 * rho is distributed through both of them and their
	 * left-hand side either is a variable or has the
	 * form rho^i(a variable).
	 * 
	 * This equation is also in normal form after being
	 * reduced by this method.
	 * 
	 * If this equation has changed after its reduction
	 * then the current time is incremented.
	 * 
	 * @param E an oriented equation
	 */
	public void reduceWith(LuEquation E) {
		Term l  = this.left.reduceWith(E);		
		Term r = this.right.reduceWith(E);
		
		if (this.left.hasChanged() || this.right.hasChanged())
			LuEquation.incCurrentTime();
		
		if (smallerThan(r, l)) {
			this.left = l;
			this.right = r;
		}
		else {
			this.left = r;
			this.right = l;
		}
	}

	/**
	 * Returns a string representation of this equation
	 * relatively to the given set of variable symbols.
	 * 
	 * @return a string representation of this equation
	 */
	public String toString(Map<Variable,String> variables) {
		return this.left.toString(variables, false) +
				" = " + 
				this.right.toString(variables, false);
	}
}
