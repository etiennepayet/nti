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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.term.leftunif;

import java.util.Map;

import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A variable used in the left-unification decision
 * procedure (Algorithm A-1, Kapur et al., TCS 1991).
 * 
 * It has the form rho^i(X) where X is a standard
 * variable.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LuVariable extends Variable {

	/**
	 * The variable which is embedded in
	 * this LUVariable.
	 */
	private Variable X;

	/**
	 * The number of applications of rho
	 * to the variable which is embedded in
	 * this LUVariable.
	 */
	protected int rho;

	/**
	 * Builds a LUVariable.
	 * 
	 * @param X the variable which is embedded in
	 * this LUVariable
	 * @param rho the number of applications of rho
	 * to the variable which is embedded in
	 * this LUVariable
	 */
	public LuVariable(Variable X, int rho) {
		this.X = X;
		this.rho = rho;
	}

	/**
	 * Returns the number of applications of
	 * rho to the variable which is embedded
	 * in this object.
	 * 
	 * @return the number of applications of
	 * rho to the variable which is embedded
	 * in this object
	 */
	public int getRho() {
		return this.rho;
	}

	/**
	 * Returns the variable which is embedded
	 * in this object.
	 * 
	 * @return the variable which is embedded
	 * in this object
	 */
	public Variable getVariable() {
		return this.X;
	}

	/**
	 * Returns <code>true</code> iff this variable
	 * is the same as the provided one.
	 * 
	 * @param V a variable
	 * @return <code>true</code> iff this variable
	 * is the same as the provided one
	 */
	public boolean sameAs(Variable V) {
		if (V instanceof LuVariable) {
			LuVariable X = (LuVariable) V;
			return (X.getRho() == this.rho) && (X.getVariable() == this.X);
		}

		// Here, V is a standard variable.
		return (this.rho == 0) && (V == this.X);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return a shallow copy of this term
	 */
	@Override
	public Term shallowCopyAux() {
		return new LuVariable(this.X, this.rho);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains the given
	 * term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Moreover, it is supposed
	 * that <code>this != t</code>.
	 * 
	 * @param t a term whose presence in this term
	 * is to be tested
	 * @return <code>true</code> iff this term
	 * contains <code>t</code>
	 */
	@Override
	protected boolean containsAux(Term t) {
		if (t instanceof LuVariable) {
			LuVariable X = (LuVariable) t;
			return (X.getRho() <= this.rho) && (X.getVariable() == this.X);
		}

		if (t instanceof Variable)
			// Here, t is a standard variable.
			return t == this.X;
		
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0. As this term is an
	 * instance of <code>LUVariable</code>, this
	 * method just checks its rho component.
	 * 
	 * Used in the implementation of step 3 of
	 * Alg. A-2.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	@Override
	protected boolean containsRhoAux() {
		return 0 < this.rho;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for applying the distributivity rule to this
	 * term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. It is not modified by
	 * this method.
	 * 
	 * Used in the left-unification decision procedure.
	 * 
	 * @param rho the number of applications of rho
	 * to this term
	 * @return the resulting term
	 */
	@Override
	protected Term distributeAux(int rho) {
		return new LuVariable(this.X, this.rho + rho);
	}

	/**
	 * An auxiliary, internal method, which is used
	 * for reducing this term by a single step of rewriting
	 * using the provided rule (specified as an oriented
	 * equation). The resulting term may be this term
	 * modified in place, or a new term.
	 * 
	 * If something has changed after reduction
	 * (meaning that this term is reducible with
	 * the provided rule) then the <code>changed</code>
	 * flag of this term is set to <code>true</code>
	 * (can be checked using method <code>hasChanged</code>).
	 * 
	 * The provided equation is supposed to be in normal
	 * form: the substitution rho is distributed through
	 * it and its left-hand side either is a variable or
	 * has the form rho^i(a variable).
	 * 
	 * It is supposed that the substitution rho is
	 * already distributed through this term before
	 * it is reduced. It is also distributed after the
	 * reduction.
	 * 
	 * It is supposed that the <code>changed</code>
	 * flag of this term is set to <code>false</code>.
	 * 
	 * Used in the left-unification decision procedure.
	 * 
	 * @param E a rule (specified as an oriented
	 * equation)
	 * @return the resulting term
	 */
	@Override
	public Term reduceWithAux(LuEquation E) {
		// The value to return at the end.
		Term result = this;

		// It is supposed that the left-hand side
		// of E is an instance of Variable.
		Variable V = (Variable) E.getLeft();
		int rho_V = 0;

		if (V instanceof LuVariable) {
			LuVariable X = (LuVariable) V;
			rho_V = X.getRho();
			V = X.getVariable();
		}

		if (rho_V <= this.rho && V == this.X) {
			this.changed = true;
			int n = this.rho - rho_V;
			result = E.getRight().distribute(n);
		}

		return result;
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term may be this
	 * term or a new term.
	 * 
	 * Used in the implementation of step 2 of
	 * Alg. A-2.
	 * 
	 * @param rho a substitution to apply to, and
	 * complete from, this term
	 * @return the term resulting from applying
	 * <code>rho</code> to this term
	 */
	@Override
	protected Term applyAndCompleteRho(Substitution rho) {
		// The term to return at the end.
		Term result = this;

		// At this step of Alg. A-2, only 0 < rho
		// is considered.
		if (0 < this.rho) {
			// At this step of Alg. A-2, rho only consists
			// of mappings of the form variable -> variable.

			Variable X = this.X;
			Variable U = (Variable) rho.get(X);
			int i = 1; // because U = rho(X)
			while (i < this.rho && U != null) {
				X = U;
				U = (Variable) rho.get(X);
				i++;
			}

			// If rho does not map this LUVariable
			// to anything, then create all the
			// necessary intermediate variables u_i.
			if (U == null)
				while (i < this.rho + 1) {
					U = new Variable();
					rho.addReplace(X, U);
					X = U;
					i++;
				}

			result = U;
		}

		return result;
	}

	/**
	 * Applies the specified rho to this term
	 * (which is supposed to be the left-hand
	 * side of an equation). The resulting term
	 * is this term (if rho does not include a
	 * mapping for this term) possibly modified
	 * in place or the term which rho maps to
	 * this term.
	 * 
	 * Used in the implementation of step 2 of
	 * Alg. A-2.
	 * 
	 * @param rho a substitution to apply to
	 * this term
	 * @return the term resulting from applying
	 * the specified substitution to this term
	 */
	@Override
	protected Term applyRho(Substitution rho) {
		// The term to return at the end.
		Term result = this;

		// At this step of Alg. A-2, only 0 < rho
		// is considered.
		if (0 < this.rho) {
			// At this step of Alg. A-2, rho only consists
			// of mappings of the form variable -> variable.

			Variable X = this.X;
			Variable U = (Variable) rho.get(X);
			int i = 1; // because U = rho(X)
			while (i < this.rho && U != null) {
				X = U;
				U = (Variable) rho.get(X);
				i++;
			}

			if (U == null) {
				this.X = X;
				this.rho -= (i - 1);
			}
			else result = U;
		}

		return result;
	}
	
	/**
	 * Completes <code>rho</code> from this term,
	 * which is supposed to be the left-hand side
	 * of an equation.
	 * 
	 * Used in the implementation of step 4 of
	 * Alg. A-2.
	 * 
	 * @param rho a substitution to complete from
	 * this term
	 * @param right the right-hand side of the
	 * equation whose left-hand side is this term
	 */
	@Override
	protected void completeRho(Substitution rho, Term right) {
		// At this step of Alg. A-2, only 0 < rho
		// is considered.
		if (0 < this.rho) {
			// At this step of Alg. A-2, rho only consists
			// of mappings of the form variable -> variable.

			Variable X = this.X;
			Variable U = (Variable) rho.get(X);
			int i = 1; // because U = rho(X)
			while (i < this.rho && U != null) {
				X = U;
				U = (Variable) rho.get(X);
				i++;
			}

			// Normally, rho does not map this LUVariable
			// to anything, hence we do not check whether
			// U is null (this should automatically be the
			// case). We create all the necessary intermediate
			// variables u_i and then we map the last u_i
			// to right.
			if (U == null)
				while (i < this.rho) {
					U = new Variable();
					rho.addReplace(X, U);
					X = U;
					i++;
				}
			
			rho.addReplace(X, right);
		}
	}

	/**
	 * Returns a string representation of this
	 * LUVariable term relatively to the given
	 * set of variable symbols.
	 * 
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * 
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 * Moreover, this term is supposed to be the schema of
	 * its class representative.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return a string representation of this LUVariable
	 */
	public String toString(Map<Variable,String> variables, boolean shallow) {
		String start = "rho^" + this.rho + "(";
		String Xstring = this.X.toString(variables, shallow);
		String end = ")";
		
		return  start + Xstring + end;
	}
}
