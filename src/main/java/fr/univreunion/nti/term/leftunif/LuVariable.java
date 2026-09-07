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

import java.util.Map;

import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A variable used in the left-unification decision
 * procedure (Algorithm A-1) of D. Kapur, D. R. Musser, P. Narendran,
 * and J. Stillman,
 * <a href="https://doi.org/10.1016/0304-3975(91)90189-9">Semi-Unification</a>,
 * Theoretical Computer Science 81(2), 169--187, 1991.
 * <p>
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
	private Variable embeddedVariable;

	/**
	 * The number of applications of rho
	 * to the variable which is embedded in
	 * this LUVariable.
	 */
	protected int rho;

	/**
	 * Builds a LUVariable.
	 *
	 * @param embeddedVariable the variable which is embedded in
	 * this LUVariable
	 * @param rho the number of applications of rho
	 * to the variable which is embedded in
	 * this LUVariable
	 */
	public LuVariable(Variable embeddedVariable, int rho) {
		this.embeddedVariable = embeddedVariable;
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
		return this.embeddedVariable;
	}

	/**
	 * Returns <code>true</code> iff this variable
	 * is the same as the provided one.
	 *
	 * @param variable a variable
	 * @return <code>true</code> iff this variable
	 * is the same as the provided one
	 */
	@Override
	public boolean sameAs(Variable variable) {
		if (variable instanceof LuVariable luVariable) {
			return (luVariable.getRho() == this.rho) &&
					(luVariable.getVariable() == this.embeddedVariable);
		}

		// Here, variable is a standard variable.
		return (this.rho == 0) && (variable == this.embeddedVariable);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return a shallow copy of this term
	 */
	@Override
	public Term shallowCopyAux() {
		return new LuVariable(this.embeddedVariable, this.rho);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains the given
	 * term.
	 * <p>
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
		if (t instanceof LuVariable luVariable) {
			return (luVariable.getRho() <= this.rho) &&
					(luVariable.getVariable() == this.embeddedVariable);
		}

		if (t instanceof Variable)
			// Here, t is a standard variable.
			return t == this.embeddedVariable;

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0. As this term is an
	 * instance of <code>LUVariable</code>, this
	 * method just checks its rho component.
	 * <p>
	 * Used in the implementation of step 3 of
	 * Alg. A-2.
	 * <p>
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
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative. It is not modified by
	 * this method.
	 * <p>
	 * Used in the left-unification decision procedure.
	 *
	 * @param rho the number of applications of rho
	 * to this term
	 * @return the resulting term
	 */
	@Override
	protected Term distributeAux(int rho) {
		return new LuVariable(this.embeddedVariable, this.rho + rho);
	}

	/**
	 * An auxiliary, internal method, which is used
	 * for reducing this term by a single step of rewriting
	 * using the provided rule (specified as an oriented
	 * equation). The resulting term may be this term
	 * modified in place, or a new term.
	 * <p>
	 * If something has changed after reduction
	 * (meaning that this term is reducible with
	 * the provided rule) then the <code>changed</code>
	 * flag of this term is set to <code>true</code>
	 * (can be checked using method <code>hasChanged</code>).
	 * <p>
	 * The provided equation is supposed to be in normal
	 * form: the substitution rho is distributed through
	 * it and its left-hand side either is a variable or
	 * has the form rho^i(a variable).
	 * <p>
	 * It is supposed that the substitution rho is
	 * already distributed through this term before
	 * it is reduced. It is also distributed after the
	 * reduction.
	 * <p>
	 * It is supposed that the <code>changed</code>
	 * flag of this term is set to <code>false</code>.
	 * <p>
	 * Used in the left-unification decision procedure.
	 *
	 * @param equation a rule (specified as an oriented
	 * equation)
	 * @return the resulting term
	 */
	@Override
	protected Term reduceWithLeftUnificationRuleAux(LuEquation equation) {
		// It is supposed that the left-hand side
		// of equation is an instance of Variable.
		Variable variable = (Variable) equation.getLeft();
		int variableRho = 0;

		if (variable instanceof LuVariable luVariable) {
			variableRho = luVariable.getRho();
			variable = luVariable.getVariable();
		}

		if (this.rho < variableRho || variable != this.embeddedVariable)
			return this;

		this.changed = true;
		int remainingRho = this.rho - variableRho;
		return equation.getRight().distribute(remainingRho);
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term may be this
	 * term or a new term.
	 * <p>
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
		// At this step of Alg. A-2, only 0 < rho
		// is considered.
		if (this.rho <= 0)
			return this;

		// At this step of Alg. A-2, rho only consists
		// of mappings of the form variable -> variable.

		Variable currentVariable = this.embeddedVariable;
		Variable rhoImage = (Variable) rho.get(currentVariable);
		int appliedRho = 1; // because rhoImage = rho(currentVariable)
		while (appliedRho < this.rho && rhoImage != null) {
			currentVariable = rhoImage;
			rhoImage = (Variable) rho.get(currentVariable);
			appliedRho++;
		}

		// If rho does not map this LUVariable
		// to anything, then create all the
		// necessary intermediate variables u_i.
		if (rhoImage == null)
			while (appliedRho < this.rho + 1) {
				rhoImage = new Variable();
				rho.addReplace(currentVariable, rhoImage);
				currentVariable = rhoImage;
				appliedRho++;
			}

		return rhoImage;
	}

	/**
	 * Applies the specified rho to this term
	 * (which is supposed to be the left-hand
	 * side of an equation). The resulting term
	 * is this term (if rho does not include a
	 * mapping for this term) possibly modified
	 * in place or the term which rho maps to
	 * this term.
	 * <p>
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
		// At this step of Alg. A-2, only 0 < rho
		// is considered.
		if (this.rho <= 0)
			return this;

		// At this step of Alg. A-2, rho only consists
		// of mappings of the form variable -> variable.

		Variable currentVariable = this.embeddedVariable;
		Variable rhoImage = (Variable) rho.get(currentVariable);
		int appliedRho = 1; // because rhoImage = rho(currentVariable)
		while (appliedRho < this.rho && rhoImage != null) {
			currentVariable = rhoImage;
			rhoImage = (Variable) rho.get(currentVariable);
			appliedRho++;
		}

		if (rhoImage != null)
			return rhoImage;

		this.embeddedVariable = currentVariable;
		this.rho -= (appliedRho - 1);
		return this;
	}

	/**
	 * Completes <code>rho</code> from this term,
	 * which is supposed to be the left-hand side
	 * of an equation.
	 * <p>
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
		if (this.rho <= 0)
			return;

		// At this step of Alg. A-2, rho only consists
		// of mappings of the form variable -> variable.

		Variable currentVariable = this.embeddedVariable;
		Variable rhoImage = (Variable) rho.get(currentVariable);
		int appliedRho = 1; // because rhoImage = rho(currentVariable)
		while (appliedRho < this.rho && rhoImage != null) {
			currentVariable = rhoImage;
			rhoImage = (Variable) rho.get(currentVariable);
			appliedRho++;
		}

		// Normally, rho does not map this LUVariable
		// to anything, hence we do not check whether
		// U is null (this should automatically be the
		// case). We create all the necessary intermediate
		// variables u_i, and then we map the last u_i
		// to right.
		if (rhoImage == null)
			while (appliedRho < this.rho) {
				rhoImage = new Variable();
				rho.addReplace(currentVariable, rhoImage);
				currentVariable = rhoImage;
				appliedRho++;
			}

		rho.addReplace(currentVariable, right);
	}

	/**
	 * Returns a string representation of this
	 * LUVariable term relatively to the given
	 * set of variable symbols.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * <p>
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
	@Override
	public String toString(Map<Variable,String> variables, boolean shallow) {
		String start = "rho^" + this.rho + "(";
		String variableString = this.embeddedVariable.toString(variables, shallow);
		String end = ")";

		return  start + variableString + end;
	}
}
