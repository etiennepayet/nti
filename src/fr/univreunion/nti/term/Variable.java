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

package fr.univreunion.nti.term;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.polynomial.Polynomial;
import fr.univreunion.nti.program.trs.polynomial.PolynomialVar;
import fr.univreunion.nti.program.trs.reducpair.LexOrder;
import fr.univreunion.nti.program.trs.reducpair.PolyInterpretation;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.leftunif.LuEquation;
import fr.univreunion.nti.term.leftunif.LuVariable;

/**
 * A variable.
 * 
 * An object of this class is mutable.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Variable extends Term {

	/**
	 * The root symbol for a variable.
	 * We insert a space in the symbol name
	 * in order to avoid interferences with
	 * any symbol in the analyzed program.
	 */
	public final static FunctionSymbol VARIABLE_ROOT_SYMBOL =
			FunctionSymbol.getInstance(" _", 0);

	/**
	 * Builds a variable.
	 */
	public Variable() {
		this.vars.add(this);
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * flatten this term i.e., make each of its subterms
	 * its own schema and the only element of its class.
	 */
	/*
	@Override
	protected void flattenAux() {
		this.vars.add(this);
	}
	 */

	/**
	 * Returns the root symbol of this term.
	 * 
	 * @return the root symbol of this term
	 */
	@Override
	public FunctionSymbol getRootSymbol() {
		return VARIABLE_ROOT_SYMBOL;
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether this term has the same structure as the specified
	 * term <code>t</code>. This term and <code>t</code> are
	 * not modified by this method.
	 * 
	 * This method implements a rough, but quickly computable,
	 * over-approximation of both the subsumption and the
	 * unification tests. It is essentially used for computing
	 * families (see method <code>getFamily</code> in class
	 * <code>FD_Graph</code>).
	 * 
	 * Both this term and the specified term are supposed to be
	 * the schemas of their respective class representatives.
	 * Moreover, it is supposed that <code>this != t</code>
	 * and that <code>t != null</code>.
	 * 
	 * Always returns <code>true</code>, as a variable has the
	 * same structure as any other term.
	 * 
	 * @param t the term whose structure has to be compared
	 * to that of this term
	 * @return <code>true</code>
	 */
	@Override
	protected boolean hasSameStructureAsAux(Term t) {
		return true;
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
			return (X.getRho() == 0) && (X.getVariable() == this);
		}

		// Here, V is a standard variable.
		return V == this;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether some other term is equal to
	 * this one.
	 * 
	 * This a deep, structural, comparison which is
	 * used in the implementation of substitutions.
	 * 
	 * Both this term and the provided term are
	 * supposed to be the representatives of their
	 * respective class. Moreover, it is supposed
	 * that <code>this != t</code>. Consequently,
	 * this method always returns <code>false</code>.
	 * 
	 * @param t the reference term with which to compare
	 * @return <code>false</code>
	 */
	@Override
	protected boolean deepEqualsAux(Term t) {
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Consequently, as this term
	 * is a variable, it is not copied, and this method
	 * simply returns this variable.
	 * 
	 * @return this variable
	 */
	@Override
	protected Term shallowCopyAux() {
		return this;
	}

	/**
	 * An auxiliary, internal, method which returns a
	 * deep copy of this term i.e., a copy where each
	 * subterm is also copied, except the variables
	 * not occurring in the specified collection.
	 * 
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied. 
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param varsToBeCopied a collection of variables
	 * that must be copied
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return a deep copy of this term
	 */
	@Override
	protected Term deepCopyAux(
			Collection<Variable> varsToBeCopied,
			Map<Term, Term> copies) {

		Term s = this;

		if (varsToBeCopied == null || varsToBeCopied.contains(this)) {
			s = copies.get(this);
			if (s == null) {
				s = new Variable();
				copies.put(this, s);
			}
		}

		return s;
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
			return (X.getRho() == 0) && (X.getVariable() == this);
		}

		// Here, as this != t, we return false.
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0.
	 * 
	 * Used in the implementation of step 3 of
	 * Alg. A-2.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * Always returns <code>false</code> as this method
	 * is overriden by class <code>LUVariable</code>.
	 * 
	 * @return <code>false</code>
	 */
	@Override
	protected boolean containsRhoAux() {
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * check whether this term is ground i.e., contains
	 * no variable.
	 * 
	 * This term is supposed to be the schema of its class
	 * representative. Hence, this method always returns
	 * <code>false</code> as such a term is not ground.
	 * 
	 * @return <code>false</code>
	 */
	@Override
	protected boolean isGroundAux() {
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of variables of this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Therefore, this method
	 * always returns a set consisting of this variable
	 * only.
	 * 
	 * @return a set consisting of this variable only
	 */
	@Override
	protected Set<Variable> getVariablesAux() {
		HashSet<Variable> Vars = new HashSet<Variable>();

		Vars.add(this);

		return Vars;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to compute the number of occurrences of each
	 * variable of this term.
	 * 
	 * The provided mapping is filled accordingly.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param occurrences a mapping which associates
	 * variables with their number of occurrences in 
	 * this term
	 */
	@Override
	protected void getVariableOccurrencesAux(Map<Variable, Integer> occurrences) {
		Integer n = occurrences.get(this);
		occurrences.put(this, (n == null ? 0 : n) + 1);
	}
	
	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of function symbols of this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Therefore, this method
	 * always returns an empty set.
	 * 
	 * @return an empty set
	 */
	@Override
	protected Set<FunctionSymbol> getFunSymbolsAux() {
		return new HashSet<FunctionSymbol>();
	}
	
	/**
	 * An auxiliary, internal, method which returns
	 * the subterm of this term at the given single
	 * position.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. 
	 * 
	 * @param i a single position
	 * @return the subterm of this term at the given
	 * position
	 * @throws IndexOutOfBoundsException
	 */
	@Override
	protected Term getAux(int i) {
		throw new IndexOutOfBoundsException(i + " -- " + this);
	}
	
	/**
	 * An auxiliary, internal, method which is used to
	 * return the subterm of this term at the position
	 * specified by the provided iterator.
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
	 * It is also supposed that <code>it</code> has a
	 * next element. Consequently, this method always
	 * throws an <code>IndexOutOfBoundsException</code>.
	 * 
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @throws IndexOutOfBoundsException
	 */
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		throw new IndexOutOfBoundsException(it.next() + " -- " + this);
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the disagreement positions
	 * of this term and the specified term.
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * Moreover, it is supposed that <code>this != t</code>.
	 * 
	 * @param t a term
	 * @param var <code>true</code> iff disagreement pairs of the
	 * form <variable,variable> are allowed
	 * @return a collection consisting of the disagreement positions
	 * of this term and the given term
	 */
	@Override
	protected Collection<Position> dposAux(Term t, boolean var) {
		// The collection to return at the end.
		Collection<Position> C = new LinkedList<Position>();

		if (!(t instanceof Variable) || var)
			C.add(new Position());

		return C;
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, the subterm at the position specified by
	 * <code>it</code> with <code>t</code>.
	 * 
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * 
	 * Both this term and <code>t</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * 
	 * Moreover, it is supposed that <code>it</code> has a
	 * next element. Consequently, this method always
	 * throws an <code>IndexOutOfBoundsException</code>
	 * because the only valid position in a variable is the
	 * root position.
	 * 
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param t a replacing term
	 * @throws IndexOutOfBoundsException
	 */
	@Override
	protected Term replaceAux(Iterator<Integer> it, Term t) {
		throw new IndexOutOfBoundsException(it.next() + " -- " + this);
	}
	
	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, each variable with the provided term
	 * <code>t</code>.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * 
	 * Both this term and <code>t</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * 
	 * @param t a replacing term
	 * @return <code>t</code>, because this term is a
	 * variable
	 */
	@Override
	protected Term replaceVariablesAux(Term t) {
		return t;
	}

	/**
	 * An auxiliary, internal, method which tries to complete
	 * <code>theta</code> into a matcher of this term onto
	 * <code>t</code>.
	 * 
	 * This term and <code>t</code> are not modified by this
	 * method. On the contrary, <code>theta</code> may be
	 * modified, even if this method fails.
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * @param t a term
	 * @param theta a substitution
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a matcher of this term onto
	 * <code>t</code>
	 */
	@Override
	protected boolean isMoreGeneralThanAux(Term t, Substitution theta) {
		return theta.add(this, t);
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether the terms <code>s</code> and <code>t</code>
	 * are unifiable. If they are unifiable, then the computed
	 * most general unifier is applied to them (hence, they are
	 * modified). If they are not unifiable, then they may also
	 * be modified.
	 * 
	 * Both <code>s</code> and <code>t</code> are supposed to
	 * be their class representative. It is also supposed
	 * that <code>s != t</code>.
	 * 
	 * Moreover, this term is supposed to be the schema term
	 * of <code>s</code>.
	 * 
	 * @param s a term whose schema term is this term
	 * @param t a term
	 * @return <code>true</code> iff <code>s</code> and
	 * <code>t</code> are unifiable or they contain a cycle
	 * at the end of this method
	 */
	@Override
	protected boolean unifyClosureAux(Term s, Term t) {
		s.union(t);
		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for finding a unification solution from this
	 * term.
	 * 
	 * If a solution is found and <code>theta != null</code>,
	 * then <code>theta</code> is completed with the solution.
	 * 
	 * This term is supposed to be the schema of its class
	 * representative.
	 * 
	 * @param theta a substitution
	 * @return <code>true</code> iff a solution could be found
	 */
	@Override
	protected boolean findUnifSolutionAux(Substitution theta) {
		return true;
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
		return (0 < rho ? new LuVariable(this, rho) : this);
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

		if (rho_V == 0 && V == this) {
			this.changed = true;
			result = E.getRight().shallowCopy();
		}

		return result;
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term is this term.
	 * 
	 * Used in the implementation of step 2 of
	 * Alg. A-2.
	 * 
	 * @param rho a substitution to apply to, and
	 * complete from, this term
	 * @return this term
	 */
	@Override
	protected Term applyAndCompleteRho(Substitution rho) {
		// At this step of Alg. A-2, only 0 < rho
		// is considered.
		return this;
	}

	/**
	 * Applies the specified rho to this term
	 * (which is supposed to be the left-hand
	 * side of an equation).
	 * 
	 * At this step of Alg. A-2, only 0 < rho
	 * is considered, hence the resulting term
	 * is this term.
	 * 
	 * Used in the implementation of step 2 of
	 * Alg. A-2.
	 * 
	 * @param rho a substitution to apply to
	 * this term
	 * @return this term
	 */
	protected Term applyRho(Substitution rho) {
		// At this step of Alg. A-2, only 0 < rho
		// is considered.
		return this;
	}

	/**
	 * Completes <code>rho</code> from this term,
	 * which is supposed to be the left-hand side
	 * of an equation.
	 * 
	 * At this step of Alg. A-2, only 0 < rho
	 * is considered, hence this method does
	 * nothing.
	 * 
	 * Used in the implementation of step 4 of
	 * Alg. A-2.
	 * 
	 * @param rho a substitution to complete from
	 * this term
	 * @param right the right-hand side of the
	 * equation whose left-hand side is this term
	 */
	protected void completeRho(Substitution rho, Term right) {
		// At this step of Alg. A-2, only 0 < rho
		// is considered.
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether this term left-unifies with the specified term.
	 * Both this term and the specified term may be modified
	 * by this method.
	 * 
	 * @param hnode a term
	 * @param cost a cost
	 * @param dir a direction (<code>true</code> for
	 * left-to-right, <code>false</code> for right-to-left)
	 * @return <code>true</code> iff this term left-unifies
	 * with <code>t</code> or this term and <code>t</code>
	 * contain a cycle at the end of this method
	 */
	/*
	@Override
	protected boolean propagate(Term hnode, int cost, boolean dir) {
		return this.addArc(hnode, cost, dir);
	}
	 */

	/**
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term is not modified by this method.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param theta a substitution
	 * @return a term resulting from applying
	 * the specified substitution to this term
	 */
	@Override
	protected Term applyAux(Substitution theta) {
		Term t = theta.get(this);

		return (t == null ? this : t.shallowCopy());
	}

	/**
	 * Rewrites this term at inner positions with the
	 * rules of the provided TRS.
	 * 
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Consequently, as a variable
	 * does not have any inner position, this method
	 * always returns an empty collection.
	 * 
	 * @param IR a TRS for rewriting this term
	 * @return an empty collection
	 */
	@Override
	protected Collection<Term> rewriteAtInnerPositions(Trs IR) {
		return new LinkedList<Term>();
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * unfold this term with the provided rule at the
	 * provided position (specified as an iterator).
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Moreover, <code>it</code>
	 * is supposed to have a next element. Consequently,
	 * this method always throws an
	 * <code>IndexOutOfBoundsException</code>.
	 * 
	 * @param R a rule for unfolding this term
	 * @param it an iterator, that has a next element,
	 * over a position where the unfolding takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param var a boolean indicating whether unfolding
	 * of variable positions is enabled
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @throws IndexOutOfBoundsException
	 */
	@Override
	protected Term unfoldWithAux(RuleTrs R,
			Iterator<Integer> it,
			boolean dir, boolean var,
			Map<Term, Term> copies) {

		throw new IndexOutOfBoundsException(it.next() + " -- " + this);
	}

	/**
	 * An auxiliary, internal, method which returns
	 * an iterator over the positions of this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	protected Iterator<Position> iteratorAux() {
		LinkedList<Position> positions = new LinkedList<Position>();

		// The only available position for a
		// variable is the empty position.
		positions.add(new Position());

		return positions.listIterator();	
	}

	/**
	 * Returns a shallow iterator over the positions of
	 * this term. Such an iterator stops at subterms i.e.,
	 * it does not consider the class representative nor
	 * the schema of the subterms.
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<Position> shallowIterator() {
		LinkedList<Position> positions = new LinkedList<Position>();

		// The only available position for a
		// variable is the empty position.
		positions.add(new Position());

		return positions.listIterator(); 
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the depth of this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Consequently, this method
	 * always returns 0, as the depth of variable is 0.
	 * 
	 * @return 0
	 */
	@Override
	protected int depthAux() {
		return 0;
	}
	
	/**
	 * An auxiliary, internal, method for computing
	 * the maximum arity of a function symbol in
	 * this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Consequently, this method
	 * always returns a negative integer, as the arity
	 * of a variable is undefined.
	 * 
	 * @return a negative integer
	 */
	@Override
	protected int maxArityAux() {
		return -1;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * check whether this term embeds the specified term
	 * (homeomorphic embedding).
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * Moreover, it is supposed that <code>this != t</code>.
	 * 
	 * Consequently, this method always returns
	 * <code>false</code>.
	 * 
	 * @param t the reference term with which to compare
	 * @return <code>false</code>
	 */
	@Override
	protected boolean embedsAux(Term t) {
		return false;
	}

	/**
	 * An internal method which returns
	 * <code>REN(CAP(this term))</code>.
	 * 
	 * See [Arts & Giesl, TCS'00] for a definition
	 * of <code>REN</code> and <code>CAP</code>.
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * @param IR the TRS whose defined symbols are used
	 * for computing the result
	 * @param root a boolean indicating whether the term
	 * at root position has to be replaced with a variable
	 * if its root symbol is defined in <code>IR</code>
	 * @return <code>REN(CAP(this term))</code>
	 */
	@Override
	protected Term rencap(Trs IR, boolean root) {
		return new Variable();
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing the polynomial corresponding to this term.
	 * It fills the provided <code>Coefficients</code>
	 * with missing coefficients.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param coefficients the coefficients of the polynomials
	 * associated with each function symbol and each tuple symbol
	 * @return the polynomial corresponding to this term
	 */
	@Override
	protected Polynomial toPolynomialAux(PolyInterpretation coefficients) {

		return new PolynomialVar(this);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * generating a weight for each function symbol
	 * and each tuple symbol occurring in this term.
	 * The generated weights are added to the provided
	 * weight function.
	 * 
	 * Used for implementing the Knuth-Bendix order
	 * technique for proving termination of TRSs.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * For variables, this method does nothing as a
	 * variable does not contain any function or tuple
	 * symbol.
	 * 
	 * @param weights a weight function for storing
	 * the weight of each function symbol and each
	 * tuple symbol occurring in this term
	 */
	@Override
	protected void generateKBOWeightsAux(WeightFunction weights) {

	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing a tuple version of this term when this
	 * term is a function. If this term is not a function
	 * then this method merely returns this term.
	 * 
	 * Used in the dependency pair framework.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return this term, as a variable is not a function
	 */
	@Override
	protected Term toTupleAux() {
		return this;
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing a function version of this term when
	 * this term is a tuple. If this term is not a tuple
	 * then this method merely returns this term.
	 * 
	 * Used in the dependency pair framework.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return this term, as a variable is not a tuple
	 */
	@Override
	protected Term toFunctionAux() {
		return this;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO1) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 * 
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>false</code>, always, as (LPO1) is always
	 * false if this term is a variable, hence the completion
	 * of the specified order cannot succeed
	 */
	@Override
	protected boolean lpo1(LexOrder order, Term t) {
		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2a) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 * 
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>false</code>, always, as (LPO2a) is not
	 * applicable to a variable, hence the completion of
	 * the specified order cannot succeed
	 */
	@Override
	protected boolean lpo2a(LexOrder order, Term t) {
		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2b) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 * 
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>false</code>, always, as (LPO2b) is not
	 * applicable to a variable, hence the completion of
	 * the specified order cannot succeed
	 */
	@Override
	protected boolean lpo2b(LexOrder order, Term t) {
		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2c) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 * 
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>false</code>, always, as (LPO2c) is not
	 * applicable to a variable, hence the completion of
	 * the specified order cannot succeed
	 */
	@Override
	protected boolean lpo2c(LexOrder order, Term t) {
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for computing the weight of this term relatively
	 * to the provided weight function.
	 * 
	 * The weight of a term results from adding up the
	 * weights of all occurrences of symbols in the
	 * term (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
	 * @param weights a weight function
	 * @return the weight of this term relatively
	 * to the provided weight function
	 */
	@Override
	protected Integer getWeightAux(WeightFunction weights) {
		return weights.getVariableWeight().integerValue(null);
	}
	
	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2a) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 * 
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>false</code>, always, as (KBO2a) is not
	 * applicable to a variable, hence the completion of
	 * the specified order cannot succeed
	 */
	@Override
	protected boolean kbo2a(LexOrder order, WeightFunction weights, Term t) {
		return false;
	}
	
	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2b) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 * 
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>false</code>, always, as (KBO2b) is not
	 * applicable to a variable, hence the completion of
	 * the specified order cannot succeed
	 */
	@Override
	protected boolean kbo2b(LexOrder order, WeightFunction weights, Term t) {
		return false;
	}
	
	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2c) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 * 
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>false</code>, always, as (KBO2c) is not
	 * applicable to a variable, hence the completion of
	 * the specified order cannot succeed
	 */
	@Override
	protected boolean kbo2c(LexOrder order, WeightFunction weights, Term t) {
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * building empty filters for the function and tuple
	 * symbols occurring in this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * Does nothing, as no function nor tuple symbol
	 * occur in a variable.
	 * 
	 * @param filtering the data structure to complete
	 * with the filters built from this term
	 */
	@Override
	protected void buildFiltersAux(ArgFiltering filtering) {}

	/**
	 * An auxiliary, internal, method which is used for
	 * applying the specified argument filtering to this
	 * term.
	 * 
	 * This term is not modified by this method.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param filtering an argument filtering to apply
	 * to this term
	 * @return this term, as argument filterings map
	 * any variable to itself
	 */
	@Override
	protected Term applyFiltersAux(ArgFiltering filtering) {
		return this;
	}

	/**
	 * An auxiliary, internal, method which returns a string
	 * representation of this term relatively to the given
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
	 * @return a string representation of this term
	 */
	@Override
	protected String toStringAux(Map<Variable, String> variables, boolean shallow) {
		String s = variables.get(this);

		if (s == null) {
			s = "_" + variables.size();
			variables.put(this, s);
		}

		return s;
	}
}
