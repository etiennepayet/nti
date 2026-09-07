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

package fr.univreunion.nti.term;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;

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
 * <p>
 * An object of this class is mutable.
 *
 * <p>The homeomorphic-embedding operations follow T. Arts and J. Giesl,
 * <a href="https://doi.org/10.1016/S0304-3975(99)00207-8">Termination of
 * Term Rewriting Using Dependency Pairs</a>, Theoretical Computer Science
 * 236(1--2), 133--178, 2000. The path-order operations follow F. Baader and
 * T. Nipkow, <a href="https://doi.org/10.1017/CBO9781139172752">Term
 * Rewriting and All That</a>, Cambridge University Press, 1998.
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
	public static final FunctionSymbol VARIABLE_ROOT_SYMBOL =
			FunctionSymbol.intern(" _", 0);

	/**
	 * Builds a variable.
	 */
	public Variable() {
		this.vars = new LinkedList<>();
		this.vars.add(this);
	}

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
	 * <p>
	 * This method implements a rough, but quickly computable,
	 * over-approximation of both the subsumption and the
	 * unification tests. It is essentially used for computing
	 * families (see method <code>getFamily</code> in class
	 * <code>FD_Graph</code>).
	 * <p>
	 * Both this term and the specified term are supposed to be
	 * the schemas of their respective class representatives.
	 * Moreover, it is supposed that <code>this != t</code>
	 * and that <code>t != null</code>.
	 * <p>
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
	 * @param variable a variable
	 * @return <code>true</code> iff this variable
	 * is the same as the provided one
	 */
	public boolean sameAs(Variable variable) {
		return this.isThisVariableWithoutRho(variable);
	}

	/**
	 * Returns <code>true</code> iff the provided variable is this
	 * standard variable, without any positive rho application.
	 *
	 * @param variable a variable
	 * @return <code>true</code> iff the provided variable is this
	 * standard variable, without any positive rho application
	 */
	private boolean isThisVariableWithoutRho(Variable variable) {
		if (variable instanceof LuVariable luVariable)
			return luVariable.getRho() == 0 &&
					luVariable.getVariable() == this;

		// Here, variable is a standard variable.
		return variable == this;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether some other term is equal to
	 * this one.
	 * <p>
	 * This a deep, structural, comparison.
	 * <p>
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
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
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
	 * <p>
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
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

		if (varsToBeCopied == null || varsToBeCopied.contains(this))
			return copies.computeIfAbsent(this, variable -> new Variable());

		return this;
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
		if (t instanceof LuVariable luVariable)
			return this.isThisVariableWithoutRho(luVariable);

		// Here, as this != t, we return false.
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0.
	 * <p>
	 * Used in the implementation of step 3 of
	 * Alg. A-2.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 * <p>
	 * Always returns <code>false</code> as this method
	 * is overridden by class <code>LUVariable</code>.
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
	 * <p>
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
	 * Adds this variable to the provided set.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param variables the variable set to complete
	 */
	@Override
	protected void addVariablesTo(Set<Variable> variables) {
		variables.add(this);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to compute the number of occurrences of each
	 * variable of this term.
	 * <p>
	 * The provided mapping is filled accordingly.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param occurrences a mapping which associates
	 * variables with their number of occurrences in
	 * this term
	 */
	@Override
	protected void getVariableOccurrencesAux(Map<Variable, Integer> occurrences) {
		occurrences.compute(this,
				(variable, occurrenceCount) ->
						occurrenceCount == null ? 1 : occurrenceCount + 1);
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of function symbols of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative. Therefore, this method
	 * always returns an empty set.
	 *
	 * @return an empty set
	 */
	@Override
	protected Set<FunctionSymbol> getFunSymbolsAux() {
		return new HashSet<>();
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the subterm of this term at the given single
	 * position.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param i a single position
	 * @return <code>null</code>
	 */
	@Override
	protected Term getAux(int i) {
		return null;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * return the subterm of this term at the position
	 * specified by the provided iterator.
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
	 * <p>
	 * It is also supposed that <code>it</code> has a
	 * next element. Consequently, this method always
	 * returns <code>null</code>.
	 *
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return <code>null</code>
	 */
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		return null;
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the hat subterms of this
	 * term.
	 * <p>
	 * There are no duplicate in the returned collection,
	 * i.e., if s and t are in the returned collection
	 * then they are not equal (w.r.t. a deep, structural,
	 * comparison).
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 * <p>
	 * As no hat symbol occurs in a variable, this method
	 * always returns an empty collection.
	 *
	 * @return an empty collection
	 */
	@Override
	protected Collection<Term> getHatSubtermsAux() {
		return new LinkedList<>();
	}

	/** {@inheritDoc} */
	@Override
	protected boolean containsHatSubtermAux() {
		return false;
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the disagreement positions
	 * of this term and the specified term.
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * <p>
	 * Moreover, it is supposed that <code>this != t</code>.
	 *
	 * @param t a term
	 * @param allowVariablePairs <code>true</code> iff disagreement pairs of the
	 * form {@code <variable, variable>} are allowed
	 * @return a collection consisting of the disagreement positions
	 * of this term and the given term
	 */
	@Override
	protected Collection<Position> dposAux(Term t, boolean allowVariablePairs) {
		// The collection to return at the end.
		Collection<Position> positions = new LinkedList<>();

		if (hasRootDisagreementWith(t, allowVariablePairs))
			positions.add(rootPosition());

		return positions;
	}

	/**
	 * Returns <code>true</code> iff a disagreement at root
	 * position has to be reported against the provided term.
	 *
	 * @param term a term
	 * @param allowVariablePairs <code>true</code> iff disagreement pairs of the
	 * form {@code <variable, variable>} are allowed
	 * @return <code>true</code> iff a disagreement at root
	 * position has to be reported against the provided term
	 */
	private static boolean hasRootDisagreementWith(
			Term term, boolean allowVariablePairs) {

		return !(term instanceof Variable) || allowVariablePairs;
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, the subterm at the position specified by
	 * <code>it</code> with <code>t</code>.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * <p>
	 * Both this term and <code>t</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * <p>
	 * Moreover, it is supposed that <code>it</code> has a
	 * next element. Consequently, this method always
	 * throws an <code>IndexOutOfBoundsException</code>
	 * because the only valid position in a variable is the
	 * root position.
	 *
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param t a replacing term
	 */
	@Override
	protected Term replaceAux(Iterator<Integer> it, Term t) {
		throw new IndexOutOfBoundsException(it.next() + " -- " + this);
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, each variable with the provided term
	 * <code>replacement</code>.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and <code>replacement</code> are not
	 * modified by this method.
	 * <p>
	 * Both this term and <code>replacement</code> are
	 * supposed to be the schemas of their respective class
	 * representatives.
	 *
	 * @param replacement a replacing term
	 * @return <code>replacement</code>, because this term is
	 * a variable
	 */
	@Override
	protected Term replaceVariablesAux(Term replacement) {
		return replacement;
	}

	/**
	 * An auxiliary, internal, method which tries to complete
	 * <code>theta</code> into a matcher of this term onto
	 * <code>t</code>.
	 * <p>
	 * This term and <code>t</code> are not modified by this
	 * method. On the contrary, <code>theta</code> may be
	 * modified, even if this method fails.
	 * <p>
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
	 * <p>
	 * Both <code>s</code> and <code>t</code> are supposed to
	 * be their class representative. It is also supposed
	 * that <code>s != t</code>.
	 * <p>
	 * Moreover, this term is supposed to be the schema term
	 * of <code>s</code>.
	 *
	 * @param s a term whose schema term is this term
	 * @param t a term
	 * @return <code>true</code> iff <code>s</code> and
	 * <code>t</code> are unifiable, or they contain a cycle
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
	 * <p>
	 * If a solution is found and <code>theta != null</code>,
	 * then <code>theta</code> is completed with the solution.
	 * <p>
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
		return 0 < rho ? new LuVariable(this, rho) : this;
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
		if (!this.isThisVariableWithoutRho((Variable) equation.getLeft()))
			return this;

		this.changed = true;
		return equation.getRight().shallowCopy();
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term is this term.
	 * <p>
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
	 * <p>
	 * At this step of Alg. A-2, only {@code 0 < rho}
	 * is considered, hence the resulting term
	 * is this term.
	 * <p>
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
	 * <p>
	 * At this step of Alg. A-2, only {@code 0 < rho}
	 * is considered, hence this method does
	 * nothing.
	 * <p>
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
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term is not modified by this method.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param theta a substitution
	 * @return a term resulting from applying
	 * the specified substitution to this term
	 */
	@Override
	protected Term applyAux(Substitution theta) {
		Term replacement = theta.get(this);

		return replacement == null ? this : replacement.shallowCopy();
	}

	/**
	 * Unsupported operation because one can not
	 * apply a substitution in place to a variable.
	 */
	@Override
	protected void applyInPlaceAux(Substitution theta) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Rewrites this term at inner positions with the
	 * rules of the provided TRS.
	 * <p>
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative. Consequently, as a variable
	 * does not have any inner position, this method
	 * always returns an empty collection.
	 *
	 * @param trs a TRS for rewriting this term
	 * @return an empty collection
	 */
	@Override
	protected Collection<Term> rewriteAtInnerPositions(Trs trs) {
		return new LinkedList<>();
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * unfold this term with the provided rule at the
	 * provided position (specified as an iterator).
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative. Moreover, <code>it</code>
	 * is supposed to have a next element. Consequently,
	 * this method always throws an
	 * <code>IndexOutOfBoundsException</code>.
	 *
	 * @param rule a rule for unfolding this term
	 * @param it an iterator, that has a next element,
	 * over a position where the unfolding takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param unfoldVariablePositions a boolean indicating whether unfolding
	 * of variable positions is enabled
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 */
	@Override
	protected Term unfoldWithAux(RuleTrs rule,
			Iterator<Integer> it,
			boolean dir, boolean unfoldVariablePositions,
			Map<Term, Term> copies) {

		throw new IndexOutOfBoundsException(it.next() + " -- " + this);
	}

	/**
	 * An auxiliary, internal, method which returns
	 * an iterator over the positions of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	protected Iterator<Position> iteratorAux() {
		return rootPositionIterator();
	}

	/**
	 * Applies the specified action to this variable.
	 *
	 * @param action the action to apply to this variable
	 */
	@Override
	protected void forEachSubtermAux(Consumer<? super Term> action) {
		action.accept(this);
	}

	private static Iterator<Position> rootPositionIterator() {
		LinkedList<Position> positions = new LinkedList<>();

		// The only available position for a
		// variable is the empty position.
		positions.add(rootPosition());

		return positions.listIterator();
	}

	/**
	 * Returns a new root position.
	 *
	 * @return a new root position
	 */
	private static Position rootPosition() {
		return new Position();
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
		return rootPositionIterator();
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the depth of this term.
	 * <p>
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
	 * <p>
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
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * <p>
	 * Moreover, it is supposed that <code>this != t</code>.
	 * <p>
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
	 * <p>
	 * See [Arts &amp; Giesl, TCS'00] for a definition
	 * of <code>REN</code> and <code>CAP</code>.
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 *
	 * @param trs the TRS whose defined symbols are used
	 * for computing the result
	 * @param root a boolean indicating whether the term
	 * at root position has to be replaced with a variable
	 * if its root symbol is defined in <code>trs</code>
	 * @return <code>REN(CAP(this term))</code>
	 */
	@Override
	protected Term rencap(Trs trs, boolean root) {
		return new Variable();
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing the polynomial corresponding to this term.
	 * It fills the provided <code>Coefficients</code>
	 * with missing coefficients.
	 * <p>
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
	 * <p>
	 * Used for implementing the Knuth-Bendix order
	 * technique for proving termination of TRSs.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 * <p>
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
		// For variables, this method does nothing as a
		// variable does not contain any function or tuple
		// symbol.
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing a tuple version of this term when this
	 * term is a function. If this term is not a function
	 * then this method merely returns this term.
	 * <p>
	 * Used in the dependency pair framework.
	 * <p>
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
	 * <p>
	 * Used in the dependency pair framework.
	 * <p>
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
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
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
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
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
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
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
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
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
	 * <p>
	 * The weight of a term results from adding up the
	 * weights of all occurrences of symbols in the
	 * term (see p. 124 of [Baader &amp; Nipkow, 1998]).
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
	 * is satisfied (see p. 124 of [Baader &amp; Nipkow, 1998]).
	 * <p>
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
	 * is satisfied (see p. 124 of [Baader &amp; Nipkow, 1998]).
	 * <p>
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
	 * is satisfied (see p. 124 of [Baader &amp; Nipkow, 1998]).
	 * <p>
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
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 * <p>
	 * Does nothing, as no function nor tuple symbol
	 * occur in a variable.
	 *
	 * @param filtering the data structure to complete
	 * with the filters built from this term
	 */
	@Override
	protected void buildFiltersAux(ArgFiltering filtering) {
		// For variables, this method does nothing as a
		// variable does not contain any function or tuple
		// symbol.
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * applying the specified argument filtering to this
	 * term.
	 * <p>
	 * This term is not modified by this method.
	 * <p>
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
	 * @return a string representation of this term
	 */
	@Override
	protected String toStringAux(Map<Variable, String> variables, boolean shallow) {
		return variables.computeIfAbsent(this, k -> "_" + variables.size());
	}
}
