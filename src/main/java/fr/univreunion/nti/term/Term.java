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

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.polynomial.Polynomial;
import fr.univreunion.nti.program.trs.reducpair.LexOrder;
import fr.univreunion.nti.program.trs.reducpair.PolyInterpretation;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.leftunif.LuEquation;

/**
 * A term: a function or an atom, a variable, a Prolog list...
 * implemented as a DAG.
 * <p>
 * The objects of this class are mutable and not thread safe.
 *
 * <p>The homeomorphic-embedding operations follow T. Arts and J. Giesl,
 * <a href="https://doi.org/10.1016/S0304-3975(99)00207-8">Termination of
 * Term Rewriting Using Dependency Pairs</a>, Theoretical Computer Science
 * 236(1--2), 133--178, 2000. The path-order operations follow F. Baader and
 * T. Nipkow, <a href="https://doi.org/10.1017/CBO9781139172752">Term
 * Rewriting and All That</a>, Cambridge University Press, 1998.
 * The left-unification operations implement Algorithms A-1 and A-2 of
 * D. Kapur, D. R. Musser, P. Narendran, and J. Stillman,
 * <a href="https://doi.org/10.1016/0304-3975(91)90189-9">Semi-Unification</a>,
 * Theoretical Computer Science 81(2), 169--187, 1991.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class Term implements Iterable<Position> {

	/**
	 * A global value which is used to mark the terms.
	 * <p>
	 * It is essentially used for avoiding duplicate
	 * searches through the same subterms.
	 */
	private static long currentTime = 0;

	/**
	 * Returns the current time.
	 *
	 * @return the current time
	 */
	protected static synchronized long getCurrentTime() {
		return currentTime;
	}

	/**
	 * Increments the current time.
	 */
	protected static synchronized void incCurrentTime() {
		currentTime++;
	}

	/**
	 * A mark for this term.
	 * <p>
	 * It is essentially used for avoiding duplicate
	 * searches through the same subterms. It is
	 * set to, or compared with, the current time.
	 */
	protected long mark = -1;

	/**
	 * The representative for the class of this term.
	 * <p>
	 * Used for Union-Find operations.
	 */
	private Term representative = this;

	/**
	 * A counter of the size of the class of
	 * this term.
	 * <p>
	 * Used for Union-Find operations.
	 */
	private int size = 1;

	/**
	 * The schema term for the class of this term.
	 * <p>
	 * Used for Union-Find operations.
	 */
	private Term schema = this;

	/**
	 * Used in cycle checking in the unification
	 * algorithm.
	 */
	protected boolean visited = false;

	/**
	 * Used in cycle checking in the unification
	 * algorithm.
	 */
	private boolean acyclic = false;

	/**
	 * The list of all variables in the class
	 * of this term.
	 * <p>
	 * Used when generating solutions in the
	 * unification algorithm.
	 */
	protected List<Variable> vars;

	/**
	 * A flag used for checking whether this
	 * term has changed after some operation.
	 */
	protected boolean changed = false;

	/**
	 * Returns <code>true</code> iff the
	 * <code>changed</code> flag of this term
	 * is set to <code>true</code>, meaning that
	 * this term has changed.
	 *
	 * @return <code>true</code> iff this term
	 * has changed
	 */
	public boolean hasChanged() {
		return this.changed;
	}

	/**
	 * Returns the schema term for the class of this term.
	 *
	 * @return the schema term for the class of this term
	 */
	protected Term getSchema() {
		return this.schema;
	}

	/**
	 * Union-Find operation.
	 * <p>
	 * Returns the representative for the class
	 * of this term. Also compresses the path
	 * to the representative.
	 *
	 * @return the representative for the class
	 * of this term
	 */
	private Term find() {
		if (this.representative != this)
			this.representative = this.representative.find();
		return this.representative;
	}

	/**
	 * Union-Find operation.
	 * <p>
	 * Returns the schema of the class representative
	 * of this term. Also compresses the path to the
	 * representative.
	 *
	 * @return the schema of the class representative
	 * of this term
	 */
	protected Term findSchema() {
		return this.find().schema;
	}

	/**
	 * Union-Find operation.
	 * <p>
	 * Connects this term to the provided term.
	 * Both this term and the provided term
	 * are supposed to be the representatives
	 * of their respective class.
	 *
	 * @param t a term to connect to this term
	 */
	protected void union(Term t) {
		if (this.size >= t.size) {
			this.size += t.size;
			this.addVariables(t.vars);
			if (this.schema instanceof Variable)
				this.schema = t.schema;
			t.representative = this;
		}
		else {
			t.size += this.size;
			t.addVariables(this.vars);
			if (t.schema instanceof Variable)
				t.schema = this.schema;
			this.representative = t;
		}
	}

	/**
	 * Adds the specified variables to this term's unification class.
	 *
	 * @param variables the variables to add, or {@code null} for none
	 */
	private void addVariables(List<Variable> variables) {
		if (variables != null) {
			if (this.vars == null)
				this.vars = new LinkedList<>();
			this.vars.addAll(variables);
		}
	}

	/**
	 * Returns the root symbol of this term.
	 *
	 * @return the root symbol of this term
	 */
	public abstract FunctionSymbol getRootSymbol();

	/**
	 * Checks whether this term has the same structure as the
	 * specified term <code>t</code>. This term and <code>t</code>
	 * are not modified by this method.
	 * <p>
	 * This method implements a rough, but quickly computable,
	 * over-approximation of both the subsumption and the
	 * unification tests. It is essentially used for computing
	 * families (see method <code>getFamily</code> in class
	 * <code>FD_Graph</code>).
	 *
	 * @param t the term whose structure has to be compared
	 * to that of this term
	 * @return <code>true</code> if this term has the same
	 * structure as that of the given term and <code>false</code>
	 * otherwise
	 * @throws NullPointerException if the specified term is
	 * <code>null</code>
	 */
	public boolean hasSameStructureAs(Term t) {
		Term s = this.findSchema();
		t = t.findSchema();

		if (s == t) return true;
		return s.hasSameStructureAsAux(t);
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
	 *
	 * @param t the term whose structure has to be compared
	 * to that of this term
	 * @return <code>true</code> if this term has the same
	 * structure as that of the given term and <code>false</code>
	 * otherwise
	 */
	protected abstract boolean hasSameStructureAsAux(Term t);

	/**
	 * Indicates whether some other term is equal to
	 * this one.
	 * <p>
	 * This a deep, structural, comparison.
	 *
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term is the
	 * same as the term argument
	 */
	public boolean deepEquals(Term t) {
		Term.incCurrentTime();
		return this.deepEqualsAux1(t);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether some other term is equal to
	 * this one.
	 * <p>
	 * This a deep, structural, comparison.
	 *
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term is the
	 * same as the term argument
	 */
	protected boolean deepEqualsAux1(Term t) {
		Term s = this.find();
		t = t.find();

		if (s == t) return true;
		return s.deepEqualsAux(t);
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
	 * that <code>this != t</code>.
	 *
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term is the
	 * same as the term argument
	 */
	protected abstract boolean deepEqualsAux(Term t);

	/**
	 * Returns a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @return a shallow copy of this term
	 */
	public Term shallowCopy() {
		return this.findSchema().shallowCopyAux();
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
	 * class representative.
	 *
	 * @return a shallow copy of this term
	 */
	protected abstract Term shallowCopyAux();

	/**
	 * Returns a deep copy of this term i.e., a copy
	 * where each subterm is also copied, even variable
	 * subterms.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @return a deep copy of this term
	 */
	public Term deepCopy() {
		return this.findSchema().
				deepCopyAux(null, new HashMap<>());
	}

	/**
	 * Returns a deep copy of this term i.e., a copy
	 * where each subterm is also copied, even variable
	 * subterms.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return a deep copy of this term
	 */
	public Term deepCopy(Map<Term, Term> copies) {
		return this.findSchema().deepCopyAux(null, copies);
	}

	/**
	 * Returns a deep copy of this term i.e., a copy where
	 * each subterm is also copied, except the variables
	 * not occurring in the specified collection.
	 * <p>
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied (in this
	 * case, the behavior of this method is identical
	 * to that of <code>deepCopy()</code>).
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param varsToBeCopied a collection of variables
	 * that must be copied
	 * @return a deep copy of this term
	 */
	public Term deepCopy(Collection<Variable> varsToBeCopied) {
		return this.findSchema().
				deepCopyAux(varsToBeCopied, new HashMap<>());
	}

	/**
	 * Returns a deep copy of this term i.e., a copy where
	 * each subterm is also copied, except the variables
	 * not occurring in the specified collection.
	 * <p>
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied (in this
	 * case, the behavior of this method is identical
	 * to that of {@code deepCopy(Map<Term, Term>)}).
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param varsToBeCopied a collection of variables
	 * that must be copied
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return a deep copy of this term
	 */
	public Term deepCopy(Collection<Variable> varsToBeCopied,
			Map<Term, Term> copies) {

		return this.findSchema().
				deepCopyAux(varsToBeCopied, copies);
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
	protected abstract Term deepCopyAux(Collection<Variable> varsToBeCopied,
			Map<Term, Term> copies);

	/**
	 * Checks whether this term contains the given
	 * term.
	 *
	 * @param t a term whose presence in this
	 * term is to be tested
	 * @return <code>true</code> iff this term
	 * contains <code>t</code>
	 */
	public boolean contains(Term t) {
		Term.incCurrentTime();
		return this.containsAux1(t);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains the given
	 * term.
	 *
	 * @param t a term whose presence in this term
	 * is to be tested
	 * @return <code>true</code> iff this term
	 * contains <code>t</code>
	 */
	protected boolean containsAux1(Term t) {
		Term s = this.findSchema();

		if (s == t) return true;

		return s.containsAux(t);
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
	protected abstract boolean containsAux(Term t);

	/**
	 * Checks whether this term is ground i.e., contains
	 * no variable.
	 *
	 * @return <code>true</code> iff this term contains
	 * no variable
	 */
	public boolean isGround() {
		Term.incCurrentTime();
		return this.findSchema().isGroundAux();
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * check whether this term is ground i.e., contains
	 * no variable.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return <code>true</code> iff this term contains
	 * no variable
	 */
	protected abstract boolean isGroundAux();

	/**
	 * Checks whether this term points to a variable.
	 *
	 * @return <code>true</code> iff this term points
	 * to a variable
	 */
	public boolean isVariable() {
		return this.findSchema() instanceof Variable;
	}

	/**
	 * Checks whether this term is variable disjoint with
	 * the given term.
	 *
	 * @param t a term
	 * @return <code>true</code> if this term is variable
	 * disjoint with the given term and <code>false</code>
	 * otherwise
	 */
	public boolean isVariableDisjointWith(Term t) {
		return !this.hasVariablesInCommonWith(t);
	}

	/**
	 * Checks whether this term and the given term have at least one variable in
	 * common.
	 *
	 * @param term a term
	 * @return {@code true} if this term and the given term have a variable in
	 * common, and {@code false} otherwise
	 */
	public boolean hasVariablesInCommonWith(Term term) {
		Set<Variable> thisVariables = this.getVariables();
		Set<Variable> otherVariables = term.getVariables();

		for (Variable variable: thisVariables)
			if (otherVariables.contains(variable)) return true;

		return false;
	}

	/**
	 * Returns the set of variables of this term.
	 *
	 * @return the set of variables of this term
	 */
	public Set<Variable> getVariables() {
		Set<Variable> variables = new HashSet<>();
		this.collectVariablesInto(variables);
		return variables;
	}

	/**
	 * Adds the variables of this term to the provided set.
	 *
	 * @param variables the variable set to complete
	 * @throws NullPointerException if {@code variables} is {@code null}
	 */
	public void collectVariablesInto(Set<Variable> variables) {
		Objects.requireNonNull(variables, "variables");
		Term.incCurrentTime();
		this.findSchema().addVariablesTo(variables);
	}

	/**
	 * Adds the variables of this term to the provided set.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param variables the variable set to complete
	 */
	protected abstract void addVariablesTo(Set<Variable> variables);

	/**
	 * Computes the number of occurrences of each
	 * variable of this term and fills the provided
	 * mapping accordingly.
	 *
	 * @param occurrences a mapping which associates
	 * variables with their number of occurrences in
	 * this term
	 */
	public void getVariableOccurrences(Map<Variable, Integer> occurrences) {
		this.findSchema().getVariableOccurrencesAux(occurrences);
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
	protected abstract void getVariableOccurrencesAux(Map<Variable, Integer> occurrences);

	/**
	 * Returns the set of function symbols of this term.
	 *
	 * @return the set of function symbols of this term
	 */
	public Set<FunctionSymbol> getFunSymbols() {
		Term.incCurrentTime();
		return this.findSchema().getFunSymbolsAux();
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of function symbols of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return the set of function symbols of this term
	 */
	protected abstract Set<FunctionSymbol> getFunSymbolsAux();

	/**
	 * Returns the subterm of this term at the given
	 * single position.
	 *
	 * @param i a single position
	 * @return the subterm of this term at position
	 * <code>i</code>, or <code>null</code> if
	 * <code>i</code> is not a valid position in
	 * this term
	 */
	public Term get(int i) {
		return this.findSchema().getAux(i);
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
	 * @return the subterm of this term at position
	 * <code>i</code>, or <code>null</code> if
	 * <code>i</code> is not a valid position in
	 * this term
	 */
	protected abstract Term getAux(int i);

	/**
	 * Returns the subterm of this term at the given
	 * position.
	 * <p>
	 * This is a convenience method: the call
	 * <code>get(p)</code> is equivalent to
	 * <code>get(p, false)</code> (see method
	 * <code>get(Position p, boolean shallow)</code>
	 * in this class).
	 *
	 * @param p a position
	 * @return the subterm of this term at position
	 * <code>p</code>, or <code>null</code> if
	 * <code>p</code> is not a valid position in
	 * this term
	 */
	public Term get(Position p) {
		return this.get(p.iterator(), false);
	}

	/**
	 * Returns the subterm of this term at the given
	 * position.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * <p>
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 *
	 * @param p a position
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at position
	 * <code>p</code>, or <code>null</code> if
	 * <code>p</code> is not a valid position in
	 * this term
	 */
	public Term get(Position p, boolean shallow) {
		return this.get(p.iterator(), shallow);
	}

	/**
	 * An auxiliary, internal, method which returns the
	 * subterm of this term at the position specified
	 * by the provided iterator.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * <p>
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 *
	 * @param it an iterator over a position
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at the given position
	 * or <code>null</code> if the provided iterator does not
	 * correspond to a valid position in this term
	 */
	protected Term get(Iterator<Integer> it, boolean shallow) {
		Term s = (shallow ? this : this.findSchema());

		if (!it.hasNext()) return s;
		return s.getAux(it, shallow);
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
	 * next element.
	 *
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at the given position
	 * or <code>null</code> if the provided iterator does not
	 * correspond to a valid position in this term
	 */
	protected abstract Term getAux(Iterator<Integer> it, boolean shallow);

	/**
	 * Returns a collection consisting of the hat subterms
	 * of this term. A hat term has exactly one occurrence
	 * of a hat symbol located at the root position.
	 * <p>
	 * There are no duplicate in the returned collection,
	 * i.e., if s and t are in the returned collection
	 * then they are not equal (w.r.t. a deep, structural,
	 * comparison).
	 *
	 * @return a collection consisting of the hat subterms
	 * of this term
	 */
	public Collection<Term> getHatSubterms() {
		return this.findSchema().getHatSubtermsAux();
	}

	/**
	 * Checks whether this term contains a hat subterm.
	 *
	 * @return {@code true} iff this term contains a hat subterm
	 */
	public boolean containsHatSubterm() {
		Term.incCurrentTime();
		return this.findSchema().containsHatSubtermAux();
	}

	/**
	 * Checks whether this term contains a hat subterm.
	 * <p>
	 * This term is supposed to be the schema of its class representative.
	 *
	 * @return {@code true} iff this term contains a hat subterm
	 */
	protected abstract boolean containsHatSubtermAux();

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
	 *
	 * @return a collection consisting of the hat subterms
	 * of this term
	 */
	protected abstract Collection<Term> getHatSubtermsAux();

	/**
	 * Returns a collection consisting of the disagreement
	 * positions of this term and the specified term.
	 *
	 * @param t a term
	 * @param allowVariablePairs <code>true</code> iff disagreement pairs
	 * of the form (variable,variable) are allowed
	 * @return a collection consisting of the disagreement
	 * positions of this term and the given term
	 */
	public Collection<Position> dpos(Term t, boolean allowVariablePairs) {
		Term s = this.findSchema();
		t = t.findSchema();

		if (s == t) return new LinkedList<>();
		else return s.dposAux(t, allowVariablePairs);
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
	protected abstract Collection<Position> dposAux(Term t, boolean allowVariablePairs);

	/**
	 * Returns the term obtained from replacing, in a copy
	 * of this term, the subterm at position <code>p</code>
	 * with <code>t</code>.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method.
	 *
	 * @param p a position in this term
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 * @throws IndexOutOfBoundsException if the specified
	 * position is not a valid position in this term
	 */
	public Term replace(Position p, Term t) {
		return this.replace(p.iterator(), t);
	}

	/**
	 * Returns the term obtained from replacing, in a copy
	 * of this term, the subterm at the position specified
	 * by <code>it</code> with <code>t</code>.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method.
	 *
	 * @param it an iterator over a position
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 * @throws IndexOutOfBoundsException when the provided
	 * iterator does not correspond to a valid position in
	 * this term
	 */
	protected Term replace(Iterator<Integer> it, Term t) {
		Term s = this.findSchema();
		t = t.findSchema();

		if (!it.hasNext()) return t;
		else return s.replaceAux(it, t);
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, the subterm at the position specified by
	 * <code>it</code> with <code>t</code>.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * <p>
	 * Both this term and <code>t</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * <p>
	 * Moreover, it is supposed that <code>it</code> has a
	 * next element.
	 *
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 * @throws IndexOutOfBoundsException when the provided
	 * iterator does not correspond to a valid position in
	 * this term
	 */
	protected abstract Term replaceAux(Iterator<Integer> it, Term t);

	/**
	 * Returns the term obtained from replacing, in a copy
	 * of this term, each variable with the provided term
	 * <code>t</code>.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method.
	 *
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 */
	public Term replaceVariables(Term t) {
		return this.findSchema().replaceVariablesAux(t.findSchema());
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, each variable with the provided term
	 * <code>t</code>.
	 * <p>
	 * The returned term is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * <p>
	 * Both this term and <code>t</code> are supposed to be
	 * the schemas of their respective class representatives.
	 *
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 */
	protected abstract Term replaceVariablesAux(Term t);

	/**
	 * Checks whether this term is a variant of the
	 * specified term.
	 *
	 * @param t a term
	 * @return <code>true</code> iff this term is a
	 * variant of the specified term
	 */
	public boolean isVariantOf(Term t) {
		return this.isMoreGeneralThan(t) && t.isMoreGeneralThan(this);
	}

	/**
	 * Tries to complete <code>theta</code> into a
	 * renaming which is a matcher of this term onto
	 * <code>t</code>, i.e., tries to complete
	 * <code>theta</code> so that it is a renaming and
	 * this term is more general than <code>t</code>
	 * for <code>theta</code>.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method. On the contrary, <code>theta</code>
	 * may be modified, even if this method fails.
	 * <p>
	 * It is supposed that <code>theta</code> is a renaming,
	 * i.e., a bijection from variables to variables.
	 *
	 * @param t a term
	 * @param theta a renaming
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a renaming which is a matcher
	 * of this term onto <code>t</code>
	 */
	public boolean isVariantOf(Term t, Substitution theta) {
		return this.isMoreGeneralThan(t, theta) && t.isMoreGeneralThan(this, theta);
	}

	/**
	 * Checks whether this term matches onto the specified
	 * term, i.e., whether this term is more general than
	 * the specified term.
	 *
	 * @param t a term
	 * @return <code>true</code> iff this term is more
	 * general than the specified term
	 */
	public boolean isMoreGeneralThan(Term t) {
		return this.isMoreGeneralThan(t, new Substitution());
	}

	/**
	 * Tries to complete <code>theta</code> into a
	 * matcher of this term onto <code>t</code>, i.e.,
	 * tries to complete <code>theta</code> so that
	 * this term is more general than <code>t</code>
	 * for <code>theta</code>.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method. On the contrary, <code>theta</code>
	 * may be modified, even if this method fails.
	 *
	 * @param t a term
	 * @param theta a substitution
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a matcher of this term onto
	 * <code>t</code>
	 */
	public boolean isMoreGeneralThan(Term t, Substitution theta) {
		Term s = this.findSchema();
		t = t.findSchema();

		// For variables, we need to add s/t to theta, hence we do not check whether s == t.
		return s.isMoreGeneralThanAux(t, theta);
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
	protected abstract boolean isMoreGeneralThanAux(Term t, Substitution theta);

	/**
	 * Tries to complete <code>theta</code> into a
	 * unifier of this term with <code>t</code>, using
	 * the standard, not efficient, Robinson's algorithm.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method. The substitution <code>theta</code>
	 * is modified only if this method succeeds.
	 *
	 * @param t a term
	 * @param theta a substitution
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a unifier of this term with
	 * <code>t</code>
	 */
	public boolean isUnifiableWith(Term t, Substitution theta) {
		return this.findSchema().isUnifiableWithAux(
				t.findSchema(), theta);
	}

	/**
	 * An auxiliary, internal, method which tries to complete
	 * <code>theta</code> into a unifier of this term with
	 * <code>t</code>, using the standard, not efficient,
	 * Robinson's algorithm.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method. The substitution <code>theta</code>
	 * is modified only if this method succeeds.
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 *
	 * @param t a term
	 * @param theta a substitution
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a unifier of this term with
	 * <code>t</code>
	 */
	private boolean isUnifiableWithAux(Term t, Substitution theta) {
		return new RobinsonUnifier(this, t, theta).unify();
	}

	/**
	 * A read-only Robinson unifier which processes disagreements in leftmost
	 * order without repeatedly applying its complete substitution to both root
	 * terms. The result substitution is committed only after every equation has
	 * succeeded.
	 */
	private static final class RobinsonUnifier {

		/** The substitution supplied by the caller, copied for rollback. */
		private final Substitution initialSubstitution;

		/** The caller's substitution, updated only on success. */
		private final Substitution resultSubstitution;

		/** Equations waiting to be processed in leftmost order. */
		private final Deque<Disagreement> equations = new ArrayDeque<>();

		/** Bindings discovered after applying the initial substitution. */
		private Substitution bindings = new Substitution();

		/**
		 * Builds a unifier for the provided terms and initial substitution.
		 *
		 * @param source the first term
		 * @param target the second term
		 * @param resultSubstitution the substitution completed on success
		 */
		private RobinsonUnifier(
				Term source,
				Term target,
				Substitution resultSubstitution) {

			this.initialSubstitution = new Substitution(resultSubstitution);
			this.resultSubstitution = resultSubstitution;

			Term initialSource = source;
			Term initialTarget = target;
			if (!this.initialSubstitution.isEmpty()) {
				initialSource = source.apply(this.initialSubstitution);
				initialTarget = target.apply(this.initialSubstitution);
			}
			this.equations.addLast(new Disagreement(
					initialSource, initialTarget));
		}

		/**
		 * Processes every equation and commits the resulting substitution.
		 *
		 * @return <code>true</code> iff all equations are unifiable
		 */
		private boolean unify() {
			while (!this.equations.isEmpty())
				if (!this.unifyFirstEquation())
					return false;

			this.commitResult();
			return true;
		}

		/**
		 * Processes the first pending equation.
		 *
		 * @return <code>true</code> iff the equation is unifiable
		 */
		private boolean unifyFirstEquation() {
			Disagreement equation = this.equations.removeFirst();
			Term left = this.normalizeRoot(equation.left());
			Term right = this.normalizeRoot(equation.right());

			if (left == right) {
				// Robinson unification deliberately remains unsupported for tuples,
				// even when both sides share the same input object.
				if (left instanceof PrologTuple)
					left.dposAux(right, true);
				return true;
			}
			if (left instanceof Variable leftVariable)
				return this.bind(leftVariable, right);
			if (right instanceof Variable rightVariable)
				return this.bind(rightVariable, left);
			if (left instanceof Function leftFunction &&
					right instanceof Function rightFunction)
				return this.decompose(leftFunction, rightFunction);
			if (left instanceof HatFunction || right instanceof HatFunction)
				return this.simplifyHatEquation(left, right);

			// PrologTuple.dposAux(...) deliberately rejects this generic path.
			if (left instanceof PrologTuple || right instanceof PrologTuple)
				left.dpos(right, true);
			return left.deepEquals(right);
		}

		/**
		 * Applies bindings which may change the root kind of a term. Non-unary
		 * function roots are stable and their arguments are handled lazily.
		 *
		 * @param term the term whose root is needed
		 * @return the term with its current root normalized
		 */
		private Term normalizeRoot(Term term) {
			Term dereferenced = this.dereference(term);
			if (this.bindings.isEmpty())
				return dereferenced;
			if (dereferenced instanceof HatFunction)
				return dereferenced.apply(this.bindings);
			if (dereferenced instanceof Function function &&
					function.getRootSymbol().getArity() == 1)
				return function.apply(this.bindings);
			return dereferenced;
		}

		/**
		 * Follows the current variable bindings at root position.
		 *
		 * @param term the term to dereference
		 * @return the first non-bound term
		 */
		private Term dereference(Term term) {
			Term result = term;
			while (result instanceof Variable variable) {
				Term replacement = this.bindings.get(variable);
				if (replacement == null)
					break;
				result = replacement;
			}
			return result;
		}

		/**
		 * Adds a new acyclic binding.
		 *
		 * @param variable the variable to bind
		 * @param term its candidate image
		 * @return <code>true</code> iff the occurs check succeeds
		 */
		private boolean bind(Variable variable, Term term) {
			Term normalized = this.initialBindingImage(term);
			if (normalized.contains(variable))
				return false;

			Substitution simple = substitutionOf(variable, normalized);
			this.bindings = this.bindings.composeWith(simple);
			return true;
		}

		/**
		 * Builds the image of a new binding. When the initial substitution is
		 * empty, the input terms have deliberately not been copied; the first
		 * binding image is therefore copied here to preserve the historical
		 * flattened-result contract.
		 *
		 * @param term the candidate binding image
		 * @return the normalized binding image
		 */
		private Term initialBindingImage(Term term) {
			if (!this.bindings.isEmpty())
				return term.apply(this.bindings);
			return this.initialSubstitution.isEmpty() ?
					term.apply(this.initialSubstitution) : term;
		}

		/**
		 * Decomposes two functions with a common root, retaining leftmost order.
		 *
		 * @param left the first function
		 * @param right the second function
		 * @return <code>true</code> iff their root symbols are equal
		 */
		private boolean decompose(Function left, Function right) {
			if (left.getRootSymbol() != right.getRootSymbol())
				return false;

			for (int argumentIndex = left.getRootSymbol().getArity() - 1;
				 0 <= argumentIndex;
				 argumentIndex--)
				this.equations.addFirst(new Disagreement(
						left.getChild(argumentIndex),
						right.getChild(argumentIndex)));
			return true;
		}

		/**
		 * Simplifies an equation involving at least one hat function.
		 *
		 * @param left the first side
		 * @param right the second side
		 * @return <code>true</code> iff the equation was simplified
		 */
		private boolean simplifyHatEquation(Term left, Term right) {
			Term appliedLeft = this.bindings.isEmpty() ?
					left : left.apply(this.bindings);
			Term appliedRight = this.bindings.isEmpty() ?
					right : right.apply(this.bindings);
			if (appliedLeft == appliedRight)
				return true;
			if (appliedLeft instanceof HatFunction leftHat &&
					appliedRight instanceof HatFunction rightHat &&
					leftHat.getRootSymbol() == rightHat.getRootSymbol() &&
					leftHat.equalExponents(rightHat)) {
				this.equations.addFirst(new Disagreement(
						leftHat.getArgument(), rightHat.getArgument()));
				return true;
			}

			Term[] simplified = simplifyDisagreementPair(
					appliedLeft, appliedRight);
			if (simplified == null)
				return false;
			this.equations.addFirst(new Disagreement(
					simplified[0], simplified[1]));
			return true;
		}

		/**
		 * Builds a substitution consisting of one variable mapping.
		 *
		 * @param variable the mapping domain
		 * @param term the mapping image
		 * @return the substitution containing the mapping
		 */
		private static Substitution substitutionOf(
				Variable variable,
				Term term) {

			Substitution mapping = new Substitution();
			mapping.add(variable, term);
			return mapping;
		}

		/**
		 * Attempts to simplify a disagreement involving a hat function.
		 *
		 * @param left the first disagreement term
		 * @param right the second disagreement term
		 * @return the simplified pair, or <code>null</code> if no simplification
		 * can be made
		 */
		private static Term[] simplifyDisagreementPair(
				Term left,
				Term right) {

			if (left instanceof HatFunction leftHat) {
				Term[] simplified = leftHat.minus(right);
				if (simplified != null)
					return simplified;

				return right instanceof HatFunction rightHat ?
						rightHat.minus(left) : null;
			}

			if (right instanceof HatFunction rightHat)
				return reverseDisagreement(rightHat.minus(left));

			return null;
		}

		/**
		 * Reverses a simplified disagreement in place so that it retains the
		 * orientation of the original equation.
		 *
		 * @param disagreement a subtraction result, or <code>null</code>
		 * @return the provided result after reversal, or <code>null</code>
		 */
		private static Term[] reverseDisagreement(Term[] disagreement) {
			if (disagreement == null)
				return null;

			Term first = disagreement[0];
			disagreement[0] = disagreement[1];
			disagreement[1] = first;
			return disagreement;
		}

		/**
		 * A pair of terms forming an equation to solve.
		 *
		 * @param left the left term
		 * @param right the right term
		 */
		private record Disagreement(Term left, Term right) {}

		/** Commits the completed substitution to the caller. */
		private void commitResult() {
			Substitution result = this.bindings.isEmpty() ?
					this.initialSubstitution :
					this.initialSubstitution.composeWith(this.bindings);
			this.resultSubstitution.clear();
			for (Map.Entry<Variable, Term> mapping : result)
				this.resultSubstitution.add(
						mapping.getKey(), mapping.getValue());
		}
	}

	/**
	 * Checks whether this term and the specified term are
	 * unifiable. If they are unifiable, then the computed
	 * most general unifier is applied to them (hence, they
	 * are modified). If they are not unifiable, then they
	 * may also be modified. Therefore, it is recommended
	 * to apply this method to some copies of the terms
	 * whose unifiability has to be checked.
	 * <p>
	 * This method implements the almost linear algorithm
	 * provided in [F. Baader, W. Snyder. Unification Theory.
	 * Vol. 1 of Handbook on Automated Deduction,
	 * pp. 460--462]. See file
	 * <code>unification_theory.pdf</code> in this
	 * repository.
	 *
	 * @param t a term
	 * @return <code>true</code> iff this term and
	 * <code>t</code> are unifiable
	 */
	public boolean unifyWith(Term t) {
		return this.unifyClosure(t) && this.findUnifSolution(null);
	}

	/**
	 * Checks whether this term and the specified term are
	 * unifiable. If they are unifiable, then the computed
	 * most general unifier is applied to them (hence, they
	 * are modified). If they are not unifiable, then they
	 * may also be modified. Therefore, it is recommended
	 * to apply this method to some copies of the terms
	 * whose unifiability has to be checked.
	 * <p>
	 * The provided substitution is completed with the
	 * computed most general unifier. It may be modified
	 * even if this term and the specified term are not
	 * unifiable.
	 * <p>
	 * This method implements the almost linear algorithm
	 * provided in [F. Baader, W. Snyder. Unification Theory.
	 * Vol. 1 of Handbook on Automated Deduction,
	 * pp. 460--462]. See file
	 * <code>unification_theory.pdf</code> in this
	 * repository.
	 *
	 * @param t a term
	 * @param theta a substitution
	 * @return <code>true</code> iff this term and
	 * <code>t</code> are unifiable
	 */
	public boolean unifyWith(Term t, Substitution theta) {
		return this.unifyClosure(t) && this.findUnifSolution(theta);

	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether this term and the specified term are unifiable.
	 * If they are unifiable, then the computed most general
	 * unifier is applied to them (hence, they are modified).
	 * If they are not unifiable, then they may also be modified.
	 *
	 * @param t a term
	 * @return <code>true</code> iff this term and <code>t</code>
	 * are unifiable, or they contain a cycle at the end of this
	 * method
	 */
	protected boolean unifyClosure(Term t) {
		Term s = this.find();
		t = t.find();

		if (s == t) return true;
		return s.schema.unifyClosureAux(s, t);
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
	protected abstract boolean unifyClosureAux(Term s, Term t);

	/**
	 * Tries to find a unification solution from this term.
	 * <p>
	 * If a solution is found and <code>theta != null</code>,
	 * then <code>theta</code> is completed with the solution.
	 *
	 * @param theta a substitution
	 * @return <code>true</code> iff a solution could be found
	 */
	protected boolean findUnifSolution(Substitution theta) {
		Term s = this.findSchema();

		if (s.acyclic) return true;

		if (s.visited) return false;

		if (!s.findUnifSolutionAux(theta)) return false;

		s.acyclic = true;
		addUnificationClassMappings(theta, s);
		return true;
	}

	/**
	 * Adds the mappings induced by the specified unification class to the
	 * provided substitution.
	 *
	 * @param theta the substitution to complete, or {@code null}
	 * @param schema the schema term of the unification class
	 */
	private static void addUnificationClassMappings(
			Substitution theta, Term schema) {
		if (theta == null) return;

		List<Variable> variables = schema.find().vars;
		if (variables == null) return;

		for (Variable variable : variables)
			if (variable != schema)
				theta.addReplace(variable, schema);
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
	protected abstract boolean findUnifSolutionAux(Substitution theta);

	/**
	 * Checks whether this term left-unifies with the
	 * specified term i.e., there exists some substitutions
	 * <code>rho</code> and <code>sigma</code> which are
	 * such that <code>rho(sigma(this))=sigma(t)</code>.
	 * If the provided substitutions are not
	 * <code>null</code> then they are filled with
	 * <code>sigma</code> and <code>rho</code>.
	 * <p>
	 * This term and the provided term are not modified by
	 * this method.
	 * <p>
	 * This method implements Algorithm A-1 (for deciding
	 * left-unifiability) + Algorithm A-2 (for extracting
	 * a solution) provided in
	 * the Kapur et al. (1991) article cited in the class documentation.
	 * See file <code>semiunif-kapur.pdf</code> in this repository.
	 *
	 * @param t a term
	 * @param sigma the substitution to be filled by the
	 * left-unifier
	 * @param rho the substitution to be filled by the
	 * matcher
	 * @return <code>true</code> iff this term left-unifies
	 * with <code>t</code>
	 */
	public boolean leftUnifyWith(Term t,
			Substitution sigma, Substitution rho) {

		List<LuEquation> algorithmA1Equations = this.algorithmA1(t);

		if (algorithmA1Equations != null) {
			if (sigma != null && rho != null)
				algorithmA2(algorithmA1Equations, sigma, rho);
			return true;
		}

		return false;
	}

	/**
	 * Decides left-unifiability of this term with
	 * the specified term.
	 *
	 * @param t a term
	 * @return <code>null</code> if this term does not
	 * left-unify with the specified term, otherwise a
	 * list of equations from which rho and sigma can
	 * be extracted
	 */
	private List<LuEquation> algorithmA1(Term t) {
		// The list of equations resulting from Alg. A-1.
		List<LuEquation> result = new LinkedList<>();

		// A data structure used for computing the result.
		List<LuEquation> nextEquations = new LinkedList<>();

		// We initialize the timer for equations.
		LuEquation.resetTime();

		// Step 1 of Algorithm A-1.
		result.add(new LuEquation(this.distribute(1), t.shallowCopy()));

		boolean somethingChanged = true;
		while (somethingChanged) {
			// Steps 2 & 3 of Algorithm A-1.
			int time2and3 = LuEquation.getCurrentTime();
			if (!distributeAndCancelEquations(result, nextEquations))
				return null;
			boolean somethingChanged2and3 = (time2and3 < LuEquation.getCurrentTime());

			result.clear();
			result.addAll(nextEquations);
			nextEquations.clear();

			boolean somethingChanged4 = reduceEquationsWithEachOther(result);

			somethingChanged = somethingChanged2and3 || somethingChanged4;
		}

		return result;
	}

	/**
	 * Applies steps 2 and 3 of Algorithm A-1 to the provided equations.
	 *
	 * @param equations the equations to distribute and cancel
	 * @param nextEquations the list to which resulting equations are appended
	 * @return <code>false</code> if a root conflict or occurs-check failure is
	 * found, otherwise <code>true</code>
	 */
	private static boolean distributeAndCancelEquations(
			List<LuEquation> equations,
			List<LuEquation> nextEquations) {

		for (LuEquation equation : equations) {
			List<LuEquation> distributedEquations = equation.distributeAndCancel();
			if (distributedEquations == null)
				return false;

			// Preserve the historical second pass and its effect on equation time.
			nextEquations.addAll(equation.distributeAndCancel());
		}

		return true;
	}

	/**
	 * Applies step 4 of Algorithm A-1 by reducing each equation with every
	 * other equation until the first effective reduction.
	 *
	 * @param equations the equations to reduce with each other
	 * @return <code>true</code> iff an equation changed
	 */
	private static boolean reduceEquationsWithEachOther(
			List<LuEquation> equations) {

		int timeBeforeReduction = LuEquation.getCurrentTime();
		for (LuEquation equation : equations) {
			for (LuEquation otherEquation : equations)
				if (otherEquation != equation)
					otherEquation.reduceWith(equation);

			if (timeBeforeReduction < LuEquation.getCurrentTime())
				break;
		}

		return timeBeforeReduction < LuEquation.getCurrentTime();
	}

	/**
	 * Extracts the substitutions sigma and rho
	 * from the result of Algorithm A-1.
	 *
	 * @param algorithmA1Equations a list of equations provided by
	 * Algorithm A-1
	 * @param sigma a substitution to be filled
	 * with the mappings of sigma
	 * @param rho a substitution to be filled
	 * with the mappings of rho
	 */
	private static synchronized void algorithmA2(List<LuEquation> algorithmA1Equations,
			Substitution sigma, Substitution rho) {

		// Step 2 of Alg. A-2.
		completeEquationsWithRho(algorithmA1Equations, rho);

		// Step 3 of Alg. A-2.
		extractSigma(algorithmA1Equations, sigma);

		// Step 4 of Alg. A-2.
		completeRho(algorithmA1Equations, rho);
	}

	/**
	 * Applies step 2 of Algorithm A-2 by completing rho from equation
	 * right-hand sides and then applying it to equation left-hand sides.
	 *
	 * @param equations the equations produced by Algorithm A-1
	 * @param rho the substitution to apply and complete
	 */
	private static void completeEquationsWithRho(
			List<LuEquation> equations,
			Substitution rho) {

		List<LuEquation> completedEquations = new LinkedList<>();

		for (LuEquation equation : equations)
			completedEquations.add(new LuEquation(
					equation.getLeft(),
					equation.getRight().applyAndCompleteRho(rho)));
		equations.clear();
		for (LuEquation equation : completedEquations)
			// The left-hand side of each equation
			// should be a variable.
			equations.add(new LuEquation(
					((Variable) equation.getLeft()).applyRho(rho),
					equation.getRight()));
	}

	/**
	 * Applies step 3 of Algorithm A-2 by extracting rho-free equations into
	 * sigma.
	 *
	 * @param equations the completed equations
	 * @param sigma the substitution to fill
	 */
	private static void extractSigma(
			List<LuEquation> equations,
			Substitution sigma) {

		for (LuEquation equation : equations) {
			Term left = equation.getLeft();
			Term right = equation.getRight();
			if (left.isRhoFree() && right.isRhoFree())
				sigma.addReplace((Variable) left, right);
		}
	}

	/**
	 * Applies step 4 of Algorithm A-2 by completing rho from every equation.
	 *
	 * @param equations the completed equations
	 * @param rho the substitution to complete
	 */
	private static void completeRho(
			List<LuEquation> equations,
			Substitution rho) {

		for (LuEquation equation : equations)
			// The left-hand side of each equation
			// should be a variable.
			((Variable) equation.getLeft()).completeRho(rho, equation.getRight());
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term may be this term
	 * modified in place, or a new term.
	 * <p>
	 * Used in the implementation of step 2 of
	 * Alg. A-2.
	 *
	 * @param rho a substitution to apply to, and
	 * complete from, this term
	 * @return the term resulting from applying
	 * <code>rho</code> to this term
	 */
	protected abstract Term applyAndCompleteRho(Substitution rho);

	/**
	 * Returns <code>true</code> iff this term
	 * contains rho i.e., an instance of
	 * <code>LUVariable</code> whose rho component
	 * is not 0.
	 * <p>
	 * Used in the implementation of step 3 of
	 * Alg. A-2.
	 *
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	protected boolean containsRho() {
		Term.incCurrentTime();
		return this.findSchema().containsRhoAux();
	}

	/**
	 * Returns whether this term contains no occurrence of rho.
	 *
	 * <p>Used in the implementation of step 3 of Algorithm A-2.</p>
	 *
	 * @return {@code true} iff this term does not contain rho
	 */
	private boolean isRhoFree() {
		Term.incCurrentTime();
		return !this.findSchema().containsRhoAux();
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
	 *
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	protected abstract boolean containsRhoAux();

	/**
	 * Applies the distributivity rule to this term.
	 * <p>
	 * This term is not modified by this method.
	 * <p>
	 * Used in the left-unification decision procedure.
	 *
	 * @param rho the number of applications of rho
	 * to this term
	 * @return the resulting term
	 */
	public Term distribute(int rho) {
		return this.findSchema().distributeAux(rho);
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
	protected abstract Term distributeAux(int rho);

	/**
	 * Reduces this term by a single step of rewriting during
	 * the left-unification decision procedure, using the provided
	 * rule (specified as an oriented equation). The resulting term
	 * may be this term modified in place, or a new term.
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
	 * This method is public because it is called from
	 * <code>fr.univreunion.nti.term.leftunif</code>, which is a
	 * distinct Java package from <code>fr.univreunion.nti.term</code>.
	 *
	 * @param equation a rule (specified as an oriented
	 * equation)
	 * @return the resulting term
	 */
	public Term reduceWithLeftUnificationRule(LuEquation equation) {
		this.changed = false;
		return this.reduceWithLeftUnificationRuleAux(equation);
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
	protected abstract Term reduceWithLeftUnificationRuleAux(LuEquation equation);

	/**
	 * Applies the specified substitution to this term.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term is not modified by this method.
	 *
	 * @param theta a substitution
	 * @return a term resulting from applying
	 * the specified substitution to this term
	 */
	public Term apply(Substitution theta) {
		return this.findSchema().applyAux(theta);
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
	protected abstract Term applyAux(Substitution theta);

	/**
	 * Applies the specified substitution to this term,
	 * which is modified by this method.
	 *
	 * @param theta a substitution
	 */
	public void applyInPlace(Substitution theta) {
		this.findSchema().applyInPlaceAux(theta);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term (which is modified by this method).
	 *
	 * @param theta a substitution
	 */
	protected abstract void applyInPlaceAux(Substitution theta);

	/**
	 * Rewrites this term with the rules of the provided TRS.
	 * <p>
	 * The returned terms are "flattened" i.e., each of
	 * their subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 *
	 * @param trs a TRS for rewriting this term
	 * @return the collection of terms resulting from
	 * rewriting this term
	 */
	public Collection<Term> rewriteWith(Trs trs) {
		// The collection to return at the end.
		Collection<Term> result = new LinkedList<>();

		// First, we try to rewrite the term at root position
		// with the rules of trs.
		for (RuleTrs rule : trs) {
			Substitution theta = new Substitution();
			if (rule.getLeft().isMoreGeneralThan(this, theta) )
				result.add(rule.getRight().apply(theta));
		}

		// Then, we try to rewrite the subterms at inner
		// positions.
		result.addAll(this.findSchema().rewriteAtInnerPositions(trs));

		return result;
	}

	/**
	 * Rewrites this term at inner positions with the
	 * rules of the provided TRS.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param trs a TRS for rewriting this term
	 * @return the collection of terms resulting from
	 * rewriting this term at inner positions
	 */
	protected abstract Collection<Term> rewriteAtInnerPositions(Trs trs);

	/**
	 * Unfolds this term with the provided rule at the
	 * provided position.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 *
	 * @param rule a rule for unfolding this term
	 * @param p a position where the unfolding
	 * takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param unfoldVariablePositions a boolean indicating whether unfolding
	 * of variable positions is enabled
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return the term resulting from unfolding
	 * this term, or <code>null</code> if the
	 * unfolding fails
	 * @throws IndexOutOfBoundsException when
	 * <code>p</code> is not a valid position in
	 * this term
	 */
	public Term unfoldWith(RuleTrs rule, Position p,
			boolean dir, boolean unfoldVariablePositions, Map<Term, Term> copies) {

		return this.unfoldWith(
				rule, p.iterator(), dir, unfoldVariablePositions, copies);
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * unfold this term with the provided rule at the
	 * provided position (specified as an iterator).
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 *
	 * @param rule a rule for unfolding this term
	 * @param it an iterator over a position
	 * where the unfolding takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param unfoldVariablePositions a boolean indicating whether unfolding
	 * of variable positions is enabled
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return the term resulting from unfolding
	 * this term, or <code>null</code> if the
	 * unfolding fails
	 * @throws IndexOutOfBoundsException when the
	 * provided iterator does not correspond to a
	 * valid position in this term
	 */
	protected Term unfoldWith(RuleTrs rule,
			Iterator<Integer> it,
			boolean dir, boolean unfoldVariablePositions,
			Map<Term, Term> copies) {

		if (!it.hasNext())
			return this.unfoldAtRoot(
					rule, dir, unfoldVariablePositions, copies);

		return this.findSchema().unfoldWithAux(
				rule, it, dir, unfoldVariablePositions, copies);
	}

	/**
	 * Unfolds this term at its root with a fresh copy of a rule.
	 *
	 * @param rule the rule used for unfolding
	 * @param dir {@code true} for backward unfolding and {@code false} for
	 * forward unfolding
	 * @param unfoldVariablePositions whether unfolding variable positions is
	 * enabled
	 * @param copies the incrementally constructed map from source subterms to
	 * their copies
	 * @return the unfolded rule side, or {@code null} when unfolding fails
	 */
	private Term unfoldAtRoot(
			RuleTrs rule,
			boolean dir,
			boolean unfoldVariablePositions,
			Map<Term, Term> copies) {

		if (!unfoldVariablePositions && this.isVariable()) return null;

		RuleTrs ruleCopy = rule.deepCopy();
		Term thisCopy = this.deepCopy(copies);
		Term unifiedSide = dir ? ruleCopy.getRight() : ruleCopy.getLeft();
		if (!thisCopy.unifyWith(unifiedSide)) return null;

		return dir ? ruleCopy.getLeft() : ruleCopy.getRight();
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
	 * is supposed to have a next element.
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
	 * @return the term resulting from unfolding
	 * this term, or <code>null</code> if the
	 * unfolding fails
	 * @throws IndexOutOfBoundsException when the
	 * provided iterator does not correspond to a
	 * valid position in this term
	 */
	protected abstract Term unfoldWithAux(RuleTrs rule,
			Iterator<Integer> it,
			boolean dir, boolean unfoldVariablePositions,
			Map<Term, Term> copies);

	/**
	 * Returns an iterator over the positions of
	 * this term.
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<Position> iterator() {
		return this.findSchema().iteratorAux();
	}

	/**
	 * Applies the specified action to every subterm of this term, in prefix
	 * order.
	 *
	 * @param action the action to apply to each subterm
	 * @throws NullPointerException if {@code action} is {@code null}
	 */
	public final void forEachSubterm(Consumer<? super Term> action) {
		Objects.requireNonNull(action);
		this.findSchema().forEachSubtermAux(action);
	}

	/**
	 * An auxiliary, internal, method which applies the specified action to
	 * every subterm of this term, in prefix order.
	 * <p>
	 * This term is supposed to be the schema of its class representative.
	 *
	 * @param action the action to apply to each subterm
	 */
	protected void forEachSubtermAux(Consumer<? super Term> action) {
		for (Position position : this)
			action.accept(this.get(position));
	}

	/**
	 * An auxiliary, internal, method which returns
	 * an iterator over the positions of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return an <code>Iterator</code>
	 */
	protected abstract Iterator<Position> iteratorAux();

	/**
	 * Returns a shallow iterator over the positions of
	 * this term. Such an iterator stops at subterms i.e.,
	 * it does not consider the class representative nor
	 * the schema of the subterms.
	 *
	 * @return an <code>Iterator</code>
	 */
	public abstract Iterator<Position> shallowIterator();

	/**
	 * Returns the depth of this term.
	 *
	 * @return the depth of this term
	 */
	public int depth() {
		return this.findSchema().depthAux();
	}

	/**
	 * An auxiliary, internal, method for computing
	 * the depth of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return the depth of this term
	 */
	protected abstract int depthAux();

	/**
	 * Returns the maximum arity of a function
	 * symbol in this term.
	 *
	 * @return the maximum arity of a function
	 * symbol in this term
	 */
	public int maxArity() {
		return this.findSchema().maxArityAux();
	}

	/**
	 * An auxiliary, internal, method for computing
	 * the maximum arity of a function symbol in
	 * this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return the maximum arity of a function
	 * symbol in this term
	 */
	protected abstract int maxArityAux();

	/**
	 * Homeomorphic embedding.
	 *
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term embeds the
	 * specified term
	 */
	public boolean embeds(Term t) {
		Term s = this.findSchema();
		t = t.findSchema();

		if (s == t) return true;
		return s.embedsAux(t);
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
	 *
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term embeds the
	 * specified term
	 */
	protected abstract boolean embedsAux(Term t);

	/**
	 * Checks whether this term is connectable to the
	 * specified term w.r.t. the specified TRS.
	 *
	 * @param t a term
	 * @param trs a TRS
	 * @return <code>true</code> iff this term is connectable
	 * to the specified term w.r.t. the specified TRS
	 */
	public boolean isConnectableTo(Term t, Trs trs) {
		return this.buildConnectabilityPattern(trs).unifyWith(t.deepCopy());
	}

	/**
	 * Builds <code>REN(CAP(this term))</code> for a connectability test w.r.t.
	 * the specified TRS.
	 * <p>
	 * This term is not modified by this method.
	 *
	 * @param trs the TRS whose defined symbols are used for computing the result
	 * @return <code>REN(CAP(this term))</code>
	 */
	public Term buildConnectabilityPattern(Trs trs) {
		return this.findSchema().rencap(trs, false);
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
	protected abstract Term rencap(Trs trs, boolean root);

	/**
	 * Returns the polynomial corresponding to this term
	 * and fills the provided <code>Coefficients</code>
	 * with missing coefficients.
	 * <p>
	 * Used for implementing the polynomial interpretation
	 * technique for proving termination of TRSs.
	 *
	 * @param coefficients the coefficients of the polynomials
	 * associated with each function symbol and each tuple symbol
	 * @return the polynomial corresponding to this term
	 */
	public Polynomial toPolynomial(PolyInterpretation coefficients) {
		return this.findSchema().toPolynomialAux(coefficients);
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
	protected abstract Polynomial toPolynomialAux(PolyInterpretation coefficients);

	/**
	 * Generates a weight for each function symbol
	 * and each tuple symbol occurring in this term.
	 * The generated weights are added to the provided
	 * weight function.
	 * <p>
	 * Used for implementing the Knuth-Bendix order
	 * technique for proving termination of TRSs.
	 *
	 * @param weights a weight function for storing
	 * the weight of each function symbol and each
	 * tuple symbol occurring in this term
	 */
	public void generateKBOWeights(WeightFunction weights) {
		Term.incCurrentTime();
		this.findSchema().generateKBOWeightsAux(weights);
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
	 *
	 * @param weights a weight function for storing
	 * the weight of each function symbol and each
	 * tuple symbol occurring in this term
	 */
	protected abstract void generateKBOWeightsAux(WeightFunction weights);

	/**
	 * Returns a tuple version of this term when
	 * this term is a function. If this term is
	 * not a function then this method merely
	 * returns this term.
	 * <p>
	 * Used in the dependency pair framework.
	 *
	 * @return a tuple version of this term
	 */
	public Term toTuple() {
		return this.findSchema().toTupleAux();
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
	 * @return a tuple version of this term
	 */
	protected abstract Term toTupleAux();

	/**
	 * Returns a function version of this term when
	 * this term is a tuple. If this term is not a
	 * tuple then this method merely returns this
	 * term.
	 * <p>
	 * Used in the dependency pair framework.
	 *
	 * @return a function version of this term
	 */
	public Term toFunction() {
		return this.findSchema().toFunctionAux();
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
	 * @return a function version of this term
	 */
	protected abstract Term toFunctionAux();

	/**
	 * Completes the specified partial order on function symbols
	 * so that this term is greater than, or equal to, <code>t</code>
	 * w.r.t. the lexicographic path order.
	 *
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>true</code> iff the completion succeeds
	 */
	public boolean completeLPO(LexOrder order, Term t) {
		return this.deepEquals(t) || this.completeLPOStrict(order, t);
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that this term is strictly greater than <code>t</code>
	 * w.r.t. the lexicographic path order.
	 *
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>true</code> iff the completion succeeds
	 */
	public boolean completeLPOStrict(LexOrder order, Term t) {
		Term s = this.findSchema();
		t = t.findSchema();

		return
				s.lpo1(order, t) ||
				s.lpo2a(order, t) ||
				s.lpo2b(order, t) ||
				s.lpo2c(order, t);
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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean lpo1(LexOrder order, Term t);

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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean lpo2a(LexOrder order, Term t);

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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean lpo2b(LexOrder order, Term t);

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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean lpo2c(LexOrder order, Term t);

	/**
	 * Completes the specified partial order on function symbols
	 * so that this term is greater than, or equal to, <code>t</code>
	 * w.r.t. the Knuth-Bendix order related to the provided
	 * weight function.
	 *
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>true</code> iff the completion succeeds
	 */
	public boolean completeKBO(LexOrder order, WeightFunction weights, Term t) {
		return this.deepEquals(t) || this.completeKBOStrict(order, weights, t);
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that this term is strictly greater than <code>t</code>
	 * w.r.t. the Knuth-Bendix order related to the provided
	 * weight function.
	 *
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>true</code> iff the completion succeeds
	 */
	public boolean completeKBOStrict(LexOrder order, WeightFunction weights, Term t) {
		Term s = this.findSchema();
		t = t.findSchema();

		// First, we check whether the number of occurrences
		// of each variable is greater in s than in t.
		Map<Variable, Integer> sourceOccurrences = new HashMap<>();
		s.getVariableOccurrences(sourceOccurrences);
		Map<Variable, Integer> targetOccurrences = new HashMap<>();
		t.getVariableOccurrences(targetOccurrences);

		if (this.hasMoreOccurrencesThan(sourceOccurrences, targetOccurrences)) {
			// Then, we complete the partial order so that
			// (KBO1) or (KBO2) are satisfied
			// (see p. 124 of [Baader & Nipkow, 1998]).

			Integer sourceWeight = s.getWeight(weights);
			Integer targetWeight = t.getWeight(weights);
			if (sourceWeight != null && targetWeight != null) {
				if (sourceWeight > targetWeight)
					// (KBO1)
					return true;
				else if (sourceWeight.equals(targetWeight)) {
					// (KBO2)
					return
							s.kbo2a(order, weights, t) ||
							s.kbo2b(order, weights, t) ||
							s.kbo2c(order, weights, t);
				}
			}
		}

		return false;
	}

	/**
	 * For each variable, checks whether the number of
	 * occurrences in <code>occ1</code> is greater than,
	 * or equal to, the number of occurrences in
	 * <code>occ2</code>.
	 *
	 * @param occ1 a mapping from variables to numbers
	 * of occurrences
	 * @param occ2 a mapping from variables to numbers
	 * of occurrences
	 * @return <code>true</code> iff for each variable,
	 * the number of occurrences in <code>occ1</code>
	 * is greater than, or equal to, the number of
	 * occurrences in <code>occ2</code>
	 */
	private boolean hasMoreOccurrencesThan(
			Map<Variable, Integer> occ1, Map<Variable, Integer> occ2) {

		for (Map.Entry<Variable, Integer> e : occ2.entrySet()) {
			Integer n = occ1.get(e.getKey());
			if (n == null || n < e.getValue()) return false;
		}

		return true;
	}

	/**
	 * Returns the weight of this term relatively
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
	public Integer getWeight(WeightFunction weights) {
		return this.findSchema().getWeightAux(weights);
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
	protected abstract Integer getWeightAux(WeightFunction weights);

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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean kbo2a(LexOrder order, WeightFunction weights, Term t);

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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean kbo2b(LexOrder order, WeightFunction weights, Term t);

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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean kbo2c(LexOrder order, WeightFunction weights, Term t);

	/**
	 * Builds empty filters for the function and tuple
	 * symbols occurring in this term. The filters are
	 * inserted into the specified data structure.
	 * <p>
	 * Used in the dependency pair framework.
	 *
	 * @param filtering the data structure to complete
	 * with the filters built from this term
	 */
	public void buildFilters(ArgFiltering filtering) {
		this.findSchema().buildFiltersAux(filtering);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * building empty filters for the function and tuple
	 * symbols occurring in this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param filtering the data structure to complete
	 * with the filters built from this term
	 */
	protected abstract void buildFiltersAux(ArgFiltering filtering);

	/**
	 * Applies the specified argument filtering to this
	 * term.
	 * <p>
	 * This term is not modified by this method.
	 *
	 * @param filtering an argument filtering to apply
	 * to this term
	 * @return the resulting term
	 */
	public Term applyFilters(ArgFiltering filtering) {
		return this.findSchema().applyFiltersAux(filtering);
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
	 * @return the resulting term
	 */
	protected abstract Term applyFiltersAux(ArgFiltering filtering);

	/**
	 * Computes a substitution form of this term.
	 * <p>
	 * More precisely, fills the provided substitution
	 * <code>theta</code> with mappings of the form
	 * <code>x -> t</code> where <code>x</code> is a new
	 * variable and <code>t</code> is a subterm of this
	 * term. At the same time, replaces <code>t</code> by
	 * <code>x</code> in this term. The term <code>s</code>
	 * resulting from the replacements is returned.
	 * <p>
	 * This term is not modified by this method.
	 * <p>
	 * By default this method does nothing, i.e.,
	 * it does not modify <code>theta</code> and
	 * just returns this term. Subclasses override
	 * this behavior.
	 *
	 * @param theta a substitution
	 * @return the term resulting from replacing
	 * subterms of this term by new variables
	 */
	public Term toSubstitution(Substitution theta) {
		// The default behaviour is to do nothing.
		// Subclasses override this behaviour.
		return this;
	}

	/**
	 * Returns a string representation of this term relatively
	 * to the given set of variable symbols.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * <p>
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 *
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return a string representation of this term
	 */
	public String toString(Map<Variable, String> variables, boolean shallow) {
		return (shallow ?
				this.toStringAux(variables, shallow) :
					this.findSchema().toStringAux(variables, shallow));
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
	protected abstract String toStringAux(
			Map<Variable, String> variables, boolean shallow);

	/**
	 * Returns a string representation of this term.
	 *
	 * @return a string representation of this term
	 */
	@Override
	public String toString() {
		return this.findSchema().
				toStringAux(new HashMap<>(), false);
	}
}
