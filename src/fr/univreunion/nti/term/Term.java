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
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 *
 * The objects of this class are mutable and not thread safe.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class Term implements Iterable<Position> {

	/**
	 * A global value which is used to mark the terms.
	 * 
	 * It is essentially used for avoiding duplicate
	 * searches through the same subterms.
	 */
	private static long currentTime = 0;

	/**
	 * Returns the current time.
	 * 
	 * @return the current time
	 */
	protected synchronized static long getCurrentTime() {
		return currentTime;
	}

	/**
	 * Increments the current time.
	 */
	protected synchronized static void incCurrentTime() {
		currentTime++;
	}

	/**
	 * A mark for this term.
	 * 
	 * It is essentially used for avoiding duplicate
	 * searches through the same subterms. It is
	 * set to, or compared with, the current time.
	 */
	protected long mark = -1;

	/**
	 * The representative for the class of this term.
	 * 
	 * Used for Union-Find operations.
	 */
	private Term representative = this;

	/**
	 * A counter of the size of the class of
	 * this term.
	 * 
	 * Used for Union-Find operations.
	 */
	private int size = 1;

	/**
	 * The schema term for the class of this term.
	 * 
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
	 * 
	 * Used when generating solutions in the
	 * unification algorithm.
	 */
	protected List<Variable> vars = new LinkedList<Variable>();

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
	 * 
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
	 * 
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
	 * 
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
			this.vars.addAll(t.vars);
			if (this.schema instanceof Variable)
				this.schema = t.schema;
			t.representative = this;
		}
		else {
			t.size += this.size;
			t.vars.addAll(this.vars);
			if (t.schema instanceof Variable)
				t.schema = this.schema;
			this.representative = t;
		}
	}

	/**
	 * Flattens this term i.e., makes each of its subterms
	 * its own schema and the only element of its class.
	 */
	/*
	public void flatten() {
		this.mark = -1;
		this.representative = this;
		this.size = 1;
		this.schema = this;
		this.visited = false;
		this.acyclic = false;
		this.vars.clear();
		this.changed = false;
		this.flattenAux();
	}
	 */

	/**
	 * An auxiliary, internal, method which is used to
	 * flatten this term i.e., make each of its subterms
	 * its own schema and the only element of its class.
	 */
	// protected abstract void flattenAux();

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
	 * 
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
	 * 
	 * This a deep, structural, comparison which is
	 * used in the implementation of substitutions.
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
	 * 
	 * This a deep, structural, comparison which is
	 * used in the implementation of substitutions.
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
	 * 
	 * This a deep, structural, comparison which is
	 * used in the implementation of substitutions.
	 * 
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
	 * 
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
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
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
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this term
	 */
	public Term deepCopy() {
		return this.findSchema().
				deepCopyAux(null, new HashMap<Term, Term>());
	}

	/**
	 * Returns a deep copy of this term i.e., a copy
	 * where each subterm is also copied, even variable
	 * subterms.
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
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
	 * 
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied (in this 
	 * case, the behavior of this method is identical
	 * to that of <code>deepCopy()</code>).
	 * 
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
				deepCopyAux(varsToBeCopied, new HashMap<Term, Term>());
	}

	/**
	 * Returns a deep copy of this term i.e., a copy where
	 * each subterm is also copied, except the variables
	 * not occurring in the specified collection.
	 * 
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied (in this 
	 * case, the behavior of this method is identical
	 * to that of <code>deepCopy(Map<Term, Term>)</code>).
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
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
	protected abstract Term deepCopyAux(
			Collection<Variable> varsToBeCopied,
			Map<Term, Term> copies);

	/**
	 * Returns the number of occurrences of the
	 * provided term in this term.
	 * 
	 * @return the number of occurrences of the
	 * provided term in this term
	 */
	public int nbOccurrences(Term t) {
		Term s = this.findSchema();
		
		if (s == t) return 1;
		
		return s.nbOccurrencesAux(t);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return the number of occurrences of the
	 * provided term in this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Moreover, it is supposed
	 * that <code>this != t</code>.
	 * 
	 * @return the number of occurrences of the
	 * provided term in this term
	 */
	protected abstract int nbOccurrencesAux(Term t);
	
	/**
	 * Checks whether this term contains the given
	 * variable.
	 * 
	 * @param v a variable whose presence in this
	 * term is to be tested
	 * @return <code>true</code> iff this term
	 * contains <code>v</code>
	 */
	public boolean contains(Variable v) {
		Term.incCurrentTime();
		return this.findSchema().containsAux(v);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains the given
	 * variable.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param v a variable whose presence in this
	 * term is to be tested
	 * @return <code>true</code> iff this term
	 * contains <code>v</code>
	 */
	protected abstract boolean containsAux(Variable v);

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
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return <code>true</code> iff this term contains
	 * no variable
	 */
	protected abstract boolean isGroundAux();
	
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
		Set<Variable> Vars_this = this.getVariables();
		Set<Variable> Vars_t    = t.getVariables();

		for (Variable V: Vars_this)
			if (Vars_t.contains(V)) return false;

		return true;
	}

	/**
	 * Returns the set of variables of this term.
	 * 
	 * @return the set of variables of this term
	 */
	public Set<Variable> getVariables() {
		Term.incCurrentTime();
		return this.findSchema().getVariablesAux();
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of variables of this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return the set of variables of this term
	 */
	protected abstract Set<Variable> getVariablesAux();

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
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return the set of function symbols of this term
	 */
	protected abstract Set<FunctionSymbol> getFunSymbolsAux();

	/**
	 * Returns the subterm of this term at the given
	 * position.
	 * 
	 * This is a convenience method: the call
	 * <code>get(p)</code> is equivalent to
	 * <code>get(p, false)</code> (see method
	 * <code>get(Position p, boolean shallow)</code>
	 * in this class).
	 * 
	 * @param p a position
	 * @return the subterm of this term at the given
	 * position
	 * @throws IndexOutOfBoundsException when <code>p</code>
	 * is not a valid position in this term
	 */
	public Term get(Position p) {
		return this.get(p.iterator(), false);
	}

	/**
	 * Returns the subterm of this term at the given
	 * position.
	 * 
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * 
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 * 
	 * @param p a position
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at the given
	 * position
	 * @throws IndexOutOfBoundsException when <code>p</code>
	 * is not a valid position in this term
	 */
	public Term get(Position p, boolean shallow) {
		return this.get(p.iterator(), shallow);
	}

	/**
	 * An auxiliary, internal, method which returns the
	 * subterm of this term at the position specified
	 * by the provided iterator.
	 * 
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * 
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 * 
	 * @param it an iterator over a position
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at the given position
	 * @throws IndexOutOfBoundsException when the provided
	 * iterator does not correspond to a valid position in
	 * this term
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
	 * next element.
	 * 
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at the given position
	 * @throws IndexOutOfBoundsException when the provided
	 * iterator does not correspond to a valid position in
	 * this term
	 */
	protected abstract Term getAux(Iterator<Integer> it, boolean shallow);

	/**
	 * Returns a collection consisting of the disagreement
	 * positions of this term and the specified term.
	 * 
	 * @param t a term
	 * @param var <code>true</code> iff disagreement pairs
	 * of the form <variable,variable> are allowed
	 * @return a collection consisting of the disagreement
	 * positions of this term and the given term
	 */
	public Collection<Position> dpos(Term t, boolean var) {
		Term s = this.findSchema();
		t = t.findSchema();

		if (s == t) return new LinkedList<Position>();
		else return s.dposAux(t, var);
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
	protected abstract Collection<Position> dposAux(Term t, boolean var);

	/**
	 * Returns the term obtained from replacing, in a copy
	 * of this term, the subterm at position <code>p</code>
	 * with <code>t</code>.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * 
	 * @param p a position in this term
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 * @throws IndexOutOfBoundsException when the specified
	 * position is not a valid position in this term
	 */
	public Term replace(Position p, Term t) {
		return this.replace(p.iterator(), t);
	}

	/**
	 * Returns the term obtained from replacing, in a copy
	 * of this term, the subterm at the position specified
	 * by <code>it</code> with <code>t</code>.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
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
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
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
	 * @return the term resulting from the replacement
	 */
	protected abstract Term replaceVariablesAux(Term t);

	/**
	 * Checks whether this term matches onto the specified
	 * term i.e., whether this term is more general than
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
	 * matcher of this term onto <code>t</code> i.e.,
	 * tries to complete <code>theta</code> so that
	 * this term is more general than <code>t</code>
	 * for <code>theta</code>.
	 * 
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
		
		// if (s == t) return true; // NO: for variables, we need to add s/t to theta!
		return s.isMoreGeneralThanAux(t, theta);
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
	protected abstract boolean isMoreGeneralThanAux(Term t, Substitution theta);

	/**
	 * Tries to complete <code>theta</code> into a
	 * unifier of this term with <code>t</code>, using
	 * the standard, not efficient, Robinson's algorithm.
	 * 
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
	 * 
	 * This term and <code>t</code> are not modified by
	 * this method. The substitution <code>theta</code>
	 * is modified only if this method succeeds.
	 * 
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
		Substitution sigma = new Substitution(theta);

		Term t1, t2;

		// BEWARE: THIS ALGORITHM DOES NOT WORK FOR PROLOG TUPLES!!
		// Indeed, if this = (A, B) and t = (C, D, E) then
		// the disagreement positions are 0 and 1. After handling 0,
		// the algorithm transforms this to (C, B). Then the only
		// disagreement position is 1 with newThis.get(1) = B and
		// t.get(1) = D (instead of (D, E)) so the algorithm
		// transforms newThis to (C, D) (instead of (C, D, E)).
		// Finally, the only disagreement position of (C, D)
		// and (C, D, E) is 1 but we have an occur-check...

		while (!(t1 = this.apply(sigma)).deepEquals(t2 = t.apply(sigma))) {
			// We compute the disagreement pairs of t1 and t2.
			Collection<Position> D = t1.dpos(t2, true);

			// As the guard of the while loop is true, necessarily
			// D is not empty.
			Position p = D.iterator().next();
			Term t1_p = t1.get(p);
			Term t2_p = t2.get(p);

			// We check whether (t1_p, t2_p) is a simple pair.
			if (t1_p instanceof Variable && !t2_p.contains((Variable) t1_p)) {
				Substitution gamma = new Substitution();
				gamma.add((Variable) t1_p, t2_p);
				sigma = sigma.composeWith(gamma);
			}
			else if (t2_p instanceof Variable && !t1_p.contains((Variable) t2_p)) {
				Substitution gamma = new Substitution();
				gamma.add((Variable) t2_p, t1_p);
				sigma = sigma.composeWith(gamma);
			}
			else
				return false;
		}

		// If we get here, then everything went fine i.e., unification
		// succeeded. Hence, we copy sigma into theta.
		theta.clear();
		for (Map.Entry<Variable, Term> mapping : sigma)
			theta.add(mapping.getKey(), mapping.getValue());

		return true;
	}

	/**
	 * Checks whether this term and the specified term are
	 * unifiable. If they are unifiable, then the computed
	 * most general unifier is applied to them (hence, they
	 * are modified). If they are not unifiable, then they
	 * may also be modified. Therefore, it is recommended
	 * to apply this method to some copies of the terms
	 * whose unifiability has to be checked.
	 * 
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
	 * 
	 * The provided substitution is completed with the 
	 * computed most general unifier. It may be modified
	 * even if this term and the specified term are not
	 * unifiable.
	 * 
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
	 * are unifiable or they contain a cycle at the end of this
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
	protected abstract boolean unifyClosureAux(Term s, Term t);

	/**
	 * Tries to find a unification solution from this term.
	 * 
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

		if (s.findUnifSolutionAux(theta)) {
			s.acyclic = true;

			if (theta != null)
				for (Variable v : s.find().vars)
					if (v != s)
						theta.addReplace(v, s);

			return true;
		}

		return false;
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
	protected abstract boolean findUnifSolutionAux(Substitution theta);

	/**
	 * Checks whether this term left-unifies with the
	 * specified term i.e., there exists some substitutions
	 * <code>rho</code> and <code>sigma</code> which are
	 * such that <code>rho(sigma(this))=sigma(t)</code>.
	 * If the provided substitutions are not
	 * <code>null</code> then they are filled with
	 * <code>sigma</code> and <code>rho</code>.
	 * 
	 * This term and the provided term are not modified by
	 * this method.
	 * 
	 * This method implements Algorithm A-1 (for deciding
	 * left-unifiability) + Algorithm A-2 (for extracting
	 * a solution) provided in
	 * [D. Kapur, D. Musser, P. Narendran, J. Stillman.
	 * Semi-unification. Theoretical Computer Science 81,
	 * 1991]. See file <code>semiunif-kapur.pdf</code> in
	 * this repository.
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

		List<LuEquation> A1 = this.algorithmA1(t);

		if (A1 != null) {			
			if (sigma != null && rho != null)
				algorithmA2(A1, sigma, rho);
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
		List<LuEquation> Result = new LinkedList<LuEquation>();

		// A data structure used for computing the result.
		List<LuEquation> L  = new LinkedList<LuEquation>();

		// We initialize the timer for equations.
		LuEquation.resetTime();

		// Step 1 of Algorithm A-1.
		Result.add(new LuEquation(this.distribute(1), t.shallowCopy()));

		boolean somethingChanged = true;
		while (somethingChanged) {
			// Steps 2 & 3 of Algorithm A-1.
			int time2_3 = LuEquation.getCurrentTime();
			for (LuEquation E : Result) {
				List<LuEquation> Le = E.distributeAndCancel();
				if (Le == null) return null;
				L.addAll(E.distributeAndCancel());
			}
			boolean somethingChanged2_3 = (time2_3 < LuEquation.getCurrentTime());

			Result.clear();
			Result.addAll(L);
			L.clear();

			// Step 4 of Algorithm A-1.
			// We take an equation and try to reduce
			// all the other equations with it. If
			// something changes, then we stop.
			int time4 = LuEquation.getCurrentTime();
			for (LuEquation E : Result) {
				for (LuEquation EE : Result)
					if (EE != E)
						EE.reduceWith(E);
				if (time4 < LuEquation.getCurrentTime())
					break;
			}
			boolean somethingChanged4 = (time4 < LuEquation.getCurrentTime());

			somethingChanged = somethingChanged2_3 || somethingChanged4;
		}

		return Result;
	}

	/**
	 * Extracts the substitutions sigma and rho
	 * from the result of Algorithm A-1.
	 * 
	 * @param A1 a list of equations provided by
	 * Algorithm A-1
	 * @param sigma a substitution to be filled
	 * with the mappings of sigma
	 * @param rho a substitution to be filled
	 * with the mappings of rho
	 */
	private synchronized static void algorithmA2(List<LuEquation> A1,
			Substitution sigma, Substitution rho) {

		// A data structure used for computing the result.
		List<LuEquation> L  = new LinkedList<LuEquation>();

		// Step 2 of Alg. A-2.
		for (LuEquation E : A1)
			L.add(new LuEquation(
					E.getLeft(),
					E.getRight().applyAndCompleteRho(rho)));
		A1.clear();
		for (LuEquation E : L)
			// The left-hand side of each equation
			// should be a variable.
			A1.add(new LuEquation(
					((Variable) E.getLeft()).applyRho(rho),
					E.getRight()));

		// Step 3 of Alg. A-2.
		for (LuEquation E : A1) {
			Term l = E.getLeft();
			Term r = E.getRight();
			if (!l.containsRho() && !r.containsRho())
				sigma.addReplace((Variable) l, r);
		}

		// Step 4 of Alg. A-2.
		for (LuEquation E : A1)
			// The left-hand side of each equation
			// should be a variable.
			((Variable) E.getLeft()).completeRho(rho, E.getRight());
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term may be this term
	 * modified in place, or a new term.
	 * 
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
	 * 
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
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	protected abstract boolean containsRhoAux();

	/**
	 * Applies the distributivity rule to this term.
	 * 
	 * This term is not modified by this method.
	 * 
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
	protected abstract Term distributeAux(int rho);

	/**
	 * Reduces this term by a single step of rewriting
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
	 * Used in the left-unification decision procedure.
	 * 
	 * @param E a rule (specified as an oriented
	 * equation)
	 * @return the resulting term
	 */
	// TODO
	// This could be improved: this method is public
	// whereas it is only used in the left-unification
	// decision procedure. So, it should not be public,
	// (but it is needed in package com.nti.term.leftunif)
	// or it should consider this.find().schema and have
	// a corresponding aux method (as the other public
	// methods in this class).
	public Term reduceWith(LuEquation E) {
		this.changed = false;
		return this.reduceWithAux(E);
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
	protected abstract Term reduceWithAux(LuEquation E);

	/**
	 * All the arcs from this term.
	 * 
	 * Used in the semi-unification algorithm.
	 */
	// private LinkedList<LUArc> arcs = new LinkedList<LUArc>();

	/**
	 * Checks whether this term left-unifies with the
	 * specified term i.e., there exists some substitutions
	 * <code>rho</code> and <code>sigma</code> which are
	 * such that <code>rho(sigma(this))=sigma(t)</code>.
	 * 
	 * Both this term and the specified term may be modified
	 * by this method. Therefore, it is recommended to apply
	 * it to some copies of the terms whose left-unifiability
	 * has to be checked.
	 * 
	 * This method implements the fast algorithm provided
	 * in [D. Kapur, D. Musser, P. Narendran, J. Stillman.
	 * Semi-unification. Theoretical Computer Science 81,
	 * 1991]. See file <code>semiunif-kapur.pdf</code> in
	 * this repository.
	 * 
	 * @param t a term
	 * @return <code>true</code> iff this term left-unifies
	 * with <code>t</code>
	 */
	/*
	public boolean leftUnifyWith(Term t) {
		return this.propagate(t, 1, true)
				&& this.findLeftUnifSolution(t);
	}
	 */

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
	// protected abstract boolean propagate(Term hnode, int cost, boolean dir);

	/**
	 * Adds an arc between this term and the specified term.
	 * 
	 * @param hnode a term to connect to this term
	 * @param cost the cost of the arc
	 * @param dir the direction of the arc
	 * @return <code>true</code> iff the operation succeeds
	 */
	/*
	protected boolean addArc(Term hnode, int cost, boolean dir) {
		// The value to return at the end.
		boolean result = true;

		// This test is not in Algorithm B
		// in the paper by Kapur et al.
		// We add it for avoiding self-loops
		// with cost 0, corresponding to
		// rewrite rules of the form x -> x.
		if (this != hnode) {
			Term tnode = this;

			if (!(tnode instanceof Variable && dir) &&
					(hnode instanceof Variable)) {
				tnode = hnode;
				hnode = this;
				dir = !dir;
			}

			// Add the new arc at the beginning of the
			// list of arcs from tnode.
			tnode.arcs.addFirst(new LUArc(cost, dir, hnode));

			// If adding an arc introduces multiple arcs from tnode.
			if (1 < tnode.arcs.size()) {
				// We search for the arcs from tnode to hnode.
				LinkedList<LUArc> L = new LinkedList<LUArc>();
				for (LUArc a : tnode.arcs)
					if (a.getTarget() == hnode) L.add(a);
				// If there are multiple arcs from tnode
				// to hnode, then we call multiEdge2.
				if (1 < L.size()) result = tnode.multiEdge2(L);
				// Otherwise, we call multiEdge1.
				else result = tnode.multiEdge1();
			}
		}

		return result;
	}
	 */

	/**
	 * Handles the situation where multiple arcs 
	 * from this tnode have been introduced, with
	 * distinct hnodes for all the arcs.
	 */
	/*
	private boolean multiEdge1() {
		// The value to return at the end.
		boolean result = true;

		Iterator<LUArc> it = this.arcs.iterator();
		// The new arc was added at the beginning
		// of the list of arcs (see method addArc).
		LUArc a1 = it.next();
		// Then, we search for a suitable second
		// arc from tnode: this is an arc which
		// is not marked for deletion (there is
		// exactly one such arc).
		LUArc a2 = it.next();
		while (a2.isMarkedForDeletion())
			a2 = it.next();

		// If the cost of a1 is less than that
		// of a2, then permute a1 and a2.
		if (a1.getCost() < a2.getCost()) {
			LUArc a = a1;
			a1 = a2;
			a2 = a;
		}

		// From here on, the cost of a1 is greater
		// than or equal to that of a2.
		a1.markForDeletion();
		if (a1.getDir() && a2.getDir())
			result = a2.getTarget().propagate(a1.getTarget(),
					a1.getCost() - a2.getCost(), true);
		else if (!a1.getDir() && !a2.getDir())
			result = a1.getTarget().propagate(a2.getTarget(),
					a1.getCost() - a2.getCost(), true);
		else
			result = a2.getTarget().propagate(a1.getTarget(),
					a1.getCost() + a2.getCost(), true);

		return result;
	}
	 */

	/**
	 * Handles the situation where multiple arcs 
	 * from this tnode to a same hnode have been
	 * introduced.
	 * 
	 * @param L a list of all the arcs from this
	 * tnode to a same hnode (contains at least
	 * two elements)
	 */
	/*
	private boolean multiEdge2(LinkedList<LUArc> L) {
		Iterator<LUArc> it = L.iterator();
		// We can safely write this as L contains at
		// least two elements.
		LUArc a1 = it.next(), a2 = it.next(); 
		if (a1.getDir() != a2.getDir()) {
			// If a1 and a2 have different directions
			// then try to find another arc with the
			// same direction as a1 or a2.
			while (it.hasNext()) {
				LUArc a = it.next();
				if (a.getDir() == a1.getDir()) {
					a2 = a;
					break;
				}
				else {
					a1 = a;
					break;
				}
			}
		}

		// If the cost of a1 is less than that
		// of a2, then permute a1 and a2.
		if (a1.getCost() < a2.getCost()) {
			LUArc a = a1;
			a1 = a2;
			a2 = a;
		}

		// From here on, the cost of a1 is greater
		// than or equal to that of a2.

		int c1 = a1.getCost();
		int c2 = a2.getCost();
		Term h1 = a1.getTarget();
		boolean dir1 = a1.getDir();

		if (h1 == this) {
			int g = gcd(c1, c2);
			if (g != c2) {
				this.arcs.remove(a1);
				this.arcs.remove(a2);
				return this.addArc(this, g, dir1);
			}
			else {
				this.arcs.remove(a1);
				return true;
			}
		}
		else if (dir1 == a2.getDir()) {
			// OK for case1: a1.getDir() == a2.getDir() == true.
			// But not sure for case2: a1.getDir() == a2.getDir() == false
			// (not clear in the paper...)
			if (h1.propagate(h1, c1 - c2, dir1))
				if (this.propagate(this, c1 - c2, dir1)) {
					this.arcs.remove(a1);
					if (c1 != c2 && c2 >= c1 / 2) {
						this.arcs.remove(a2);
						return this.propagate(h1, c1 % (c1 - c2), dir1);
					}
					return true;
				}
			return false;
		}
		else {
			if (h1.propagate(h1, c1 + c2, true))
				if (this.propagate(this, c1 + c2, true)) {
					// Not sure that the arc to consider is a1
					// (the paper says "mark the arc with cost i
					// for deletion" but does not explain what
					// is 'i'):
					a1.markForDeletion();
					return true;
				}
			return false;
		}
	}
	 */

	/**
	 * Returns the greatest common divisor
	 * of the provided integers.
	 *
	 * Implements the Euclidean algorithm.
	 * 
	 * @param a an integer
	 * @param b an integer 
	 * @return the gcd of the provided integers
	 */
	/*
	private static int gcd(int a, int b) {		
		int r;
		while (b > 0) {
			r = a % b;
			a = b;
			b = r;
		}

		return a;
	}

	protected boolean findLeftUnifSolution(Term t) {
		return true;
	}
	 */

	/**
	 * Applies the specified substitution to this term.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
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
	protected abstract Term applyAux(Substitution theta);

	/**
	 * Rewrites this term with the rules of the provided TRS.
	 * 
	 * The returned terms are "flattened" i.e., each of
	 * their subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 * 
	 * @param IR a TRS for rewriting this term
	 * @return the collection of terms resulting from
	 * rewriting this term
	 */
	public Collection<Term> rewriteWith(Trs IR) {
		// The collection to return at the end.
		Collection<Term> result = new LinkedList<Term>();

		// First, we try to rewrite the term at root position
		// with the rules of IR.
		for (RuleTrs R : IR) {
			Substitution theta = new Substitution();
			if (R.getLeft().isMoreGeneralThan(this, theta) )
				result.add(R.getRight().apply(theta));
		}

		// Then, we try to rewrite the subterms at inner
		// positions.
		result.addAll(this.findSchema().rewriteAtInnerPositions(IR));

		return result;
	}

	/**
	 * Rewrites this term at inner positions with the
	 * rules of the provided TRS.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param IR a TRS for rewriting this term
	 * @return the collection of terms resulting from
	 * rewriting this term at inner positions
	 */
	protected abstract Collection<Term> rewriteAtInnerPositions(Trs IR);

	/**
	 * Unfolds this term with the provided rule at the
	 * provided position.
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * @param R a rule for unfolding this term
	 * @param p a position where the unfolding
	 * takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param var a boolean indicating whether unfolding
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
	public Term unfoldWith(RuleTrs R, Position p,
			boolean dir, boolean var, Map<Term, Term> copies) {

		return this.unfoldWith(R, p.iterator(), dir, var, copies);
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * unfold this term with the provided rule at the
	 * provided position (specified as an iterator).
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * @param R a rule for unfolding this term
	 * @param it an iterator over a position
	 * where the unfolding takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param var a boolean indicating whether unfolding
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
	protected Term unfoldWith(RuleTrs R,
			Iterator<Integer> it,
			boolean dir, boolean var,
			Map<Term, Term> copies) {

		if (!it.hasNext()) {

			if (var || !this.isVariable()) {
				RuleTrs Rcopy = R.deepCopy();
				Term this_copy = this.deepCopy(copies);
				if (dir) {
					// Backward unfolding.
					if (this_copy.unifyWith(Rcopy.getRight()))
						return Rcopy.getLeft();
				}
				else {
					// Forward unfolding:
					if (this_copy.unifyWith(Rcopy.getLeft()))
						return Rcopy.getRight();
				}
			}

			return null;
		}

		return this.findSchema().unfoldWithAux(R, it, dir, var, copies);
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
	 * is supposed to have a next element.
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
	 * @return the term resulting from unfolding
	 * this term, or <code>null</code> if the
	 * unfolding fails
	 * @throws IndexOutOfBoundsException when the
	 * provided iterator does not correspond to a
	 * valid position in this term
	 */
	protected abstract Term unfoldWithAux(RuleTrs R,
			Iterator<Integer> it,
			boolean dir, boolean var,
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
	 * An auxiliary, internal, method which returns
	 * an iterator over the positions of this term.
	 * 
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
	 * 
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
	 * 
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
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
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
	 * @param IR a TRS
	 * @return <code>true</code> iff this term is connectable
	 * to the specified term w.r.t. the specified TRS
	 */
	public boolean isConnectableTo(Term t, Trs IR) {
		return this.findSchema().rencap(IR, false).
				unifyWith(t.deepCopy());
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
	protected abstract Term rencap(Trs IR, boolean root);

	/**
	 * Returns the polynomial corresponding to this term
	 * and fills the provided <code>Coefficients</code>
	 * with missing coefficients.
	 * 
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
	 * 
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
	 * 
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
	 * 
	 * Used for implementing the Knuth-Bendix order
	 * technique for proving termination of TRSs.
	 * 
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
	 * 
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
	 * 
	 * Used in the dependency pair framework.
	 * 
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
	 * 
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
	 * 
	 * Used in the dependency pair framework.
	 * 
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
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
		Map<Variable, Integer> occ_s = new HashMap<Variable, Integer>();
		s.getVariableOccurrences(occ_s);
		Map<Variable, Integer> occ_t = new HashMap<Variable, Integer>();
		t.getVariableOccurrences(occ_t);

		if (this.hasMoreOccurrencesThan(occ_s, occ_t)) {
			// Then, we complete the partial order so that
			// (KBO1) or (KBO2) are satisfied
			// (see p. 124 of [Baader & Nipkow, 1998]).

			Integer w_s = s.getWeight(weights);
			Integer w_t = t.getWeight(weights);
			if (w_s != null && w_t != null) {
				if (w_s > w_t)
					// (KBO1)
					return true;
				else if (w_s == w_t) {
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
	 * 
	 * The weight of a term results from adding up the
	 * weights of all occurrences of symbols in the
	 * term (see p. 124 of [Baader & Nipkow, 1998]).
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
	 * 
	 * The weight of a term results from adding up the
	 * weights of all occurrences of symbols in the
	 * term (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
	 * @param weights a weight function
	 * @return the weight of this term relatively
	 * to the provided weight function
	 */
	protected abstract Integer getWeightAux(WeightFunction weights);

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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean kbo2a(LexOrder order, WeightFunction weights, Term t);
	
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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean kbo2b(LexOrder order, WeightFunction weights, Term t);
	
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
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	protected abstract boolean kbo2c(LexOrder order, WeightFunction weights, Term t);
	
	/**
	 * Builds empty filters for the function and tuple
	 * symbols occurring in this term. The filters are
	 * inserted into the specified data structure.
	 * 
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
	 * 
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
	 * 
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
	 * 
	 * This term is not modified by this method.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param filtering an argument filtering to apply
	 * to this term
	 * @return the resulting term
	 */
	protected abstract Term applyFiltersAux(ArgFiltering filtering);

	/**
	 * Returns a string representation of the structure
	 * of this term. Essentially used for testing.
	 * 
	 * @return a string representation of the structure
	 * of this term
	 */
	public String toStringStructure(Map<Variable, String> variables) {
		// The string to return at the end.
		StringBuffer s = new StringBuffer();

		// Print the subterms of this.
		for (Iterator<Position> it = this.shallowIterator(); it.hasNext(); ) {
			Position p = it.next();
			Term this_p = this.get(p.iterator(), true);
			s.append("p = " + p + " : " + this_p.toString(variables, true) +
					" @" + Integer.toHexString(this_p.hashCode()) +
					" (" + this_p.getClass().getSimpleName() + ") ");
			s.append("find = @" +
					Integer.toHexString(this_p.find().hashCode()) + " ");
			s.append("schema = @" +
					Integer.toHexString(this_p.schema.hashCode()) + " ");
			s.append("size = " + this_p.size + " ");
			s.append("vars = [");
			for (Variable v : this_p.vars)
				s.append("@" + Integer.toHexString(v.hashCode()) + " ");
			s.append("]\n");
			/*
			s.append("arcs = [");
			for (LUArc A : this_p.arcs)
				s.append(A.toString(variables) + " ");
			s.append("]\n");
			 */
		}

		return s.toString();
	}

	/**
	 * Returns a string representation of this term relatively
	 * to the given set of variable symbols.
	 * 
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * 
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
				toStringAux(new HashMap<Variable, String>(), false);
	}
}
