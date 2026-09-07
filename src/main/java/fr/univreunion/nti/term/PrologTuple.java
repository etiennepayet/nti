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
 * A flat Prolog tuple i.e., (e_1,...,e_n) where n >= 1 and
 * each e_i is not a tuple.
 * <p>
 * An object of this class is mutable.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PrologTuple extends Term {

	/**
	 * The root symbol for a Prolog tuple.
	 */
	public static final FunctionSymbol PROLOG_TUPLE_ROOT_SYMBOL =
			FunctionSymbol.intern(",", 2);

	/**
	 * The elements of this Prolog tuple.
	 */
	private final List<Term> elements = new LinkedList<>();

	/**
	 * Builds a flat Prolog tuple.
	 *
	 * @param elements the elements of this tuple
	 * @throws IllegalArgumentException if the given
	 * list of elements is empty or contains
	 * <code>null</code>
	 */
	public PrologTuple(List<? extends Term> elements) {
		if (elements.isEmpty())
			throw new IllegalArgumentException("Prolog tuples cannot be empty");

		this.addFlattenedElements(elements);
	}

	/**
	 * Adds the specified elements to this tuple, preserving the flat tuple
	 * invariant.
	 *
	 * @param elements the elements to add
	 */
	private void addFlattenedElements(List<? extends Term> elements) {
		for (Term element : elements) {
			if (element == null)
				throw new NullPointerException("Prolog tuples do not permit null elements");

			this.addFlattened(element);
		}
	}

	/**
	 * Builds an empty Prolog tuple.
	 * For internal use only.
	 */
	private PrologTuple() {}

	/**
	 * Appends the specified term to the end of this
	 * Prolog tuple.
	 * <p>
	 * For internal use only.
	 *
	 * @param t term to be appended to this Prolog tuple
	 * @throws NullPointerException if the specified term
	 * is <code>null</code>
	 */
	private void add(Term t) {
		if (t == null)
			throw new NullPointerException("Prolog tuples do not permit null elements");

		this.elements.add(t);
	}

	/**
	 * Appends all the elements in the specified Prolog
	 * tuple to the end of this Prolog tuple.
	 * <p>
	 * For internal use only.
	 *
	 * @param tuple Prolog tuple containing elements to be
	 * added to this Prolog tuple
	 * @throws NullPointerException if the specified term
	 * is <code>null</code>
	 */
	private void addAll(PrologTuple tuple) {
		this.elements.addAll(tuple.elements);
	}

	/**
	 * Appends the specified term to this tuple, flattening nested Prolog
	 * tuples to preserve the flat tuple invariant.
	 *
	 * @param term the term to append
	 */
	private void addFlattened(Term term) {
		if (term instanceof PrologTuple tuple)
			this.addAll(tuple);
		else
			this.add(term);
	}

	/**
	 * Returns the root symbol of this term.
	 *
	 * @return the root symbol of this term
	 */
	@Override
	public FunctionSymbol getRootSymbol() {
		return PROLOG_TUPLE_ROOT_SYMBOL;
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean hasSameStructureAsAux(Term t) {
		throw new UnsupportedOperationException();
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
	@Override
	protected boolean deepEqualsAux(Term t) {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.

		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return true;

		if (!(t instanceof PrologTuple other))
			return false;

		if (this.elements.size() != other.elements.size())
			return false;

		return this.hasDeepEqualElements(other);
	}

	/**
	 * Checks whether this tuple and the specified tuple have deeply equal
	 * elements, compared in iteration order.
	 *
	 * @param other the tuple to compare with this tuple
	 * @return <code>true</code> iff both tuples have deeply equal elements
	 */
	private boolean hasDeepEqualElements(PrologTuple other) {
		for (Iterator<Term> thisElements = this.elements.iterator(),
				otherElements = other.elements.iterator();
				thisElements.hasNext(); )
			if (!thisElements.next().deepEqualsAux1(otherElements.next()))
				return false;

		return true;
	}

	/**
	 * Checks whether this tuple has already been visited during the current
	 * traversal, marking it as visited otherwise.
	 *
	 * @return <code>true</code> iff this tuple had already been visited
	 * during the current traversal
	 */
	private boolean hasAlreadyBeenVisitedInCurrentTraversal() {
		long time = Term.getCurrentTime();
		if (this.mark >= time)
			return true;

		this.mark = time;
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
	 * class representative.
	 *
	 * @return a shallow copy of this term
	 */
	@Override
	protected Term shallowCopyAux() {
		// The term that will be returned at the end.
		PrologTuple copy = new PrologTuple();

		this.addShallowCopiesTo(copy);

		return copy;
	}

	/**
	 * Adds shallow copies of this tuple's elements to the specified tuple.
	 *
	 * @param target the tuple to complete
	 */
	private void addShallowCopiesTo(PrologTuple target) {
		for (Term element : this.elements)
			target.addFlattened(element.shallowCopy());
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
			Map<Term,Term> copies) {

		// The term that will be returned at the end.
		PrologTuple copy = new PrologTuple();

		this.addDeepCopiesTo(copy, varsToBeCopied, copies);

		return copy;
	}

	/**
	 * Adds deep copies of this tuple's elements to the specified tuple.
	 *
	 * @param target the tuple to complete
	 * @param varsToBeCopied the variables that must be copied
	 * @param copies the already built term copies
	 */
	private void addDeepCopiesTo(
			PrologTuple target,
			Collection<Variable> varsToBeCopied,
			Map<Term,Term> copies) {

		for (Term element : this.elements)
			target.addFlattened(element.deepCopy(varsToBeCopied, copies));
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
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return false.

		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		return this.hasElementContaining(t);
	}

	/**
	 * Checks whether one element of this tuple contains the specified term.
	 *
	 * @param t a term whose presence in this tuple is to be tested
	 * @return <code>true</code> iff one tuple element contains <code>t</code>
	 */
	private boolean hasElementContaining(Term t) {
		for (Term element : this.elements)
			if (element.containsAux1(t)) return true;

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
	 *
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	@Override
	protected boolean containsRhoAux() {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return false.

		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		return this.hasElementContainingRho();
	}

	/**
	 * Checks whether one element of this tuple contains rho.
	 *
	 * @return <code>true</code> iff one tuple element contains rho
	 */
	private boolean hasElementContainingRho() {
		for (Term element : this.elements)
			if (element.findSchema().containsRhoAux()) return true;

		return false;
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
	@Override
	protected boolean isGroundAux() {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.

		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return true;

		return this.hasOnlyGroundElements();
	}

	/**
	 * Checks whether all elements of this tuple are ground.
	 *
	 * @return <code>true</code> iff all tuple elements are ground
	 */
	private boolean hasOnlyGroundElements() {
		for (Term element : this.elements)
			if (!element.findSchema().isGroundAux())
				return false;

		return true;
	}

	/**
	 * Adds the variables of this term to the provided set.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param variables the variable set to complete
	 */
	@Override
	protected void addVariablesTo(Set<Variable> variables) {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// its variables have already been considered.

		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return;

		this.addElementVariablesTo(variables);
	}

	/**
	 * Adds the variables occurring in this tuple's elements to the specified set.
	 *
	 * @param variables the set to complete
	 */
	private void addElementVariablesTo(Set<Variable> variables) {
		for (Term element : this.elements)
			element.findSchema().addVariablesTo(variables);
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
		this.addElementVariableOccurrencesTo(occurrences);
	}

	/**
	 * Adds this tuple's element variable occurrences to the specified mapping.
	 *
	 * @param occurrences the mapping to complete
	 */
	private void addElementVariableOccurrencesTo(
			Map<Variable, Integer> occurrences) {

		for (Term element : this.elements)
			element.getVariableOccurrences(occurrences);
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
	@Override
	protected Set<FunctionSymbol> getFunSymbolsAux() {
		// The set to return at the end of this method.
		HashSet<FunctionSymbol> symbols = new HashSet<>();

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited, and then we have to
		// return an empty set because the set of function
		// symbols of this term has already been considered.

		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return symbols;

		symbols.add(this.getRootSymbol());
		this.addElementFunctionSymbolsTo(symbols);

		return symbols;
	}

	/**
	 * Adds the function symbols occurring in this tuple's elements to the
	 * specified set.
	 *
	 * @param symbols the set to complete
	 */
	private void addElementFunctionSymbolsTo(Set<FunctionSymbol> symbols) {
		for (Term element : this.elements)
			symbols.addAll(element.findSchema().getFunSymbolsAux());
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the subterm of this term at the given single
	 * position.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param elementIndex a single position
	 * @return the subterm of this term at position
	 * <code>i</code>, or <code>null</code> if
	 * <code>i</code> is not a valid position in
	 * this term
	 */
	@Override
	protected Term getAux(int elementIndex) {
		// Check whether elementIndex is out of bounds.
		if (this.isElementIndexOutOfBounds(elementIndex))
			return null;

		return this.elements.get(elementIndex);
	}

	/**
	 * Checks whether the specified index is outside this tuple's elements.
	 *
	 * @param elementIndex the index to check
	 * @return <code>true</code> iff the index does not denote an element of
	 * this tuple
	 */
	private boolean isElementIndexOutOfBounds(int elementIndex) {
		return elementIndex < 0 || this.elements.size() <= elementIndex;
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
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		// 'it' is supposed to have a next element, hence we can
		// safely write this.
		Integer elementIndex = it.next();

		// Check whether elementIndex is out of bounds.
		if (this.isElementIndexOutOfBounds(elementIndex))
			return null;

		return this.elements.get(elementIndex).get(it, shallow);
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
	 *
	 * @return a collection consisting of the hat subterms
	 * of this term
	 */
	@Override
	protected Collection<Term> getHatSubtermsAux() {
		Collection<Term> result = new LinkedList<>();

		this.addElementHatSubtermsTo(result);

		return result;
	}

	/** {@inheritDoc} */
	@Override
	protected boolean containsHatSubtermAux() {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		for (Term element : this.elements)
			if (element.findSchema().containsHatSubtermAux())
				return true;

		return false;
	}

	/**
	 * Adds this tuple's element hat subterms to the specified collection.
	 *
	 * @param target the collection to complete
	 */
	private void addElementHatSubtermsTo(Collection<Term> target) {
		for (Term element : this.elements) {
			Collection<Term> hatSubterms =
					element.findSchema().getHatSubtermsAux();
			addDeepDistinctHatSubterms(target, hatSubterms);
		}
	}

	/**
	 * Adds each candidate hat subterm to the target collection only if no
	 * deeply equal term is already present.
	 *
	 * @param target the collection to complete
	 * @param candidates the candidate hat subterms to add
	 */
	private static void addDeepDistinctHatSubterms(
			Collection<Term> target,
			Collection<Term> candidates) {

		for (Term candidate : candidates)
			if (!containsDeepEqualTerm(target, candidate))
				target.add(candidate);
	}

	/**
	 * Checks whether the specified collection contains a term deeply equal to
	 * the candidate term.
	 *
	 * @param terms the collection to inspect
	 * @param candidate the candidate term
	 * @return <code>true</code> iff a deeply equal term is present
	 */
	private static boolean containsDeepEqualTerm(
			Collection<Term> terms,
			Term candidate) {

		for (Term term : terms)
			if (candidate.deepEquals(term))
				return true;

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
	 * <p>
	 * If the specified term is <code>null</code> then a
	 * collection consisting of the empty position (epsilon)
	 * is returned.
	 *
	 * @param t a term
	 * @param allowVariablePairs <code>true</code> iff disagreement pairs of the
	 * form {@code <variable, variable>} are allowed
	 * @return a collection consisting of the disagreement positions
	 * of this term and the given term
	 */
	@Override
	protected Collection<Position> dposAux(Term t, boolean allowVariablePairs) {
		// We prefer not to support this operation so that
		// the method 'isUnifiableWithAux' in class Term is
		// not supported for Prolog tuples. Indeed, currently
		// the algorithm implemented by this method does not
		// work for Prolog tuples.
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term replaceAux(Iterator<Integer> it, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, each variable with the provided term
	 * <code>t</code>.
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
	 *
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 */
	@Override
	protected Term replaceVariablesAux(Term t) {
		// The term that will be returned at the end.
		PrologTuple copy = new PrologTuple();

		this.addElementsWithVariablesReplacedBy(copy, t);

		return copy;
	}

	/**
	 * Adds this tuple's elements to the target tuple after replacing their
	 * variables with the specified term.
	 *
	 * @param target the tuple to complete
	 * @param replacement the replacing term
	 */
	private void addElementsWithVariablesReplacedBy(
			PrologTuple target,
			Term replacement) {

		for (Term element : this.elements)
			target.addFlattened(element.replaceVariablesAux(replacement));
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
		if (this == t) return true;

		if (!(t instanceof PrologTuple other))
			return false;

		if (this.elements.size() > other.elements.size())
			return false;

		return this.isMoreGeneralThanElements(other, theta);
	}

	/**
	 * Checks whether this tuple is more general than the specified tuple by
	 * comparing elements in iteration order.
	 * <p>
	 * If the specified tuple is longer, the last element of this tuple is
	 * compared with the remaining suffix of the specified tuple.
	 *
	 * @param other the tuple to compare against this tuple
	 * @param theta the substitution to complete
	 * @return <code>true</code> iff all element comparisons succeed
	 */
	private boolean isMoreGeneralThanElements(
			PrologTuple other,
			Substitution theta) {

		Iterator<Term> thisElements = this.elements.iterator();
		Iterator<Term> otherElements = other.elements.iterator();
		while (thisElements.hasNext()) {
			Term thisElement = thisElements.next();
			Term otherElement = otherElements.next();
			if (hasRemainingSuffixAfterCurrentElement(
					thisElements,
					otherElements)) {
				if (!isMoreGeneralThanRemainingTupleSuffix(
						thisElement,
						otherElement,
						otherElements,
						theta))
					return false;
			}
			else if (!thisElement.isMoreGeneralThan(otherElement, theta))
				return false;
		}

		return true;
	}

	/**
	 * Checks whether the specified element is more general than the tuple suffix
	 * formed by the first tail element and the remaining tail elements.
	 *
	 * @param element the element to match against the tuple suffix
	 * @param firstTailElement the first element of the tuple suffix
	 * @param remainingTailElements the remaining elements of the tuple suffix
	 * @param theta the substitution to complete
	 * @return <code>true</code> iff the element is more general than the suffix
	 */
	private static boolean isMoreGeneralThanRemainingTupleSuffix(
			Term element,
			Term firstTailElement,
			Iterator<Term> remainingTailElements,
			Substitution theta) {

		PrologTuple tail = tailTupleFrom(
				firstTailElement,
				remainingTailElements);
		return element.isMoreGeneralThan(tail, theta);
	}

	/**
	 * Checks whether the current element is the last element from the current
	 * sequence while the compared sequence still has a suffix.
	 *
	 * @param currentElements the iterator over the current element sequence
	 * @param remainingElements the iterator over the compared element sequence
	 * @return <code>true</code> iff the compared sequence still has a suffix
	 * after the current element
	 */
	private static boolean hasRemainingSuffixAfterCurrentElement(
			Iterator<Term> currentElements,
			Iterator<Term> remainingElements) {

		return !currentElements.hasNext() && remainingElements.hasNext();
	}

	/**
	 * Builds a tuple from the provided first element and the remaining
	 * elements returned by the iterator.
	 *
	 * @param firstElement the first element of the tuple
	 * @param remainingElements the remaining elements
	 * @return the resulting tuple
	 */
	private static PrologTuple tailTupleFrom(
			Term firstElement,
			Iterator<Term> remainingElements) {

		PrologTuple tail = new PrologTuple();
		tail.add(firstElement);
		while (remainingElements.hasNext())
			tail.add(remainingElements.next());

		return tail;
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
		Term tSchema = t.getSchema();

		if (tSchema instanceof PrologTuple other) {
			s.union(t);
			return this.unifyTupleElements(other);
		}
		else if (tSchema instanceof Variable) {
			s.union(t);
			return true;
		}

		return false;
	}

	/**
	 * The iterators used to unify two tuples by walking the shortest tuple
	 * against the longest one.
	 *
	 * @param shortestElements an iterator over the shortest tuple elements
	 * @param longestElements an iterator over the longest tuple elements
	 */
	private record OrderedTupleElementIterators(
			Iterator<Term> shortestElements,
			Iterator<Term> longestElements) {}

	/**
	 * Tries to unify this tuple's elements with the specified tuple's elements.
	 * <p>
	 * When the longest tuple still has remaining elements, the last element of
	 * the shortest tuple is unified with the corresponding tuple suffix.
	 *
	 * @param other the tuple to unify with this tuple
	 * @return <code>true</code> iff all element unifications succeed
	 */
	private boolean unifyTupleElements(PrologTuple other) {
		OrderedTupleElementIterators iterators =
				this.orderedTupleElementIteratorsFor(other);
		Iterator<Term> shortestElements = iterators.shortestElements();
		Iterator<Term> longestElements = iterators.longestElements();

		while (shortestElements.hasNext()) {
			Term shortestElement = shortestElements.next();
			Term longestElement = longestElements.next();
			if (hasRemainingSuffixAfterCurrentElement(
					shortestElements,
					longestElements)) {
				if (!unifyWithRemainingTupleSuffix(
						shortestElement,
						longestElement,
						longestElements))
					return false;
			}
			else if (!shortestElement.unifyClosure(longestElement))
				return false;
		}

		return true;
	}

	/**
	 * Unifies the specified element with the tuple suffix formed by the first
	 * tail element and the remaining tail elements.
	 *
	 * @param element the element to unify with the tuple suffix
	 * @param firstTailElement the first element of the tuple suffix
	 * @param remainingTailElements the remaining elements of the tuple suffix
	 * @return <code>true</code> iff the element unifies with the suffix
	 */
	private static boolean unifyWithRemainingTupleSuffix(
			Term element,
			Term firstTailElement,
			Iterator<Term> remainingTailElements) {

		PrologTuple tail = tailTupleFrom(
				firstTailElement,
				remainingTailElements);
		return element.unifyClosure(tail);
	}

	/**
	 * Builds iterators positioned at the beginning of the shortest and longest
	 * tuple element sequences.
	 *
	 * @param other the tuple to compare with this tuple
	 * @return iterators over the shortest and longest tuple elements
	 */
	private OrderedTupleElementIterators orderedTupleElementIteratorsFor(
			PrologTuple other) {

		if (this.elements.size() <= other.elements.size())
			return new OrderedTupleElementIterators(
					this.elements.iterator(),
					other.elements.iterator());

		return new OrderedTupleElementIterators(
				other.elements.iterator(),
				this.elements.iterator());
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
		this.visited = true;
		if (!this.hasUnificationSolutionForElements(theta))
			return false;

		this.visited = false;

		return true;
	}

	/**
	 * Checks whether all this tuple's elements have a unification solution.
	 *
	 * @param theta the substitution to complete
	 * @return <code>true</code> iff all element checks succeed
	 */
	private boolean hasUnificationSolutionForElements(Substitution theta) {
		for (Term element : this.elements)
			if (!element.findUnifSolution(theta))
				return false;

		return true;
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term distributeAux(int rho) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term reduceWithLeftUnificationRuleAux(LuEquation equation) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term applyAndCompleteRho(Substitution rho) {
		throw new UnsupportedOperationException();
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
		PrologTuple result = new PrologTuple();

		this.addElementsWithAppliedSubstitutionTo(result, theta);

		return result;
	}

	/**
	 * Adds this tuple's elements to the target tuple after applying the
	 * specified substitution.
	 *
	 * @param target the tuple to complete
	 * @param theta the substitution to apply
	 */
	private void addElementsWithAppliedSubstitutionTo(
			PrologTuple target,
			Substitution theta) {

		for (Term element : this.elements)
			target.addFlattened(element.apply(theta));
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term (which is modified by this method).
	 *
	 * @param theta a substitution
	 */
	@Override
	protected void applyInPlaceAux(Substitution theta) {
		List<Term> updatedElements = this.elementsWithAppliedSubstitution(theta);

		this.elements.clear();
		this.elements.addAll(updatedElements);
	}

	/**
	 * Builds the tuple element list obtained by applying the specified
	 * substitution in place.
	 *
	 * @param theta the substitution to apply
	 * @return the updated element list
	 */
	private List<Term> elementsWithAppliedSubstitution(Substitution theta) {
		List<Term> updatedElements = new LinkedList<>();

		for (Term element : this.elements)
			updatedElements.add(applyInPlaceReplacementFor(element, theta));

		return updatedElements;
	}

	/**
	 * Applies the specified substitution to the provided element, preserving
	 * the current in-place behavior for non-variable elements.
	 *
	 * @param element the tuple element to update
	 * @param theta the substitution to apply
	 * @return the term that must replace the specified element
	 */
	private static Term applyInPlaceReplacementFor(Term element, Substitution theta) {
		if (element instanceof Variable variable) {
			Term replacement = theta.get(variable);
			if (replacement != null)
				return replacement.shallowCopy();
			return element;
		}

		element.applyInPlace(theta);
		return element;
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Collection<Term> rewriteAtInnerPositions(Trs trs) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term unfoldWithAux(RuleTrs rule,
			Iterator<Integer> it,
			boolean dir, boolean unfoldVariablePositions,
			Map<Term,Term> variables) {

		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Iterator<Position> iteratorAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	public Iterator<Position> shallowIterator() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected int depthAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected int maxArityAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 *
	 * @param t a term
	 */
	@Override
	protected boolean embedsAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term rencap(Trs trs, boolean root) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Polynomial toPolynomialAux(PolyInterpretation coefficients) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected void generateKBOWeightsAux(WeightFunction weights) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term toTupleAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term toFunctionAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean lpo1(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean lpo2a(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean lpo2b(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean lpo2c(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Integer getWeightAux(WeightFunction weights) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean kbo2a(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean kbo2b(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean kbo2c(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected void buildFiltersAux(ArgFiltering filtering) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Term applyFiltersAux(ArgFiltering filtering) {
		throw new UnsupportedOperationException();
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
	protected String toStringAux(Map<Variable,String> variables, boolean shallow) {
		StringBuilder result = new StringBuilder("(");
		appendRenderedElements(result, this.elements, variables, shallow);
		result.append(")");

		return result.toString();
	}

	/**
	 * Appends the specified tuple elements to the provided builder, separated
	 * by commas.
	 *
	 * @param result the builder receiving the rendered elements
	 * @param elements the tuple elements to render
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 */
	private static void appendRenderedElements(
			StringBuilder result,
			List<Term> elements,
			Map<Variable,String> variables,
			boolean shallow) {

		int remainingElements = elements.size();

		for (Term element : elements) {
			result.append(element.toString(variables, shallow));
			if (0 < --remainingElements) result.append(",");
		}
	}
}
