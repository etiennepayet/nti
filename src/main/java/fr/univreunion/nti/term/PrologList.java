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
import java.util.ListIterator;
import java.util.Map;
import java.util.NoSuchElementException;
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
 * A Prolog list i.e., [], [e_1,...,e_n], [e_1,...,e_n|L]
 * <p>
 * An object of this class is mutable.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PrologList extends Term {

	/**
	 * The root symbol for a Prolog list.
	 */
	public static final FunctionSymbol PROLOG_LIST_ROOT_SYMBOL =
			FunctionSymbol.intern("|", 2);

	/**
	 * The empty list, as a constant object.
	 */
	private static final PrologList EMPTY_PROLOG_LIST =
			new PrologList((Term) null, null);

	/**
	 * The index of the head child in a non-empty Prolog list.
	 */
	private static final int HEAD_INDEX = 0;

	/**
	 * The index of the tail child in a non-empty Prolog list.
	 */
	private static final int TAIL_INDEX = 1;

	/**
	 * The first element of this Prolog list.
	 */
	private final Term first;

	/**
	 * The tail of this Prolog list.
	 */
	private final Term tail;

	/**
	 * Constructs a Prolog list with the given first
	 * element and tail.
	 *
	 * @param first the first element of this Prolog list
	 * @param tail the tail of this Prolog list
	 */
	private PrologList(Term first, Term tail) {
		this.first = first;
		this.tail = tail;
	}

	/**
	 * Constructs a Prolog list using the given iterator
	 * over a list of elements and the given suffix.
	 * The given iterator must have a next element.
	 *
	 * @param it an iterator over a list of elements
	 * @param suffix the suffix of this Prolog list
	 * @throws NoSuchElementException if <code>it</code>
	 * does not have a next element
	 * @throws NullPointerException if <code>suffix</code>
	 * is <code>null</code> or <code>it.next()</code>
	 * is <code>null</code>
	 */
	private PrologList(ListIterator<Term> it, Term suffix) {
		validateSuffix(suffix);

		this.first = nextNonNullElement(it);
		this.tail = tailFromRemainingElements(it, suffix);
	}

	/**
	 * Validates that the suffix of a constructed Prolog list is non-null.
	 *
	 * @param suffix the suffix to validate
	 * @throws NullPointerException if <code>suffix</code> is <code>null</code>
	 */
	private static void validateSuffix(Term suffix) {
		if (suffix == null)
			throw new NullPointerException("cannot build a Prolog list with a null tail");
	}

	/**
	 * Returns the next non-null element from the specified iterator.
	 *
	 * @param it an iterator over list elements
	 * @return the next element of the iterator
	 * @throws NoSuchElementException if <code>it</code> does not have a next element
	 * @throws NullPointerException if the next element is <code>null</code>
	 */
	private static Term nextNonNullElement(ListIterator<Term> it) {
		Term element = it.next();

		if (element == null)
			throw new NullPointerException("cannot build a Prolog list with a null element");

		return element;
	}

	/**
	 * Builds the tail for the current list node from the remaining iterator
	 * elements or returns the specified suffix when the iterator is exhausted.
	 *
	 * @param it an iterator over the remaining list elements
	 * @param suffix the suffix of the constructed Prolog list
	 * @return the tail of the current list node
	 */
	private static Term tailFromRemainingElements(
			ListIterator<Term> it,
			Term suffix) {

		if (it.hasNext())
			return new PrologList(it, suffix);

		return suffix;
	}

	/**
	 * Returns the empty Prolog list.
	 *
	 * @return the empty Prolog list
	 */
	public static PrologList emptyPrologList() {
		return EMPTY_PROLOG_LIST;
	}

	/**
	 * Checks whether this list is the empty Prolog list singleton.
	 *
	 * @return <code>true</code> iff this list is empty
	 */
	private boolean isEmpty() {
		return this == EMPTY_PROLOG_LIST;
	}

	/**
	 * Constructs a Prolog list with the given elements.
	 * The given list of elements must be non-empty.
	 *
	 * @param elements the elements of this Prolog list
	 * @throws NoSuchElementException if <code>elements</code>
	 * is empty
	 * @throws NullPointerException if an element of
	 * <code>elements</code> is <code>null</code>
	 */
	public PrologList(List<Term> elements) {
		this(elements.listIterator(), EMPTY_PROLOG_LIST);
	}

	/**
	 * Constructs a Prolog list with the given elements
	 * and suffix. The given list of elements must be
	 * non-empty.
	 *
	 * @param elements the elements of this Prolog list
	 * @param suffix the suffix of this Prolog list
	 * @throws NoSuchElementException if <code>elements</code>
	 * is empty
	 * @throws NullPointerException if <code>suffix</code>
	 * is <code>null</code> or an element of <code>elements</code>
	 * is <code>null</code>
	 */
	public PrologList(List<Term> elements, Term suffix) {
		this(elements.listIterator(), suffix);
	}

	/**
	 * Returns the root symbol of this term.
	 *
	 * @return the root symbol of this term
	 */
	@Override
	public FunctionSymbol getRootSymbol() {
		return PROLOG_LIST_ROOT_SYMBOL;
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
	@Override
	protected boolean hasSameStructureAsAux(Term t) {
		return (t instanceof Variable) || (t instanceof PrologList);
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
		// As this != t, if this list is the empty list then
		// t is not, hence we have to return false.
		if (this.isEmpty())
			return false;

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return true;

		if (!(t instanceof PrologList other))
			return false;

		// As this != t, if other is the empty list then
		// this list is not, hence we have to return false.
		if (other.isEmpty())
			return false;

		return this.hasDeepEqualHeadAndTail(other);
	}

	/**
	 * Checks whether this non-empty list and the specified non-empty list have
	 * deeply equal head and tail terms.
	 *
	 * @param other the list to compare with this list
	 * @return <code>true</code> iff both lists have deeply equal head and tail
	 */
	private boolean hasDeepEqualHeadAndTail(PrologList other) {
		return this.first.deepEqualsAux1(other.first) &&
				this.tail.deepEqualsAux1(other.tail);
	}

	/**
	 * Checks whether this list has already been visited during the current
	 * traversal, marking it as visited otherwise.
	 *
	 * @return <code>true</code> iff this list had already been visited
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
		if (this.isEmpty())
			return this;

		return this.shallowCopyNonEmptyList();
	}

	/**
	 * Builds a shallow copy of this non-empty list.
	 *
	 * @return a shallow copy of this non-empty list
	 */
	private PrologList shallowCopyNonEmptyList() {
		return new PrologList(
				this.first.shallowCopy(),
				this.tail.shallowCopy());
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

		if (this.isEmpty())
			return this;

		return this.deepCopyNonEmptyList(varsToBeCopied, copies);
	}

	/**
	 * Builds a deep copy of this non-empty list.
	 *
	 * @param varsToBeCopied a collection of variables that must be copied
	 * @param copies a set of pairs <code>(s,t)</code> where the term
	 * <code>t</code> is a deep copy of <code>s</code>
	 * @return a deep copy of this non-empty list
	 */
	private PrologList deepCopyNonEmptyList(
			Collection<Variable> varsToBeCopied,
			Map<Term,Term> copies) {

		return new PrologList(
				this.first.deepCopy(varsToBeCopied, copies),
				this.tail.deepCopy(varsToBeCopied, copies));
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
		// If this list is the empty list, then we return false.
		// Otherwise, we check whether the first element or the
		// tail of this list contain the provided term.
		if (this.isEmpty())
			return false;

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return false.
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		return this.headOrTailContains(t);
	}

	/**
	 * Checks whether this list's head or tail contains the specified term.
	 *
	 * @param term the term to look for
	 * @return <code>true</code> iff the term occurs in the head or tail
	 */
	private boolean headOrTailContains(Term term) {
		return this.first.containsAux1(term) ||
				this.tail.containsAux1(term);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	@Override
	protected boolean containsRhoAux() {
		// If this list is the empty list, then we return false.
		// Otherwise, we check whether the first element or the
		// tail of this list contain rho.
		if (this.isEmpty())
			return false;

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return false.
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		return this.headOrTailContainsRho();
	}

	/**
	 * Checks whether this list's head or tail contains rho.
	 *
	 * @return <code>true</code> iff rho occurs in the head or tail
	 */
	private boolean headOrTailContainsRho() {
		return this.first.findSchema().containsRhoAux() ||
				this.tail.findSchema().containsRhoAux();
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
		// If this list is the empty list, then we return true.
		// Otherwise, we check whether the first element and
		// the tail of this list are ground.
		if (this.isEmpty())
			return true;

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return true;

		return this.hasOnlyGroundHeadAndTail();
	}

	/**
	 * Checks whether this list's head and tail are ground.
	 *
	 * @return <code>true</code> iff both the head and tail are ground
	 */
	private boolean hasOnlyGroundHeadAndTail() {
		return this.first.findSchema().isGroundAux() &&
				this.tail.findSchema().isGroundAux();
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
		// The empty list has no variable.
		if (this.isEmpty())
			return;

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// its variables have already been considered.
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return;

		this.addHeadAndTailVariablesTo(variables);
	}

	/**
	 * Adds the variables occurring in this list's head and tail to the
	 * specified set.
	 *
	 * @param variables the set to complete
	 */
	private void addHeadAndTailVariablesTo(Set<Variable> variables) {
		this.first.findSchema().addVariablesTo(variables);
		this.tail.findSchema().addVariablesTo(variables);
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
		// If this list is the empty list, then it contains no variable.
		// Otherwise, we count the variables in its first element and
		// in its tail.
		if (this.isEmpty())
			return;

		this.addHeadAndTailVariableOccurrencesTo(occurrences);
	}

	/**
	 * Adds variable occurrences from this list's head and tail to the specified
	 * mapping.
	 *
	 * @param occurrences the mapping to complete
	 */
	private void addHeadAndTailVariableOccurrencesTo(
			Map<Variable, Integer> occurrences) {

		this.first.getVariableOccurrences(occurrences);
		this.tail.getVariableOccurrences(occurrences);
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
		if (this.isEmpty())
			return symbols;

		this.addHeadAndTailFunctionSymbolsTo(symbols);

		return symbols;
	}

	/**
	 * Adds the function symbols occurring in this list's head and tail to the
	 * specified set.
	 *
	 * @param symbols the set to complete
	 */
	private void addHeadAndTailFunctionSymbolsTo(Set<FunctionSymbol> symbols) {
		symbols.addAll(this.first.findSchema().getFunSymbolsAux());
		symbols.addAll(this.tail.findSchema().getFunSymbolsAux());
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the subterm of this term at the given single
	 * position.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param childIndex a single position
	 * @return the subterm of this term at position
	 * <code>i</code>, or <code>null</code> if
	 * <code>i</code> is not a valid position in
	 * this term
	 */
	@Override
	protected Term getAux(int childIndex) {
		if (childIndex == HEAD_INDEX && this.first != null)
			return this.first;

		if (childIndex == TAIL_INDEX && this.tail != null)
			return this.tail;

		return null;
	}

	/**
	 * Returns the subterm at the position specified by the given iterator.
	 *
	 * @param position an iterator over the remaining position
	 * @param shallow whether schema resolution must be skipped below this list
	 * @return the selected subterm, or {@code null} if the position is invalid
	 */
	@Override
	protected Term getAux(Iterator<Integer> position, boolean shallow) {
		Term child = this.getAux(position.next());
		return child == null ? null : child.get(position, shallow);
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

		if (this.isEmpty())
			return result;

		this.addHeadAndTailHatSubtermsTo(result);

		return result;
	}

	/** {@inheritDoc} */
	@Override
	protected boolean containsHatSubtermAux() {
		if (this.isEmpty() || this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		return this.first.findSchema().containsHatSubtermAux() ||
				this.tail.findSchema().containsHatSubtermAux();
	}

	/**
	 * Adds hat subterms from this list's head and tail to the specified
	 * collection.
	 * <p>
	 * The head subterms are added first; tail subterms are then merged without
	 * deep duplicates.
	 *
	 * @param result the collection to complete
	 */
	private void addHeadAndTailHatSubtermsTo(Collection<Term> result) {
		result.addAll(this.first.findSchema().getHatSubtermsAux());

		Collection<Term> tailHatSubterms =
				this.tail.findSchema().getHatSubtermsAux();
		addDeepDistinctHatSubterms(result, tailHatSubterms);
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

		if (!this.deepEquals(t))
			positions.add(new Position());

		return positions;
	}

	/**
	 * Returns a copy of this list in which the subterm at the position specified
	 * by the given iterator is replaced.
	 *
	 * @param position an iterator over the remaining replacement position
	 * @param replacement the replacing term
	 * @return the list containing the replacement
	 * @throws IndexOutOfBoundsException if the position is invalid
	 */
	@Override
	protected Term replaceAux(
			Iterator<Integer> position,
			Term replacement) {
		int childIndex = position.next();
		if (this.isEmpty() ||
				(childIndex != HEAD_INDEX && childIndex != TAIL_INDEX))
			throw new IndexOutOfBoundsException(childIndex + " -- " + this);

		Term replacedHead = childIndex == HEAD_INDEX ?
				this.first.replace(position, replacement) :
				this.first.shallowCopy();
		Term replacedTail = childIndex == TAIL_INDEX ?
				this.tail.replace(position, replacement) :
				this.tail.shallowCopy();
		return new PrologList(replacedHead, replacedTail);
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
		if (this.isEmpty())
			return this;

		return this.withVariablesReplacedBy(t);
	}

	/**
	 * Builds the non-empty list obtained after replacing variables in this
	 * list's head and tail with the specified term.
	 *
	 * @param replacement the replacing term
	 * @return the list with variables replaced
	 */
	private PrologList withVariablesReplacedBy(Term replacement) {
		return new PrologList(
				this.first.replaceVariables(replacement),
				this.tail.replaceVariables(replacement));
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
		if (this == t)
			return true;

		if (!(t instanceof PrologList other))
			return false;

		// As here this != t, if one of this or t is the empty list
		// then we have to return false.
		if (this.isEmpty() || other.isEmpty())
			return false;

		return this.isMoreGeneralThanHeadAndTail(other, theta);
	}

	/**
	 * Checks whether this non-empty list is more general than the specified
	 * non-empty list by comparing their head and tail terms.
	 *
	 * @param other the list to compare against this list
	 * @param theta the substitution to complete
	 * @return <code>true</code> iff both head and tail comparisons succeed
	 */
	private boolean isMoreGeneralThanHeadAndTail(
			PrologList other,
			Substitution theta) {

		return this.first.isMoreGeneralThan(other.first, theta) &&
				this.tail.isMoreGeneralThan(other.tail, theta);
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

		if (tSchema instanceof PrologList targetList)
			return this.unifyClosureWithList(s, t, targetList);
		else if (tSchema instanceof Variable) {
			s.union(t);
			return true;
		}

		return false;
	}

	/**
	 * Tries to unify the represented source term with the specified target list.
	 *
	 * @param s a term whose schema term is this term
	 * @param t a term whose schema term is <code>targetList</code>
	 * @param targetList the target list schema
	 * @return <code>true</code> iff unification succeeds or a cycle is present
	 */
	private boolean unifyClosureWithList(
			Term s,
			Term t,
			PrologList targetList) {

		if (this.isEmpty() && targetList.isEmpty())
			return true;
		if (this.hasDifferentEmptinessThan(targetList))
			return false;

		// Here, both this and targetList are not the empty Prolog list.
		s.union(t);
		return this.unifyNonEmptyListWith(targetList);
	}

	/**
	 * Checks whether exactly one of this list and the specified list is empty.
	 *
	 * @param other the list to compare with this list
	 * @return <code>true</code> iff exactly one list is empty
	 */
	private boolean hasDifferentEmptinessThan(PrologList other) {
		return this.isEmpty() != other.isEmpty();
	}

	/**
	 * Tries to unify this non-empty list's head and tail with those of the
	 * specified non-empty list.
	 *
	 * @param targetList the non-empty list to unify with this list
	 * @return <code>true</code> iff the head and tail unifications succeed
	 */
	private boolean unifyNonEmptyListWith(PrologList targetList) {
		return this.first.unifyClosure(targetList.first) &&
				this.tail.unifyClosure(targetList.tail);
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

		boolean result = this.hasUnificationSolution(theta);

		this.visited = false;

		return result;
	}

	/**
	 * Checks whether this list can provide a unification solution.
	 *
	 * @param theta the substitution to complete
	 * @return <code>true</code> iff a unification solution can be found
	 */
	private boolean hasUnificationSolution(Substitution theta) {
		return this.isEmpty() ||
				(this.first.findUnifSolution(theta)
						&& this.tail.findUnifSolution(theta));
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
		if (this.isEmpty())
			return this;

		return this.withAppliedSubstitution(theta);
	}

	/**
	 * Builds the non-empty list obtained after applying the specified
	 * substitution to this list's head and tail.
	 *
	 * @param theta the substitution to apply
	 * @return the list with the substitution applied
	 */
	private PrologList withAppliedSubstitution(Substitution theta) {
		return new PrologList(
				this.first.apply(theta), this.tail.apply(theta));
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected void applyInPlaceAux(Substitution theta) {
		throw new UnsupportedOperationException();
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
	 * An iterator over this list's positions in root-first prefix order.
	 */
	private final class PrologListIterator implements Iterator<Position> {

		/**
		 * Whether child iterators must avoid schema resolution.
		 */
		private final boolean shallow;

		/**
		 * Whether the root position has already been returned.
		 */
		private boolean rootPositionReturned = false;

		/**
		 * The child currently being traversed.
		 */
		private int childIndex = HEAD_INDEX;

		/**
		 * The iterator over the current child, once initialized.
		 */
		private Iterator<Position> childIterator;

		/**
		 * Builds a deep or shallow list-position iterator.
		 *
		 * @param shallow whether child iterators must be shallow
		 */
		private PrologListIterator(boolean shallow) {
			this.shallow = shallow;
		}

		@Override
		public boolean hasNext() {
			if (!this.rootPositionReturned)
				return true;
			if (PrologList.this.isEmpty() || this.childIndex > TAIL_INDEX)
				return false;
			if (this.childIterator == null || this.childIterator.hasNext())
				return true;
			return this.childIndex < TAIL_INDEX;
		}

		@Override
		public Position next() {
			if (!this.rootPositionReturned) {
				this.rootPositionReturned = true;
				return new Position();
			}

			while (!PrologList.this.isEmpty() &&
					this.childIndex <= TAIL_INDEX) {
				if (this.childIterator == null)
					this.childIterator = this.iteratorForCurrentChild();
				if (this.childIterator.hasNext())
					return this.childIterator.next().addFirst(this.childIndex);

				this.childIndex++;
				this.childIterator = null;
			}

			throw new NoSuchElementException();
		}

		/**
		 * Returns an iterator over the current child.
		 *
		 * @return a deep or shallow iterator over the current child
		 */
		private Iterator<Position> iteratorForCurrentChild() {
			Term child = this.childIndex == HEAD_INDEX ?
					PrologList.this.first : PrologList.this.tail;
			return this.shallow ? child.shallowIterator() : child.iterator();
		}

		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * Returns a deep iterator over this list's positions.
	 *
	 * @return a deep position iterator
	 */
	@Override
	protected Iterator<Position> iteratorAux() {
		return new PrologListIterator(false);
	}

	/**
	 * Returns a shallow iterator over this list's positions.
	 *
	 * @return a shallow position iterator
	 */
	@Override
	public Iterator<Position> shallowIterator() {
		return new PrologListIterator(true);
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
		StringBuilder result = new StringBuilder("[");

		appendRenderedElements(result, this, variables, shallow);

		result.append("]");

		return result.toString();
	}

	/**
	 * Appends the rendered elements and optional final tail of the specified list.
	 *
	 * @param result the builder receiving the rendered list content
	 * @param list the list to render
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 */
	private static void appendRenderedElements(
			StringBuilder result,
			PrologList list,
			Map<Variable,String> variables,
			boolean shallow) {

		boolean firstElement = true;
		PrologList currentList = list;
		while (!currentList.isEmpty()) {
			appendListElement(
					result,
					currentList,
					variables,
					shallow,
					firstElement);
			firstElement = false;

			PrologList nextList = appendTailOrReturnNextList(
					result,
					currentList,
					variables,
					shallow);
			if (nextList == null)
				break;

			currentList = nextList;
		}
	}

	/**
	 * Appends the current list element to the provided builder.
	 *
	 * @param result the builder receiving the rendered element
	 * @param currentList the list whose first element has to be rendered
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @param firstElement whether the rendered element is the first one
	 */
	private static void appendListElement(
			StringBuilder result,
			PrologList currentList,
			Map<Variable,String> variables,
			boolean shallow,
			boolean firstElement) {

		if (!firstElement)
			result.append(",");
		result.append(currentList.first.toString(variables, shallow));
	}

	/**
	 * Appends the current list tail when the traversal must stop, or returns
	 * the next list to visit when the tail schema is another Prolog list.
	 *
	 * @param result the builder receiving the rendered tail when needed
	 * @param currentList the list whose tail has to be processed
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the next list to visit, or <code>null</code> when rendering is done
	 */
	private static PrologList appendTailOrReturnNextList(
			StringBuilder result,
			PrologList currentList,
			Map<Variable,String> variables,
			boolean shallow) {

		if (shallow) {
			appendTail(result, currentList.tail, variables, shallow);
			return null;
		}

		Term tailSchema = currentList.tail.findSchema();
		if (tailSchema instanceof PrologList tailList)
			return tailList;

		appendTail(result, tailSchema, variables, shallow);
		return null;
	}

	/**
	 * Appends a final list tail to the provided builder.
	 *
	 * @param result the builder receiving the rendered tail
	 * @param tail the tail term to render
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 */
	private static void appendTail(
			StringBuilder result,
			Term tail,
			Map<Variable,String> variables,
			boolean shallow) {

		result.append("|");
		result.append(tail.toString(variables, shallow));
	}
}
