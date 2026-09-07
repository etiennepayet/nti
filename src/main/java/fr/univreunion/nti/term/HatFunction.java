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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
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
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternUtils;

/**
 * A term whose root symbol is a unary symbol of
 * the form <code>c^{a_1,...,a_l,b}</code> where
 * <code>c</code> is a ground 1-context and
 * <code>a_1,...,a_l,b</code> are naturals, with
	 * {@code 0 < l}.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class HatFunction extends Term {

	/**
	 * The child index of this hat function's single argument.
	 */
	private static final int ARGUMENT_INDEX = 0;

	/**
	 * The root symbol of this hat function. It
	 * has the form <code>\hat{c}</code> where
	 * <code>c</code> is a ground 1-context.
	 */
	private final HatFunctionSymbol rootSymbol;

	/**
	 * The exponents <code>a_1,...,a_l,b</code>
	 * of this hat function. This list is not
	 * <code>null</code> and its size is at
	 * least 2.
	 */
	private final LinkedList<Integer> ab = new LinkedList<>();

	/**
	 * The argument of the root symbol.
	 */
	private final Term argument;

	/**
	 * Builds a hat function.
	 * <p>
	 * The provided root symbol has arity 1.
	 * It has the form <code>\hat{c}</code>
	 * where <code>c</code> is a ground 1-context.
	 *
	 * @param rootSymbol the symbol at root position
	 * @param argument the argument (direct son)
	 * of the root symbol
	 * @param a the only exponent <code>a</code> of
	 * this hat function
	 * @param b the exponent <code>b</code> of this
	 * hat function
	 */
	public HatFunction(HatFunctionSymbol rootSymbol, Term argument,
			int a, int b) {

		requireNonNullRootSymbol(rootSymbol);
		requireNonNullArgument(argument);
		requireNonNegativeExponent(a);
		requireNonNegativeExponent(b);

		this.rootSymbol = rootSymbol;
		this.argument = argument;
		this.ab.add(a);
		this.ab.add(b);
	}

	/**
	 * Builds a hat function.
	 * <p>
	 * The provided root symbol has arity 1. It
	 * has the form <code>\hat{c}</code> where
	 * <code>c</code> is a ground 1-context.
	 *
	 * @param rootSymbol the symbol at root position
	 * @param argument the argument (direct son) of the
	 * root symbol
	 * @param exponents the exponents <code>a_1,...,a_l,b</code>
	 * of this hat function; the list contains at least two non-null naturals
	 */
	public HatFunction(HatFunctionSymbol rootSymbol, Term argument,
			List<Integer> exponents) {

		requireNonNullRootSymbol(rootSymbol);
		requireNonNullArgument(argument);
		requireValidExponentList(exponents);

		this.rootSymbol = rootSymbol;
		this.argument = argument;
		this.ab.addAll(exponents);
	}

	/**
	 * Checks that the specified root symbol can be used to build a hat function.
	 *
	 * @param rootSymbol the root symbol to validate
	 * @throws IllegalArgumentException if the root symbol is <code>null</code>
	 */
	private static void requireNonNullRootSymbol(HatFunctionSymbol rootSymbol) {
		if (rootSymbol == null)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a null root symbol");
	}

	/**
	 * Checks that the specified argument can be used to build a hat function.
	 *
	 * @param argument the argument to validate
	 * @throws IllegalArgumentException if the argument is <code>null</code>
	 */
	private static void requireNonNullArgument(Term argument) {
		if (argument == null)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a null argument");
	}

	/**
	 * Checks that the specified exponent can be used to build a hat function.
	 *
	 * @param exponent the exponent to validate
	 * @throws IllegalArgumentException if the exponent is negative
	 */
	private static void requireNonNegativeExponent(int exponent) {
		if (exponent < 0)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a negative exponent");
	}

	/**
	 * Checks that the specified exponent list can be used to build a hat
	 * function.
	 *
	 * @param exponents the exponents to validate
	 * @throws IllegalArgumentException if the list is <code>null</code>, has too
	 * few exponents or contains a <code>null</code> or negative exponent
	 */
	private static void requireValidExponentList(List<Integer> exponents) {
		if (exponents == null || exponents.size() < 2)
			throw new IllegalArgumentException(
					"construction of a HatFunction from an insufficient number of exponents");

		for (Integer exponent : exponents) {
			if (exponent == null)
				throw new IllegalArgumentException(
						"construction of a HatFunction with a null exponent");
			requireNonNegativeExponent(exponent);
		}
	}

	/**
	 * Copy constructor.
	 * <p>
	 * Builds a hat function that has the same root symbol,
	 * argument and exponents as the provided one.
	 *
	 * @param other the hat function to copy
	 */
	public HatFunction(HatFunction other) {
		this.rootSymbol = other.rootSymbol;
		this.argument = other.argument;
		this.ab.addAll(other.ab);
	}

	/**
	 * Indicates whether the provided hat function
	 * has the same exponents as this hat function.
	 *
	 * @param other a hat function with which to compare
	 * @return <code>true</code> iff the provided hat
	 * function has the same exponents as this hat
	 * function
	 */
	public boolean equalExponents(HatFunction other) {
		// This term has the form c^{a_1,...,a_l,b}(u)
		// and other has the form c'^{a'_1,...,a'_l',b'}(v).
		Iterator<Integer> thisExponents = this.ab.descendingIterator(); // we start from b
		Iterator<Integer> otherExponents = other.ab.descendingIterator(); // we start from b'

		while (thisExponents.hasNext() && otherExponents.hasNext())
			if (!thisExponents.next().equals(otherExponents.next()))
				return false;

		return remainingExponentsAreZero(thisExponents) &&
				remainingExponentsAreZero(otherExponents);
	}

	/**
	 * Checks whether every remaining exponent returned by the specified
	 * iterator is equal to zero.
	 *
	 * @param exponents an iterator over exponents
	 * @return <code>true</code> iff every remaining exponent is zero
	 */
	private static boolean remainingExponentsAreZero(
			Iterator<Integer> exponents) {

		while (exponents.hasNext())
			if (exponents.next() != 0)
				return false;

		return true;
	}

	/**
	 * Returns an iterator over the exponents of
	 * this hat function, in reverse sequential
	 * order.
	 * <p>
	 * The iterator traverses a snapshot: modifying it does not modify this hat
	 * function.
	 *
	 * @return an iterator over the exponents
	 * of this hat function in reverse sequence
	 */
	public Iterator<Integer> exponentsDescendingIterator() {
		return new LinkedList<>(this.ab).descendingIterator();
	}

	/**
	 * Returns the root symbol of this function.
	 *
	 * @return the root symbol of this function
	 */
	@Override
	public HatFunctionSymbol getRootSymbol() {
		return this.rootSymbol;
	}

	/**
	 * Returns the argument of this hat function.
	 *
	 * @return the argument of this hat function
	 */
	public Term getArgument() {
		return this.argument;
	}

	/**
	 * Returns the arity of this hat function,
	 * i.e., the integer <code>l</code> if this
	 * hat function has the form
	 * <code>c^{a_1,...,a_l,b}(u)</code>.
	 *
	 * @return the arity of this pattern substitution
	 */
	public int getArity() {
		return this.ab.size() - 1;
	}

	/**
	 * Returns the sum of the exponents corresponding
	 * to the pumping substitutions, i.e.,
	 * <code>a_1 + ... + a_l</code>.
	 *
	 * @return the natural <code>a_1 + ... + a_l</code>
	 * @throws ArithmeticException if the sum cannot be represented as an
	 * <code>int</code>
	 */
	public int getA() {
		int pumpingExponentSum = 0;
		Iterator<Integer> exponents = this.ab.iterator();
		for (int remainingPumpingExponents = this.getArity();
				0 < remainingPumpingExponents;
				remainingPumpingExponents--)
			pumpingExponentSum = Math.addExact(
					pumpingExponentSum, exponents.next());

		return pumpingExponentSum;
	}

	/**
	 * Returns the exponent <code>b</code> of this
	 * hat function.
	 *
	 * @return the exponent <code>b</code> of this
	 * hat function
	 */
	public int getB() {
		return this.ab.getLast();
	}

	/**
	 * Returns a list consisting of the
	 * exponents of this hat function.
	 *
	 * @return a list consisting of the
	 * exponents of this hat function
	 */
	public List<Integer> getExponents() {
		return new LinkedList<>(this.ab);
	}

	/**
	 * Sets the exponent <code>b</code> of this
	 * hat function to the provided value.
	 *
	 * @param b a new value for the exponent
	 * <code>b</code> of this hat function
	 * @throws IllegalArgumentException if {@code b} is negative
	 */
	public void setB(int b) {
		requireNonNegativeExponent(b);
		this.ab.removeLast();
		this.ab.add(b);
	}

	/**
	 * Subtracts the provided term to this hat function.
	 * <p>
	 * More precisely, suppose that this term has the
	 * form <code>c^{a_1,...,a_l,b}(u)</code>.
	 * If the provided term is a hat function of the form
	 * <code>c^{a'_1,...,a'_l',b'}(v)</code> with
	 * {@code a'_i <= a_i} for all {@code i}
	 * and {@code b' <= b} then returns the array
	 * <code>[c^{a_1-a'_1,...,b-b'}(u), v]</code>.
	 * Else, if the provided term is a function of the
	 * form <code>c^k(v)</code> with
	 * {@code 0 < k <= b}
	 * then returns the array
	 * <code>[c^{a_1,...,a_l,b-k}(u), v]</code>.
	 * Else, returns <code>null</code>.
	 *
	 * @param termToSubtract a term to subtract to this hat function
	 * @return the result of subtracting the provided
	 * term to this hat function
	 */
	public Term[] minus(Term termToSubtract) {
		// Suppose that this term has the form c^{a_1,...,a_l,b}(u).

		if (termToSubtract instanceof HatFunction other)
			return this.minusHatFunction(other);

		if (termToSubtract instanceof Function function)
			return this.minusContextTower(function);

		return null;
	}

	/**
	 * Subtracts the specified hat function from this one.
	 *
	 * @param other the hat function to subtract
	 * @return the subtraction result, or <code>null</code> if subtraction fails
	 */
	private Term[] minusHatFunction(HatFunction other) {
		if (this.rootSymbol != other.rootSymbol)
			return null;

		// Here, other has the form c^{a'_1,...,a'_l',b'}(v).
		// We must have a'_i <= a_i for all i and b' <= b.
		LinkedList<Integer> differenceExponents =
				this.subtractExponents(other);
		if (differenceExponents == null)
			return null;

		// Here, we have a'_i <= a_i for all i and b' <= b.
		// We build c^{a_1-a'_1,...,a_l-a'_l,b-b'}(u).
		HatFunction difference = new HatFunction(
				this.rootSymbol, this.argument, differenceExponents);
		return new Term[] { difference, other.argument };
	}

	/**
	 * Subtracts a context tower from this hat function.
	 *
	 * @param function the function that may have the form <code>c^k(v)</code>
	 * @return the subtraction result, or <code>null</code> if subtraction fails
	 */
	private Term[] minusContextTower(Function function) {
		ContextTowerMatch contextTower = this.contextTowerFrom(function);
		if (contextTower.power() <= 0 || this.getB() < contextTower.power())
			return null;

		// Here, function has the form c^k(v).
		// We must have k <= b and we build
		// c^{a_1,...,a_l,b-k}(u).
		LinkedList<Integer> remainingExponents =
				this.withAdjustedLastExponent(-contextTower.power());

		HatFunction difference = new HatFunction(
				this.rootSymbol, this.argument, remainingExponents);
		return new Term[] { difference, contextTower.base() };
	}

	/**
	 * The decomposition of a function as a tower of this hat function's
	 * underlying context.
	 *
	 * @param base the base term under the context tower
	 * @param power the height of the context tower
	 */
	private record ContextTowerMatch(Term base, int power) {}

	/**
	 * Decomposes the specified function as a tower of this hat function's
	 * underlying context.
	 *
	 * @param function the function to decompose
	 * @return the context tower decomposition
	 */
	private ContextTowerMatch contextTowerFrom(Function function) {
		int[] towerHeight = new int[1];
		Term towerBase = PatternUtils.towerOfContexts(
				function,
				this.rootSymbol.getSimpleContext(),
				this.rootSymbol.getVariable(),
				towerHeight);

		return new ContextTowerMatch(towerBase, towerHeight[0]);
	}

	/**
	 * Computes the exponent differences between this hat function and the
	 * specified hat function.
	 *
	 * @param other the hat function whose exponents are subtracted
	 * @return the exponent differences, or <code>null</code> if some
	 * subtracted exponent is too large
	 */
	private LinkedList<Integer> subtractExponents(HatFunction other) {
		LinkedList<Integer> differenceExponents = new LinkedList<>();

		Iterator<Integer> thisExponents = this.ab.descendingIterator(); // we start from b
		Iterator<Integer> otherExponents = other.ab.descendingIterator(); // we start from b'
		while (thisExponents.hasNext() && otherExponents.hasNext()) {
			int thisExponent = thisExponents.next();
			int otherExponent = otherExponents.next();
			if (thisExponent < otherExponent)
				return null;

			differenceExponents.addFirst(thisExponent - otherExponent);
		}

		while (thisExponents.hasNext())
			differenceExponents.addFirst(thisExponents.next());

		if (!remainingExponentsAreZero(otherExponents))
			return null;

		return differenceExponents;
	}

	/**
	 * Computes the sums of this hat function's exponents with the specified
	 * hat function's exponents.
	 *
	 * @param other the hat function whose exponents are added
	 * @return the exponent sums
	 * @throws ArithmeticException if a sum cannot be represented as an
	 * <code>int</code>
	 */
	private LinkedList<Integer> sumExponents(HatFunction other) {
		LinkedList<Integer> sumExponents = new LinkedList<>();

		Iterator<Integer> thisExponents = this.ab.descendingIterator(); // we start from b
		Iterator<Integer> otherExponents = other.ab.descendingIterator(); // we start from b'
		while (thisExponents.hasNext() && otherExponents.hasNext())
			sumExponents.addFirst(Math.addExact(
					thisExponents.next(), otherExponents.next()));

		while (thisExponents.hasNext())
			sumExponents.addFirst(thisExponents.next());

		while (otherExponents.hasNext())
			sumExponents.addFirst(otherExponents.next());

		return sumExponents;
	}

	/**
	 * Returns a copy of this hat function's exponents where the last exponent
	 * <code>b</code> is adjusted by the specified delta.
	 *
	 * @param delta the value to add to the last exponent
	 * @return the adjusted exponents
	 * @throws ArithmeticException if the adjusted exponent cannot be represented
	 * as an <code>int</code>
	 */
	private LinkedList<Integer> withAdjustedLastExponent(int delta) {
		LinkedList<Integer> adjustedExponents = new LinkedList<>();

		Iterator<Integer> currentExponents = this.ab.descendingIterator(); // we start from b
		adjustedExponents.add(Math.addExact(currentExponents.next(), delta));
		while (currentExponents.hasNext())
			adjustedExponents.addFirst(currentExponents.next());

		return adjustedExponents;
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

		if (t instanceof HatFunction other) {
			return this.rootSymbol == other.rootSymbol &&
					this.equalExponents(other) &&
					this.argument.deepEqualsAux1(other.argument);
		}

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * <p>
	 * The returned copy is "flattened", i.e., each
	 * of its subterms is the only element of its
	 * class and is its own schema.
	 * <p>
	 * This term is supposed to be the schema of
	 * its class representative.
	 *
	 * @return a shallow copy of this term
	 */
	@Override
	protected Term shallowCopyAux() {
		return new HatFunction(this.rootSymbol,
				this.argument.shallowCopy(),
				this.ab);
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

		return new HatFunction(this.rootSymbol,
				this.argument.deepCopy(varsToBeCopied, copies),
				this.ab);
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

		return this.argument.containsAux1(t);
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

		return this.argument.findSchema().isGroundAux();
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

		this.argument.findSchema().addVariablesTo(variables);
	}

	/**
	 * Marks this term as visited for the current traversal if needed.
	 *
	 * @return <code>true</code> iff this term had already been visited in the
	 * current traversal
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
		this.argument.getVariableOccurrences(occurrences);
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
	 * <code>childIndex</code>, or <code>null</code> if
	 * <code>childIndex</code> is not a valid position in
	 * this term
	 */
	@Override
	protected Term getAux(int childIndex) {
		// Check whether childIndex is out of bounds.
		if (childIndex != ARGUMENT_INDEX)
			return null;

		return this.getArgument();
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
		Integer childIndex = it.next();

		// Check whether childIndex is out of bounds.
		if (childIndex != ARGUMENT_INDEX)
			return null;

		return this.argument.get(it, shallow);
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

		// We add the hat subterms of the argument to result but only if they do
		// not already occur in result.
		for (Term candidate : this.argument.findSchema().getHatSubtermsAux())
			addIfDeeplyDistinct(result, candidate);

		if (result.isEmpty())
			result.add(this);

		return result;
	}

	/** {@inheritDoc} */
	@Override
	protected boolean containsHatSubtermAux() {
		return true;
	}

	/**
	 * Adds the specified term to the provided collection if no already collected
	 * term is deeply equal to it.
	 *
	 * @param terms the collection to update
	 * @param candidate the term to add if it is deeply distinct
	 */
	private static void addIfDeeplyDistinct(
			Collection<Term> terms,
			Term candidate) {

		if (!containsDeepEqualTerm(terms, candidate))
			terms.add(candidate);
	}

	/**
	 * Checks whether the provided collection contains a term deeply equal to the
	 * specified candidate.
	 *
	 * @param terms the collection to inspect
	 * @param candidate the reference term
	 * @return <code>true</code> iff some collected term is deeply equal to
	 * <code>candidate</code>
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
		// The collection to return at the end.
		Collection<Position> positions = new LinkedList<>();

		if (!(t instanceof HatFunction other) ||
				this.rootSymbol != other.rootSymbol ||
				!this.equalExponents(other)) {

			positions.add(new Position());
			return positions;
		}

		for (Position position :
				this.argument.dpos(other.argument, allowVariablePairs))
			positions.add(position.addFirst(ARGUMENT_INDEX));

		return positions;
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

		if (!(t instanceof HatFunction other) ||
				this.rootSymbol != other.rootSymbol ||
				!this.equalExponents(other))
			return false;

		return this.argument.isMoreGeneralThan(other.argument, theta);
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
		if (!this.argument.findUnifSolution(theta))
			return false;
		this.visited = false;

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term.
	 * <p>
	 * The returned term is "flattened", i.e., each of
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
		Term appliedArgument = this.argument.apply(theta);

		// This term has the form c^{a_1,...,a_l,b}(u)
		// and we have appliedArgument = theta(u).
		// We have to build the term c^{a_1,...,a_l,b}(appliedArgument),
		// which can be simplified in the particular cases
		// considered below.

		if (appliedArgument instanceof HatFunction other) {
			Term simplifiedApplication = this.appliedToHatFunction(other);
			if (simplifiedApplication != null)
				return simplifiedApplication;
		}
		else if (appliedArgument instanceof Function function) {
			Term simplifiedApplication = this.appliedToContextTower(function);
			if (simplifiedApplication != null)
				return simplifiedApplication;
		}

		return new HatFunction(this.rootSymbol, appliedArgument, this.ab);
	}

	/**
	 * Applies this hat function to the specified hat-function argument.
	 *
	 * @param other the applied hat-function argument
	 * @return the simplified application, or <code>null</code> if roots differ
	 */
	private Term appliedToHatFunction(HatFunction other) {
		if (this.rootSymbol != other.rootSymbol)
			return null;

		// Here, other has the form c^{a'_1,...,a'_l',b'}(v).
		// We build the term c^{a_1+a'_1,...,b+b'}(v).
		return new HatFunction(
				this.rootSymbol,
				other.argument,
				this.sumExponents(other));
	}

	/**
	 * Applies this hat function to a context tower.
	 *
	 * @param function the function that may have the form <code>c^k(v)</code>
	 * @return the simplified application, or <code>null</code> if the argument is
	 *         not a positive context tower
	 */
	private Term appliedToContextTower(Function function) {
		ContextTowerMatch contextTower = this.contextTowerFrom(function);
		if (contextTower.power() <= 0)
			return null;

		// Here, function has the form c^k(v).
		// We build the term c^{a_1,...,a_l,b+k}(v).
		return new HatFunction(
				this.rootSymbol,
				contextTower.base(),
				this.withAdjustedLastExponent(contextTower.power()));
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
		return this.rootSymbol.toString() + "^" +
				this.ab +
				"(" +
				this.argument.toString(variables, shallow) +
				")";
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean hasSameStructureAsAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean containsRhoAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected Set<FunctionSymbol> getFunSymbolsAux() {
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
	 * Unsupported operation.
	 */
	@Override
	protected Term replaceVariablesAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 */
	@Override
	protected boolean unifyClosureAux(Term s, Term t) {
		throw new UnsupportedOperationException();
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
			Map<Term, Term> copies) {
		throw new UnsupportedOperationException();
	}

	/**
	 * An iterator over the positions of a hat function.
	 * Only produces the empty position.
	 *
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	private static class HatFunctionIterator implements Iterator<Position> {

		/**
		 * Whether the root position has already been returned.
		 */
		private boolean rootPositionReturned = false;

		/**
		 * Returns <code>true</code> if the iteration has more elements and
		 * <code>false</code> otherwise.
		 *
		 * @return <code>true</code> if the iterator has more elements and
		 *   <code>false</code> otherwise
		 */
		@Override
		public boolean hasNext() {
			return !this.rootPositionReturned;
		}

		/**
		 * Returns the next element in the iteration.
		 *
		 * @return the next element in the iteration
		 * @throws NoSuchElementException when iteration has no more elements
		 */
		@Override
		public Position next() throws NoSuchElementException {
			if (this.rootPositionReturned)
				throw new NoSuchElementException();

			this.rootPositionReturned = true;
			return new Position();
		}

		/**
		 * Unsupported operation.
		 */
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
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
		return new HatFunctionIterator();
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
}
