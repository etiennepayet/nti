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

package fr.univreunion.nti.term;

import java.util.Collection;
import java.util.HashSet;
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
 * <code>0 < l</code>.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class HatFunction extends Term  {

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
	 * 
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

		if (rootSymbol == null)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a null root symbol");
		if (argument == null)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a null argument");
		if (a < 0 || b < 0)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a negative exponent");

		this.rootSymbol = rootSymbol;
		this.argument = argument;
		this.ab.add(a);
		this.ab.add(b);
	}

	/**
	 * Builds a hat function.
	 * 
	 * The provided root symbol has arity 1. It
	 * has the form <code>\hat{c}</code> where
	 * <code>c</code> is a ground 1-context.
	 * 
	 * @param rootSymbol the symbol at root position
	 * @param argument the argument (direct son) of the
	 * root symbol
	 * @param ab the exponents <code>a_1,...,a_l,b</code>
	 * of this hat function
	 */
	public HatFunction(HatFunctionSymbol rootSymbol, Term argument, List<Integer> ab) {

		if (rootSymbol == null)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a null root symbol");
		if (argument == null)
			throw new IllegalArgumentException(
					"construction of a HatFunction with a null argument");
		if (ab == null || ab.size() < 2)
			throw new IllegalArgumentException(
					"construction of a HatFunction from an unsufficient number of exponents");

		for (Integer i : ab)
			if (i < 0)
				throw new IllegalArgumentException("construction of a HatFunction with a negative exponent");

		this.rootSymbol = rootSymbol;
		this.argument = argument;
		this.ab.addAll(ab);
	}

	/**
	 * Copy constructor.
	 * 
	 * Builds a hat function that has the same root symbol,
	 * argument and exponents as the provided one.
	 * 
	 * @param hf the hat function to copy
	 */
	public HatFunction(HatFunction hf) {
		this.rootSymbol = hf.rootSymbol;
		this.argument = hf.argument;
		this.ab.addAll(hf.ab);
	}

	/**
	 * Indicates whether the provided hat function
	 * has the same exponents as this hat function.
	 * 
	 * @param hf a hat function with which to compare
	 * @return <code>true</code> iff the provided hat
	 * function has the same exponents as this hat
	 * function
	 */
	public boolean equalExponents(HatFunction hf) {
		// This term has the form c^{a_1,...,a_l,b}(u)
		// and hf has the form c'^{a'_1,...,a'_l',b'}(v).
		Iterator<Integer> it_this = this.ab.descendingIterator(); // we start from b
		Iterator<Integer> it_hf = hf.ab.descendingIterator(); // we start from b'

		while (it_this.hasNext() && it_hf.hasNext())
			if (!it_this.next().equals(it_hf.next()))
				return false;
		while (it_this.hasNext())
			if (it_this.next() != 0)
				return false;
		while (it_hf.hasNext())
			if (it_hf.next() != 0)
				return false;

		return true;
	}

	/**
	 * Returns an iterator over the exponents
	 * of this hat function, in proper sequence.
	 * 
	 * @return an iterator over the exponents
	 * of this hat function in proper sequence
	 */
	public Iterator<Integer> exponentsIterator() {
		return this.ab.iterator();
	}

	/**
	 * Returns an iterator over the exponents of
	 * this hat function, in reverse sequential
	 * order.
	 * 
	 * @return an iterator over the exponents
	 * of this hat function in reverse sequence
	 */
	public Iterator<Integer> exponentsDescendingIterator() {
		return this.ab.descendingIterator();
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
	 * Returns the exponent <code>a_i</code>.
	 * 
	 * @param i the index of the exponent
	 * @return the exponent at the provided index
	 */
	public int getA(int i) {
		return this.ab.get(i);
	}

	/**
	 * Returns the sum of the exponents corresponding
	 * to the pumping substitutions, i.e.,
	 * <code>a_1 + ... + a_l</code>.
	 * 
	 * @return the natural <code>a_1 + ... + a_l</code>
	 */
	public int getA() {
		// First, we remove the exponent
		// corresponding to the closing
		// substitution (because it will
		// be counted in the loop below).
		int sum = -1 * this.ab.getLast();
		for (Integer a : this.ab)
			sum += a;

		return sum;
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
	 */
	public void setB(int b) {
		this.ab.removeLast();
		this.ab.add(b);
	}

	/**
	 * Subtracts the provided term to this hat function.
	 * 
	 * More precisely, suppose that this term has the
	 * form <code>c^{a_1,...,a_l,b}(u)</code>.
	 * If the provided term is a hat function of the form
	 * <code>c^{a'_1,...,a'_l',b'}(v)</code> with
	 * <code>a'_i <= a_i</code> for all <code>i</code>
	 * and <code>b' <= b</code> then returns the array
	 * <code>[c^{a_1-a'_1,...,b-b'}(u), v]</code>.
	 * Else, if the provided term is a function of the
	 * form <code>c^k(v)</code> with
	 * <code>0 < k <= b</code>
	 * then returns the array
	 * <code>[c^{a_1,...,a_l,b-k}(u), v]</code>.
	 * Else, returns <code>null</code>.
	 * 
	 * @param t a term to subtract to this hat function
	 * @return the result of subtracting the provided
	 * term to this hat function
	 */
	public Term[] minus(Term t) {
		// The hat function to return at the end.
		Term[] result = null;

		// Suppose that this term has the form c^{a_1,...,a_l,b}(u).

		if (t instanceof HatFunction) {
			HatFunction hf = (HatFunction) t; 
			if (this.rootSymbol == hf.rootSymbol) {
				// Here, hf has the form c^{a'_1,...,a'_l',b'}(v).
				// We must have a'_i <= a_i for all i and b' <= b.

				LinkedList<Integer> ab2 = new LinkedList<>(); // the exponents a_i-a'_i and b-b'

				Iterator<Integer> it_this = this.ab.descendingIterator(); // we start from b
				Iterator<Integer> it_hf = hf.ab.descendingIterator(); // we start from b'
				while (it_this.hasNext() && it_hf.hasNext()) {
					int i_this = it_this.next();
					int i_hf = it_hf.next();
					if (i_hf <= i_this) ab2.addFirst(i_this - i_hf);
					else return null;
				}
				while (it_this.hasNext())
					ab2.addFirst(it_this.next());
				while (it_hf.hasNext())
					if (it_hf.next() != 0) return null;

				// Here, we have a'_i <= a_i for all i and b' <= b.
				// We build c^{a_1-a'_1,...,a_l-a'_l,b-b'}(u).
				HatFunction m = new HatFunction(this.rootSymbol, this.argument, ab2);
				result = new Term[] { m, hf.argument };
			}
		}
		else if (t instanceof Function) {
			int n[] = new int[1];
			Term v = PatternUtils.towerOfContexts(
					t, this.rootSymbol.getSimpleContext(), this.rootSymbol.getVariable(), n);
			int k = n[0];
			if (0 < k && k <= this.getB()) {
				// Here, t has the form c^k(v).
				// We must have k <= b and we build
				// c^{a_1,...,a_l,b-k}(u).
				LinkedList<Integer> ab2 = new LinkedList<>();
				Iterator<Integer> it = this.ab.descendingIterator(); // we start from b
				ab2.add(it.next() - k);
				while (it.hasNext()) 
					ab2.addFirst(it.next());

				HatFunction m = new HatFunction(this.rootSymbol, this.argument, ab2);
				result = new Term[] { m, v };
			}
		}

		return result;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether some other term is equal to
	 * this one.
	 * 
	 * This a deep, structural, comparison.
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
	@Override
	protected boolean deepEqualsAux(Term t) {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			if (t instanceof HatFunction) {
				HatFunction hf = (HatFunction) t;
				return this.rootSymbol == hf.rootSymbol &&
						this.equalExponents(hf) &&
						this.argument.deepEqualsAux1(hf.argument);
			}

			return false;
		}

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * 
	 * The returned copy is "flattened", i.e., each
	 * of its subterms is the only element of its
	 * class and is its own schema.
	 * 
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

		return new HatFunction(this.rootSymbol,
				this.argument.deepCopy(varsToBeCopied, copies),
				this.ab);
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
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return false.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			return this.argument.containsAux1(t);
		}

		return false;
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
	@Override
	protected boolean isGroundAux() {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			return this.argument.findSchema().isGroundAux();
		}

		return true;
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
	@Override
	protected Set<Variable> getVariablesAux() {

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return an empty set because the set of variables
		// of this term has already been considered.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			return this.argument.findSchema().getVariablesAux();
		}

		return new HashSet<Variable>();
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
		this.argument.getVariableOccurrences(occurrences);
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
	 * @return the subterm of this term at position
	 * <code>i</code>, or <code>null</code> if
	 * <code>i</code> is not a valid position in
	 * this term
	 */
	@Override
	protected Term getAux(int i) {
		// Check whether i is out of bounds.
		if (i != 0) return null;

		return this.getArgument();
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
	 * or <code>null</code> if the provided iterator does not
	 * correspond to a valid position in this term
	 */
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		// 'it' is supposed to have a next element, hence we can
		// safely write this.
		Integer i = it.next();

		// Check whether i is out of bounds.
		if (i != 0) return null;

		return this.argument.get(it, shallow);
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the hat subterms of this
	 * term.
	 * 
	 * There are no duplicate in the returned collection,
	 * i.e., if s and t are in the returned collection
	 * then they are not equal (w.r.t. a deep, structural,
	 * comparison).
	 *  
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return a collection consisting of the hat subterms
	 * of this term
	 */
	@Override
	protected Collection<Term> getHatSubtermsAux() {
		Collection<Term> result =  new LinkedList<>();

		// We add the elements of result_s to result
		// but only if they do not already occur in
		// result.
		for (Term u : this.argument.findSchema().getHatSubtermsAux()) {
			boolean found = false;
			for (Term v : result)
				if (u.deepEquals(v)) { found = true; break; }
			if (!found) result.add(u);
		}

		if (result.isEmpty()) result.add(this);

		return result;
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
	 * If the specified term is <code>null</code> then a
	 * collection consisting of the empty position (epsilon)
	 * is returned.
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

		if (t instanceof HatFunction) {
			HatFunction hf = (HatFunction) t;
			if (this.rootSymbol == hf.rootSymbol && this.equalExponents(hf))
				for (Position p : this.argument.dpos(hf.argument, var))
					C.add(p.addFirst(0));
			else
				C.add(new Position());
		}
		else
			C.add(new Position());

		return C;
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
		if (this == t) return true;

		if (t instanceof HatFunction) {
			HatFunction hf = (HatFunction) t;
			if (this.rootSymbol == hf.rootSymbol && this.equalExponents(hf))
				return this.argument.isMoreGeneralThan(hf.argument, theta);
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
	 * 
	 * The returned term is "flattened", i.e., each of
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
		Term t = this.argument.apply(theta);

		LinkedList<Integer> ab2 = this.ab;

		// This term has the form c^{a_1,...,a_l,b}(u)
		// and we have t = theta(u).
		// We have to build the term c^{a_1,...,a_l,b}(t),
		// which can be simplified in the particular cases
		// considered below. 

		if (t instanceof HatFunction) {
			HatFunction hf = (HatFunction) t;
			if (this.rootSymbol == hf.rootSymbol) {
				// Here, t has the form c^{a'_1,...,a'_l',b'}(v).
				// We build the term c^{a_1+a'_1,...,b+b'}(v).
				t = hf.argument;

				ab2 = new LinkedList<>();

				Iterator<Integer> it_this = this.ab.descendingIterator(); // we start from b
				Iterator<Integer> it_hf = hf.ab.descendingIterator(); // we start from b'
				while (it_this.hasNext() && it_hf.hasNext()) 
					ab2.addFirst(it_this.next() + it_hf.next());
				while (it_this.hasNext())
					ab2.addFirst(it_this.next());
				while (it_hf.hasNext())
					ab2.addFirst(it_hf.next());
			}
		}
		else if (t instanceof Function) {
			int n[] = new int[1];
			Term v = PatternUtils.towerOfContexts(
					t, this.rootSymbol.getSimpleContext(), this.rootSymbol.getVariable(), n);
			int k = n[0];
			if (0 < k) {
				// Here, t has the form c^k(v).
				// We build the term c^{a_1,...,a_l,b+k}(v).
				t = v;

				ab2 = new LinkedList<>();

				Iterator<Integer> it = this.ab.descendingIterator(); // we start from b
				ab2.add(it.next() + k);
				while (it.hasNext()) ab2.addFirst(it.next());
			}
		}

		return new HatFunction(this.rootSymbol, t, ab2);
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
		StringBuffer s = new StringBuffer(this.rootSymbol.toString());
		s.append("^");
		s.append(this.ab.toString());
		s.append("(");
		s.append(this.argument.toString(variables, shallow));
		s.append(")");

		return s.toString();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean hasSameStructureAsAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean containsRhoAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Set<FunctionSymbol> getFunSymbolsAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term replaceAux(Iterator<Integer> it, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term replaceVariablesAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean unifyClosureAux(Term s, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term distributeAux(int rho) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Term reduceWithAux(LuEquation E) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term applyAndCompleteRho(Substitution rho) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected void applyInPlaceAux(Substitution theta) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Collection<Term> rewriteAtInnerPositions(Trs IR) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term unfoldWithAux(RuleTrs R,
			Iterator<Integer> it,
			boolean dir, boolean var,
			Map<Term, Term> copies) {
		throw new UnsupportedOperationException();
	}

	/**
	 * An iterator over the positions of a hat function.
	 * Only produces the empty position.
	 * 
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	private class HatFunctionIterator implements Iterator<Position> {

		/**
		 * The current argument index of the iterated function.
		 */
		protected int currentIndex = -1;

		/**
		 * Returns <code>true</code> if the iteration has more elements and 
		 * <code>false</code> otherwise.
		 * 
		 * @return <code>true</code> if the iterator has more elements and
		 *   <code>false</code> otherwise
		 */
		@Override
		public boolean hasNext() {
			return currentIndex == -1;
		}

		/**
		 * Returns the next element in the iteration.
		 * 
		 * @return the next element in the iteration
		 * @throws NoSuchElementException when iteration has no more elements
		 */
		@Override
		public Position next() throws NoSuchElementException {
			if (currentIndex != -1)
				throw new NoSuchElementException();

			currentIndex = 0;
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
	 * 
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
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Iterator<Position> shallowIterator() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected int depthAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected int maxArityAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean embedsAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term rencap(Trs IR, boolean root) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Polynomial toPolynomialAux(PolyInterpretation coefficients) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected void generateKBOWeightsAux(WeightFunction weights) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term toTupleAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term toFunctionAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo1(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo2a(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo2b(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo2c(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Integer getWeightAux(WeightFunction weights) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean kbo2a(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean kbo2b(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean kbo2c(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected void buildFiltersAux(ArgFiltering filtering) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term applyFiltersAux(ArgFiltering filtering) {
		throw new UnsupportedOperationException();
	}
}
