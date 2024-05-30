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

package fr.univreunion.nti.program;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Hole;
import fr.univreunion.nti.term.Term;

/**
 * A recurrent pair for proving the existence of a binary loop
 * (see Def. 5.5 of [Payet, JAR'24]).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RecurrentPair {

	/**
	 * The term u1 of this recurrent pair, i.e.,
	 * the left-hand side of the first finite
	 * chain of this recurrent pair.
	 */
	private final Function u1;

	/**
	 * The term v1 of this recurrent pair, i.e.,
	 * the right-hand side of the first finite
	 * chain of this recurrent pair.
	 */
	private final Function v1;

	/**
	 * The term u2 of this recurrent pair, i.e.,
	 * the left-hand side of the second finite
	 * chain of this recurrent pair.
	 */
	private final Function u2;

	/**
	 * The term v2 of this recurrent pair, i.e.,
	 * the right-hand side of the second finite
	 * chain of this recurrent pair.
	 */
	private final Function v2;

	/**
	 * The context c1 of this recurrent pair.
	 */
	private final Term c1;

	/**
	 * The context c2 of this recurrent pair.
	 */
	private final Term c2;

	/**
	 * The term s of this recurrent pair.
	 */
	private final Term s;

	/**
	 * The term t of this recurrent pair
	 * (either equal to s or to a variable).
	 */
	private final Term t;

	/**
	 * The integers m1, m2 of this recurrent pair.
	 */
	private final int m1, m2;

	/**
	 * The integers n1, n2, n3, n4 of this recurrent pair.
	 */
	private final int n1, n2, n3, n4;

	/**
	 * A non-terminating term generated by
	 * this recurrent pair.
	 */
	private final Function nonterminating;


	/**
	 * Static factory method. Tries to build a recurrent
	 * pair from the provided elements.
	 * 
	 * If a recurrent pair cannot be built then
	 * <code>null</code> is returned.
	 * 
	 * @param u1 the lhs of the first  finite chain
	 * @param v1 the rhs of the first  finite chain
	 * @param u2 the lhs of the second finite chain
	 * @param v2 the rhs of the second finite chain
	 * @return a recurrent pair, or <code>null</code>
	 */
	public synchronized static RecurrentPair getInstance(
			Function u1, Term v1, Function u2, Term v2) {

		if (v1.isVariable() || v2.isVariable() ||
				!v1.hasSameStructureAs(u2) ||
				!v2.hasSameStructureAs(u1))
			return null;

		boolean b1 = v1.hasSameStructureAs(u1);
		boolean b2 = v2.hasSameStructureAs(u2);

		if (!(b1 || b2)) return null;

		// Here, u1, v1, u2 and v2 necessarily have the
		// form f(...) for the same function symbol f.

		RecurrentPair result = null;
		if (b1)
			result = buildRecPair(u1, (Function) v1, u2, (Function) v2);
		if (result == null && b2)
			result = buildRecPair(u2, (Function) v2, u1, (Function) v1);

		return result;
	}

	/**
	 * Tries to build a recurrent pair from the
	 * provided elements. If a recurrent pair
	 * cannot be built then <code>null</code>
	 * is returned.
	 * 
	 * The provided terms necessarily have the
	 * form f(...) for the same function symbol f.
	 * 
	 * @param u1 the lhs of the first finite chain
	 * of the built recurrent pair
	 * @param v1 the rhs of the first finite chain
	 * of the built recurrent pair
	 * @param u2 the lhs of the second finite chain
	 * of the built recurrent pair
	 * @param v2 the rhs of the second finite chain
	 * of the built recurrent pair
	 * @return a recurrent pair, or <code>null</code>
	 */
	private synchronized static RecurrentPair buildRecPair(
			Function u1, Function v1, Function u2, Function v2) {

		// We flatten u1 and v1 (i.e., make each subterm the
		// only element of its class and be its own schema).
		Map<Term, Term> copies = new HashMap<Term, Term>();
		u1 = (Function) u1.deepCopy(copies);
		v1 = (Function) v1.deepCopy(copies);

		// We also flatten u2 and v2.
		copies = new HashMap<Term, Term>();
		u2 = (Function) u2.deepCopy(copies);
		v2 = (Function) v2.deepCopy(copies);

		// Here, u1, v1, u2 and v2 necessarily have the
		// form f(...) for the same function symbol f.

		// Now, we try to compute c2, t, i and j.

		// The symbol f and its arity.
		FunctionSymbol f = u1.getRootSymbol();
		int n = f.getArity();

		// We identify the position i
		// of the square hole in c1.
		for (int i = 0; i < n; i++) {
			// First, we check whether u1 = f(...,x1,...) and
			// u2 = f(...,x2,...) where x1 and x2 are variables
			// located at position i and occur only at that
			// position in u1, v1 and u2.
			Term x1 = u1.getChild(i), x2 = u2.getChild(i);
			if (x1.isVariable() && x2.isVariable() &&
					occursOnlyAt(x1, u1,  i, -1, n) &&
					occursOnlyAt(x1, v1, i, -1, n) &&
					occursOnlyAt(x2, u2,  i, -1, n)) {

				// We identify the position j
				// of the square' hole in c1.
				for (int j = 0; j < n; j++)
					if (j != i) {
						Term y1 = v1.getChild(j);
						Term s = u2.getChild(j);

						if (x1 != y1 && y1.isVariable() &&
								occursOnlyAt(y1, u1, -1, j, n) &&
								occursOnlyAt(y1, v1, -1, j, n) &&
								occursOnlyAt(x2, v2, i, j, n)  && 
								s.isGround()) {

							// 0x25A1 is the UFT-16 encoding of
							// the white square character.
							Hole square = new Hole("" + '\u25A1');
							Term c2 = groundContextFrom(u1.getChild(j), y1, square);

							if (c2 != null) {
								int n1 = towerOfContexts(v1.getChild(i), c2, x1);
								// If c2 does not contain any hole then n1 < 0.
								if (0 <= n1) {
									Term t2 = v2.getChild(j);
									int n4 = towerOfContexts(t2, c2, x2);
									if (0 <= n4) {
										Term t1 = v2.getChild(i);
										int n3 = towerOfContexts(t1, c2, x2), m2 = 0;
										Term t = null, sCopy = s;
										if (0 <= n3) t = x2; // Here, m2 = 0 and we have already determined s.
										else {
											n3 = towerOfContexts(t1, c2, s);
											if (0 <= n3) t = s; // Here, m2 = 0 and we have already determined s.
											else {
												m2 = towerOfContexts(s, c2, t1);
												if (0 <= m2 && m2 <= n4) {
													n3 = 0;
													s = t1;
													t = t1;
												}
											}
										}
										if (t != null) {
											// We build the non-terminating term.

											// The arguments of the non-terminating term:
											LinkedList<Term> arguments = new LinkedList<Term>();
											for (int k = 0; k < n; k++)
												if (k == i) arguments.add(s);
												else if (k == j) arguments.add(sCopy);
												else {
													Term l1_k = u1.getChild(k);
													if (!(l1_k.unifyWith(v1.getChild(k)) &&
															l1_k.unifyWith(u2.getChild(k)) &&
															l1_k.unifyWith(v2.getChild(k))))
														// If a non-terminating term cannot be built
														// then we stop because another i or another j
														// will not work. Indeed, at that point, we have
														// u1_j = c2[y] and v1_j = y, i.e., u1_j does not
														// unify with v1_j. We have something similar for i.
														return null;
													arguments.add(l1_k);
												}

											return new RecurrentPair(u1, v1, u2, v2,
													i, j, c2, s, t,
													1, m2, n1, 0, n3, n4,
													new Function(f, arguments));
										}
									}
								}
							}
						}
					}
			}
		}

		return null;
	}

	/**
	 * Checks whether the given term <code>x</code>
	 * occurs only at the given positions <code>i</code>
	 * and <code>j</code> of the given term <code>s</code>.
	 * 
	 * @param x a term whose presence is to be tested
	 * @param s a term where the check occurs
	 * @param i a position at which the presence is allowed
	 * @param j another position at which the presence is allowed
	 * @param n the arity of the function symbol of <code>s</code>
	 * @return <code>true</code> iff <code>x</code>
	 * occurs only at positions <code>i</code>
	 * and <code>j</code> of <code>s</code>
	 */
	private synchronized static boolean occursOnlyAt(
			Term x, Function s, int i, int j, int n) {

		for (int k = 0; k < n; k++)
			if (k != i && k != j && s.getChild(k).contains(x))
				return false;

		return true;
	}

	/**
	 * Checks whether <code>c_y = c[y]</code> for a
	 * <em>ground</em> context <code>c</code> (that
	 * possibly contains several occurrences of the
	 * provided hole). If so, then returns
	 * <code>c</code>, otherwise returns
	 * <code>null</code>.
	 * 
	 * BEWARE: the returned <code>c</code> may
	 * not contain the provided hole. This happens
	 * when <code>c_y</code> is a ground function
	 * that does not contain <code>y</code>.
	 * 
	 * @param c_y the outer term from which a
	 * context is built
	 * @param y the inner term from which a
	 * context is built (supposed to be a variable)
	 * @param square the hole to be used while
	 * building the context
	 * @return a ground context, or <code>null</code>
	 * if no context could be built from the provided
	 * terms
	 */
	private synchronized static Term groundContextFrom(
			Term c_y, Term y, Hole square) {

		if (c_y.isVariable())
			// y is supposed to be a variable, hence the
			// use of ==.
			return (c_y == y ? square : null);

		if (c_y instanceof Function) {
			FunctionSymbol f = c_y.getRootSymbol();
			int n = f.getArity();
			LinkedList<Term> arguments = new LinkedList<Term>();
			for (int k = 0; k < n; k++) {
				Term c_k;
				if ((c_k = groundContextFrom(c_y.get(k), y, square)) == null)
					return null;
				arguments.add(c_k);
			}
			return new Function(f, arguments);
		}

		return null;
	}

	/**
	 * Checks whether the provided term <code>t</code> has the
	 * form <code>c^n[base]</code> for some <code>n</code>.
	 * If so, then returns <code>n</code>. Otherwise, returns
	 * a negative integer.
	 * 
	 * In particular, a negative integer is returned if
	 * <code>c</code> does not contain any hole.
	 * 
	 * @param t a term to be checked
	 * @param c a context (possibly with several holes)
	 * @param base a base term
	 * @return <code>n</code> if it exists, otherwise a
	 * negative integer
	 */
	private synchronized static int towerOfContexts(Term t, Term c, Term base) {		
		// If t is equal to base, then it is equal to c^0[base].
		if (t.deepEquals(base)) return 0;

		FunctionSymbol f = t.getRootSymbol();
		if (f == c.getRootSymbol()) {
			Term c_k;
			int n = f.getArity();
			int tow = -2;
			for (int k = 0; k < n; k++)
				if ((c_k = c.get(k)) instanceof Hole) {
					int tow_k;
					if ((tow_k = towerOfContexts(t.get(k), c, base)) < 0)
						return -1;
					// If this is the first instance of a hole
					// we encounter, then we set tow to tow_k.
					if (tow < 0) tow = tow_k;
					// Otherwise, we check whether tow_k is
					// equal to the value obtained with the
					// previous holes.
					else if (tow != tow_k) return -1;
				}
				else if (!c_k.deepEquals(t.get(k)))
					return -1;
			return tow + 1;
		}

		return -1;
	}

	/**
	 * Builds a recurrent pair from the provided elements.
	 * 
	 * @param u1 the left-hand  side of the first finite chain
	 * @param v1 the right-hand side of the first finite chain
	 * @param u2 the left-hand  side of the second finite chain
	 * @param v2 the right-hand side of the second finite chain
	 * @param i the position of the square hole
	 * @param j the position of the square' hole
	 * @param c2 the context c2
	 * @param s the term s
	 * @param t the term t
	 * @param m1 the integer m1
	 * @param m2 the integer m2
	 * @param n1 the integer n1
	 * @param n2 the integer n2
	 * @param n3 the integer n3
	 * @param n4 the integer n4
	 * @param nonterminating a non-terminating term
	 * generated by this recurrent pair
	 */
	private RecurrentPair(Function u1, Function v1, Function u2, Function v2,
			int i, int j, Term c2, Term s, Term t,
			int m1, int m2,
			int n1, int n2, int n3, int n4,
			Function nonterminating) {

		this.u1 = u1;
		this.v1 = v1;
		this.u2 = u2;
		this.v2 = v2;

		// We build c1 from u1, i and j.
		// 0x25A1 is the UFT-16 encoding of
		// the white square character.
		Hole square = new Hole("" + '\u25A1');
		Hole squarePrime = new Hole('\u25A1' + "'");
		FunctionSymbol f = u1.getRootSymbol();
		int n = f.getArity();
		LinkedList<Term> arguments = new LinkedList<Term>();
		for (int k = 0; k < n; k++) {
			if (k == i) arguments.add(square);
			else if (k == j) arguments.add(squarePrime);
			else arguments.add(u1.getChild(k));
		}
		this.c1 = new Function(f, arguments);
		this.c2 = c2;

		this.s  = s;
		this.t  = t;

		this.m1 = m1;
		this.m2 = m2;

		this.n1 = n1;
		this.n2 = n2;
		this.n3 = n3;
		this.n4 = n4;

		this.nonterminating = nonterminating;
	}

	/**
	 * Returns the left-hand side of the first
	 * finite chain of this recurrent pair.
	 */
	public Function getLeft1() {
		return this.u1;
	}

	/**
	 * Returns the right-hand side of the first
	 * finite chain of this recurrent pair.
	 */
	public Function getRight1() {
		return this.v1;
	}

	/**
	 * Returns the left-hand side of the second
	 * finite chain of this recurrent pair.
	 */
	public Function getLeft2() {
		return this.u2;
	}

	/**
	 * Returns the right-hand side of the second
	 * finite chain of this recurrent pair.
	 */
	public Function getRight2() {
		return this.v2;
	}

	/**
	 * Returns the context c1
	 * of this recurrent pair.
	 */
	public Term getContextC1() {
		return this.c1;
	}

	/**
	 * Returns the context c2
	 * of this recurrent pair.
	 */
	public Term getContextC2() {
		return this.c2;
	}

	/**
	 * Returns the ground term s of
	 * this recurrent pair.
	 */
	public Term getS() {
		return this.s;
	}

	/**
	 * Returns the term t of
	 * this recurrent pair.
	 */
	public Term getT() {
		return this.t;
	}

	/**
	 * Returns the integer m1 of
	 * this recurrent pair.
	 */
	public int getM1() {
		return this.m1;
	}

	/**
	 * Returns the integer m2 of
	 * this recurrent pair.
	 */
	public int getM2() {
		return this.m2;
	}

	/**
	 * Returns the integer n1 of
	 * this recurrent pair.
	 */
	public int getN1() {
		return this.n1;
	}

	/**
	 * Returns the integer n2 of
	 * this recurrent pair.
	 */
	public int getN2() {
		return this.n2;
	}

	/**
	 * Returns the integer n3 of
	 * this recurrent pair.
	 */
	public int getN3() {
		return this.n3;
	}

	/**
	 * Returns the integer n4 of
	 * this recurrent pair.
	 */
	public int getN4() {
		return this.n4;
	}

	/**
	 * Returns a nonterminating term from this
	 * recurrent pair.
	 *  
	 * @return a nonterminating term
	 */
	public Function getNonTerminatingTerm() {
		return this.nonterminating;
	}
}
