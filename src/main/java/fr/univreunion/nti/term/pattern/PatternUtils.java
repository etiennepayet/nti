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

package fr.univreunion.nti.term.pattern;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A set of methods for manipulating pattern terms. 
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternUtils {

	/**
	 * Returns the term <code>c^n(t)</code>, which 
	 * results from embedding <code>c</code>
	 * <code>n</code> times into itself.
	 *  
	 * @param c a 1-context whose hole
	 * is <code>x</code>
	 * @param x the unique variable of c
	 * @param n the number of embeddings of c
	 * @param t the base term
	 * @return the term <code>c^n(t)</code>
	 */
	public synchronized static Term embed(Term c, Variable x, int n, Term t) {
		Term result = null;

		if (0 < n) { 
			Substitution theta = new Substitution();
			theta.add(x, c);

			result = c.shallowCopy(); // result = c^1(x)
			for (int i = 1; i < n; i++)
				// Here, result = c^i(x).
				result.applyInPlace(theta); // Here, result = c^{i+1}(x).

			// Here, result = c^n(x).

			theta.addReplace(x, t);
			result.applyInPlace(theta); // this makes a shallow copy of t
			// Here, result = c^n(t).	
		}
		else result = t.shallowCopy();

		return result;
	}

	/**
	 * Tries to compute the smallest ground 1-context
	 * <code>c</code> such that <code>s = c^a(x)</code>
	 * for some natural <code>a</code>. 
	 * 
	 * Only contexts of the following form are considered:
	 * <code>f(t_1,...,t_n)</code> where each <code>t_i</code>
	 * is <code>x</code> or does not contain <code>x</code>.
	 * 
	 * Upon success, this method stores the computed exponent
	 * <code>a</code> in the first cell of the provided array.
	 * 
	 * @param s a term
	 * @param x a variable occurring in <code>s</code>
	 * @param a an array for storing the computed exponent 
	 * <code>a</code>
	 * @return the computed context, or <code>null</code>
	 * if no context could be computed
	 */
	public synchronized static Term getContext(Term s, Variable x, int[] a) {

		a[0] = 0;

		if (s == x) return s;

		if (s.isVariable() || !s.getVariables().contains(x))
			return null;
			/*
			throw new IllegalArgumentException(
					"cannot get a ground context from a variable that is different from the specified one");
					*/

		// From here, s is not a variable
		// and s contains x.

		FunctionSymbol f = s.getRootSymbol();
		int m = f.getArity();

		// The arguments of the context we build.
		LinkedList<Term> arguments = new LinkedList<>();

		// First, we complete the argument list of the context.
		Term s_hole = null; // the term occurring in every hole
		for (int k = 0; k < m; k++) {
			Term s_k = s.get(k);
			if (s_k.isGround())
				// s_k is ground: it does not correspond to a hole.
				arguments.add(s_k);
			else {
				// s_k is not ground: it corresponds to a hole.
				arguments.add(x);
				if (s_hole == null)
					// This is the first instance of a hole
					// we encounter. So, we set s_hole.
					s_hole = s_k;
				else
					// Otherwise, we check whether s_k
					// is equal to the term occurring
					// in the previous holes.
					if (!s_k.deepEquals(s_hole))
						return null;
			}
		}

		// Then, we build the context. It has the form
		// f(t_1,...,t_n) where each t_i is x or is a
		// ground term.
		Function c = new Function(f, arguments);

		// Finally, we compute the number of times
		// the context is embedded into itself.
		a[0] = towerOfContexts(s_hole, c, x, x) + 1; // we add 1 because s = c(s_hole)
		if (a[0] <= 0) return null;

		return c;
	}
	/* THIS VERSION RETURNS A 1-CONTEXT THAT IS NOT NECESSARILY GROUND:
	public synchronized static Term getContext(Term s, Variable x, int[] a) {

		a[0] = 0;

		if (s == x) return s;

		if (s.isVariable())
			// Here, x does not occur in s.
			throw new IllegalArgumentException(
					"cannot get a context from a variable that is different from the specified one");

		// From here, s is not a variable.

		FunctionSymbol f = s.getRootSymbol();
		int m = f.getArity();

		// The arguments of the context we build.
		LinkedList<Term> arguments = new LinkedList<>();

		// First, we complete the argument list of the context.
		Term s_hole = null; // the term occurring in every hole
		for (int k = 0; k < m; k++) {
			Term s_k = s.get(k);
			if (!s_k.contains(x))
				// s_k does not contain x: it does not correspond to a hole
				arguments.add(s_k);
			else {
				// s_k contains x: it corresponds to a hole.
				arguments.add(x);
				if (s_hole == null)
					// This is the first instance of a hole
					// we encounter. So, we set s_hole.
					s_hole = s_k;
				else
					// Otherwise, we check whether s_k
					// is equal to the term occurring
					// in the previous holes.
					if (!s_k.deepEquals(s_hole))
						return null;
			}
		}

		// Then, we build the context. It has the form
		// f(t_1,...,t_n) where each t_i is x or is a
		// term that does not contain x.
		Function c = new Function(f, arguments);

		// Finally, we compute the number of times
		// the context is embedded into itself.
		a[0] = towerOfContexts(s_hole, c, x, x) + 1; // we add 1 because s = c(s_hole)
		if (a[0] <= 0) return null;

		return c;
	}
	 */

	/**
	 * Computes a simplified version of the specified term
	 * relatively to the specified substitution.
	 * 
	 * It is supposed that the domain of <code>theta</code>
	 * is included in the set of variables of <code>s</code>.
	 * 
	 * The mappings of <code>theta</code> of the form
	 * <code>x -> c^{a_1,...,a_l,b}(t)</code> are considered. 
	 * Suppose that there are naturals <code>k</code>
	 * such that each occurrence of <code>x</code> in
	 * <code>s</code> appears in <code>c^k(x)</code>.
	 * Then, we consider the maximum <code>k'</code> of
	 * these <code>k</code>'s: all occurrences of
	 * <code>c^k(x)</code> in <code>s</code> are
	 * replaced, in a copy of <code>s</code>, by
	 * <code>x</code> and
	 * <code>x -> c^{a_1,...,a_l,b}(t)</code>
	 * in <code>theta</code> is replaced by
	 * <code>x -> c^{a_1,...,a_l,b+k'}(t)</code>.
	 * 
	 * The term <code>s</code> is not modified by
	 * this method. On the contrary, the mappings
	 * of <code>theta</code> may be modified as
	 * explained above.
	 * 
	 * @param s the term to simplify
	 * @param theta the substitution to use for the
	 * simplification
	 * @return the simplified term
	 */
	public synchronized static Term simplify(Term s, Substitution theta) {
		// The term to return at the end.
		Term new_s = s;

		Map<Variable, Map<Position, Integer>> map = getTowers(s, theta);

		for (Map.Entry<Variable, Term> e : theta) {
			// We get the next mapping x -> theta_x from theta.
			Term theta_x = e.getValue();

			if (theta_x instanceof HatFunction) {
				// Here, theta_x has the form c^{a_1,...,a_l,b}(t).
				Variable x = e.getKey();

				Map<Position, Integer> map_x = map.get(x);
				int min_x = min(map_x);
				if (0 <= min_x) {
					HatFunction theta_x_hat = (HatFunction) theta_x.shallowCopy();
					theta_x_hat.setB(theta_x_hat.getB() + min_x);
					e.setValue(theta_x_hat);

					for (Map.Entry<Position, Integer> e_x : map_x.entrySet())
						new_s = replace(new_s, e_x.getKey(), x, e_x.getValue(), min_x);
				}
			}
		}

		return new_s;
	}

	/**
	 * Checks whether <code>s = c^a(t)</code> for some
	 * natural <code>a</code>.
	 * 
	 * If <code>c</code> is the empty context (i.e.,
	 * <code>c == x_c</code>) then 0 is returned.
	 * 
	 * The terms <code>s</code>, <code>c</code> and
	 * <code>t</code> are not modified by this method.
	 * 
	 * @param s a term to be checked
	 * @param c a 1-context
	 * @param x_c the hole of <code>c</code>
	 * @param t a base term
	 * @return <code>a</code> if it exists, otherwise a
	 * negative integer
	 */
	public synchronized static int towerOfContexts(
			Term s, Term c, Variable x_c, Term t) {

		if (s == null || c == null || x_c == null || t == null)
			return -1;
		
		// If s is equal to t or c is empty
		// then a = 0.
		if (s.deepEquals(t) || c == x_c) return 0;

		FunctionSymbol f = s.getRootSymbol();

		if (f == c.getRootSymbol()) {
			Term s_hole = null;
			int a = -1;
			int m = f.getArity();
			for (int k = 0; k < m; k++) {
				Term c_k = c.get(k);
				Term s_k = s.get(k);
				if (c_k == x_c) {
					// Here, c_k is a hole in c.
					if (s_hole == null) {
						// This is the first instance of a hole
						// we encounter. So, we set s_hole and a.
						s_hole = s_k; // this is what the other holes should contain
						a = towerOfContexts(s_hole, c, x_c, t);
						if (a < 0) return -1;
					}
					else 
						// Otherwise, we check whether s_k
						// is equal to the term occurring
						// in the previous holes.
						if (!s_k.deepEquals(s_hole)) return -1;
				}
				else
					// Here, c_k is not a hole in c. Hence,
					// c_k and s_k should be equal.
					if (!c_k.deepEquals(s_k)) return -1;
					// if (!c_k.isVariantOf(s_k)) return -1; // BEWARE: IS THAT CORRECT?
			}

			// Here, we have recognized c.
			return a + 1; // we add 1 because s = c(s_hole) with s_hole = c^a(t)
		}

		return -1;
	}

	/**
	 * Computes the integer <code>b</code> and the term
	 * <code>t</code> such that <code>s = c^b(t)</code>
	 * with <code>t \neq c(...)</code>. Then,
	 * <code>t</code> is returned and <code>n[0]</code>
	 * is set to <code>b</code>.
	 * 
	 * If <code>c</code> is the empty context
	 * (i.e., it is equal to <code>x_c</code>)
	 * then <code>s</code> is returned and
	 * <code>n[0]</code> is set to <code>0</code>.
	 * 
	 * The terms <code>s</code> and <code>c</code>
	 * are not modified by this method.
	 * 
	 * @param s the term of interest
	 * @param c a 1-context
	 * @param x_c the unique variable of <code>c</code>
	 * @param n an array that is used to store the
	 * computed integer <code>b</code>
	 * @return the term <code>t</code>
	 */
	public synchronized static Term towerOfContexts(Term s, Term c, Variable x_c, int[] n) {

		n[0] = 0;

		// If c is the empty context then
		// we return s.
		if (c == x_c) return s;

		FunctionSymbol f = s.getRootSymbol();

		// If we do not recognize c
		// then we return s = c^0(s).
		if (f != c.getRootSymbol()) return s;

		Term s_hole = null;
		Term t = null; // the term to return

		int m = f.getArity();
		for (int k = 0; k < m; k++) {
			Term s_k = s.get(k);
			Term c_k = c.get(k);
			if (c_k == x_c) {
				// Here, c_k is a hole in c.
				if (s_hole == null) {
					// This is the first instance of a hole
					// we encounter. So, we set s_hole, t
					// and n.
					s_hole = s_k; // this is what the other holes should contain
					t = towerOfContexts(s_hole, c, x_c, n);
				}

				else
					// Otherwise, we check whether s_k
					// is equal to the term occurring
					// in the previous holes.
					if (!s_k.deepEquals(s_hole)) {
						// Here, we have not recognized c.
						// So, we return s = c^0(s).
						n[0] = 0;
						return s;
					}
			}
			else
				// Here, c_k is not a hole in c. Hence,
				// c_k and s_k should be equal.
				if (!c_k.deepEquals(s_k)) {
					// Here, we have not recognized c.
					// So, we return s = c^0(s).
					n[0] = 0;
					return s;
				}
		}

		// Here, we have recognized c.
		n[0] = n[0] + 1; // we add 1 because s = c(s_hole) with s_hole = c^{n[0]}(t)
		return t;
	}

	/**
	 * Returns the minimum value in the specified map.
	 * 
	 * It is supposed that each mapping <code>(p -> i)</code>
	 * in the specified map is such that <code>i</code> is a
	 * natural.
	 * 
	 * A negative value is returned if the provided map 
	 * is empty.
	 * 
	 * @param map a map from positions to naturals
	 * @return the minimum value in the map, or a
	 * negative integer if the map is empty
	 */
	private synchronized static int min(Map<Position, Integer> map) {
		int min = -1;
		for (Map.Entry<Position, Integer> e : map.entrySet())
			min = (min < 0 ? e.getValue() : Math.min(min, e.getValue()));

		return min;
	}

	/**
	 * Returns the term obtained from <code>s</code> by
	 * replacing the subterm at position <code>p</code>
	 * by <code>c^{a - min}(x)</code>, where
	 * <code>c</code> is the 1-context such that
	 * <code>s|p = c^a(x)</code>.
	 * 
	 * The term <code>s</code> is not modified by this
	 * method.
	 * 
	 * @param s the term where the replacement takes place
	 * @param p the position of the replacement
	 * @param x the unique variable of the context <code>c</code> 
	 * @param a the exponent of <code>c</code> in <code>s|p</code>
	 * @param min the minimum value of the exponents of
	 * <code>c</code> in <code>s</code>
	 * @return the term resulting from the replacement
	 */
	private synchronized static Term replace(Term s, Position p, Variable x, int a, int min) {
		// The term to return at the end.
		Term new_s = s;

		if (a == min)
			// Here, s|p = c^{min}(x), so we replace
			// s|p by x.
			new_s = new_s.replace(p, x);
		else {
			// Here, s|p = c^a(x) with a > min.
			Term s_p = s.get(p); // s_p = s|p
			int m = s_p.getRootSymbol().getArity();
			Term new_s_p_k = null;
			for (int k = 0; k < m; k++) {
				Term s_p_k = s_p.get(k);
				if (s_p_k.contains(x)) {
					// Necessarily, s_p_k = c^{a-1}(x)
					if (new_s_p_k == null)
						new_s_p_k = replace(s_p_k, new Position(), x, a - 1, min);
					new_s = new_s.replace(p.addLast(k), new_s_p_k);
				}
			}
		}

		return new_s;
	}

	/**
	 * If <code>theta(x) = c^{a_1,...,a_l,b}(t)</code> then,
	 * for all occurrences of <code>x</code> in <code>s</code>,
	 * computes the maximum natural <code>k</code> such that
	 * <code>c^k</code> embeds the occurrence.
	 * 
	 * It is supposed that the domain of <code>theta</code>
	 * is included in the set of variables of <code>s</code>.
	 * 
	 * The returned data structure maps each <code>x</code>
	 * such that <code>theta(x) = c^{a_1,...,a_l,b}(t)</code>
	 * to a set of mappings of the form <code>p -> k</code>
	 * where <code>p</code> is the position of an occurrence
	 * of <code>x</code> in <code>s</code> and <code>k</code>
	 * is the maximum natural as described above.
	 * 
	 * The term <code>s</code> and the substitution
	 * <code>theta</code> are not modified by this method.
	 * 
	 * @param s the term to examine
	 * @param theta a substitution whose domain is 
	 * the set of variables of <code>s</code>
	 * @return a map as described above
	 */
	private synchronized static Map<Variable, Map<Position, Integer>> getTowers(Term s, Substitution theta) {
		// The map that will be returned.
		Map<Variable, Map<Position, Integer>> map = new HashMap<>();

		// We consider every mapping of the form
		// x -> c^{a_1,...,a_l,b}(t) in theta. 
		for (Map.Entry<Variable, Term> e : theta) {
			// We get the next mapping x -> theta_x from theta.
			Term theta_x = e.getValue();

			if (theta_x instanceof HatFunction) {
				// Here, theta_x has the form c^{a_1,...,a_l,b}(t).
				HatFunctionSymbol c_hat = ((HatFunction) theta_x).getRootSymbol();
				Variable x = e.getKey();
				map.put(x, getTowersAux(s, x,
						c_hat.getSimpleContext(), c_hat.getVariable()));
			}
		}

		return map;
	}

	/**
	 * Computes a set of mappings of the form <code>p -> k</code>
	 * where <code>p</code> is the position of an occurrence
	 * of <code>x</code> in <code>s</code> and <code>k</code>
	 * is the maximum natural such that <code>c^k</code> embeds
	 * the occurrence.
	 * 
	 * The terms <code>s</code> and <code>c</code> are not
	 * modified by this method.
	 * 
	 * @param s the term to examine
	 * @param x the variable to consider in <code>s</code>
	 * @param c a 1-context
	 * @param x_c the hole of <code>c</code>
	 * @return a set of mappings as described above
	 */
	private synchronized static Map<Position, Integer> getTowersAux(Term s, Variable x, Term c, Variable x_c) {
		// The map that will be returned.
		Map<Position, Integer> map = new HashMap<>();

		// We check whether s has the form c^a(x).
		int a = towerOfContexts(s, c, x_c, x);

		if (0 <= a)
			// Here, s = c^a(x). We add (epsilon -> a) to the map.
			map.put(new Position(), Integer.valueOf(a));
		else {
			// Otherwise, we run this method recursively
			// on every direct subterm of s.
			int m = s.getRootSymbol().getArity();
			for (int k = 0; k < m; k++) {
				Term s_k = s.get(k);
				Map<Position, Integer> map_k = getTowersAux(s_k, x, c, x_c);
				for (Map.Entry<Position, Integer> e : map_k.entrySet()) {
					Position p = e.getKey().addFirst(k);
					map.put(p, e.getValue());
				}
			}
		}

		return map;
	}
}
