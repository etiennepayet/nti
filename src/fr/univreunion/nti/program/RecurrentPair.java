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
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Hole;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A recurrent pair (Omega1, Omega2) for proving non-looping
 * nontermination of a double path program (DPP). The following
 * template is assumed:
 * Omega1 = { C1[D^i u] | i in IN }
 * Omega2 = { C2[D^j u](D^k u) | j,k in IN }
 * where the contexts C1 and D contain the square hole only and
 * the context C2 contains the square hole as well as the circle hole.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RecurrentPair {

	/**
	 * The context C1, which contains the square hole only.
	 */
	private final Function C1;

	/**
	 * The context C2, which contains the square hole as well
	 * as the circle hole.
	 */
	private final Function C2;

	/**
	 * The context D, which contains the square hole only.
	 */
	private final Function D;

	/**
	 * The base term u.
	 */
	private final Term u;

	/**
	 * Static factory method. Tries to build a recurrent
	 * pair from the provided rules.
	 * 
	 * If the provided rules do not form a double path
	 * program (DPP) or if a recurrent pair cannot be
	 * built from them then <code>null</code> is returned.
	 * 
	 * @param l1 the lhs of the first rule of the DPP
	 * @param r1 the rhs of the first rule of the DPP
	 * @param l2 the lhs of the second rule of the DPP
	 * @param r2 the rhs of the second rule of the DPP
	 * @return an instance of <code>RecurrentPair</code>, or
	 * <code>null</code>
	 */
	public synchronized static RecurrentPair getInstance(Function l1, Term r1, Function l2, Term r2) {

		if (r1.isVariable() || r2.isVariable() ||
				!r1.deepCopy().unifyWith(l2.deepCopy()) ||
				!r2.deepCopy().unifyWith(l1.deepCopy()) ||
				!r2.deepCopy().unifyWith(l2.deepCopy()))
			return null;

		// Here, l1, r1, l2 and r2 should have the form p(...)
		// for a same predicate symbol p.

		// We flatten l1 and r1 (i.e., make each subterm the
		// only element of its class and be its own schema).
		Map<Term, Term> copies = new HashMap<Term, Term>();
		l1 = (Function) l1.deepCopy(copies);
		Function rr1 = (Function) r1.deepCopy(copies);
		// We also flatten l2 and r2.
		copies = new HashMap<Term, Term>();
		l2 = (Function) l2.deepCopy(copies);
		Function rr2 = (Function) r2.deepCopy(copies);

		// Now, we try to compute C1, C2, D and u.

		// The symbol p and its arity.
		FunctionSymbol p = l1.getRootSymbol();
		int n = p.getArity();

		for (int i = 0; i < n; i++) {
			// First, we check whether u = s_i is ground.
			Term u = l1.getChild(i), v_i = rr2.getChild(i);
			if (u.isGround() && v_i.isVariable() &&
					l2.nbOccurrences(v_i) == 1 && rr2.nbOccurrences(v_i) == 1) {
				// Then, we check whether i is a decreasing position in R2.
				Function D = decrease(l2, rr2, i);
				if (D != null) {
					// Here, i is a decreasing position in R2.
					// Hence, we check whether (transmit after increase) or
					// (transmit during increase) hold.
					TIresult res;
					if ((res = transmitIncrease(l1, rr1, l2, rr2, i, n, D)) != null &&
							checkJ(res.j, l1, rr1, l2, rr2, i, n, D, u))
						// Here, j is suitable.
						return buildRecPair(l1, rr1, l2, rr2, i, res, D, u, p, n);
				}
			}
		}

		// If we get there, then no recurrent pair could be
		// inferred from R1 and R2.
		return null;
	}

	/**
	 * Computes <code>C1</code> and <code>C2</code> from the
	 * specified arguments and then builds and returns a
	 * recurrent pair from <code>C1</code>, <code>C2</code>,
	 * and the specified <code>D</code> and <code>u</code>.
	 */
	private synchronized static RecurrentPair buildRecPair(
			Function l1, Function r1, Function l2, Function r2,
			int i, TIresult res, Function D, Term u,
			FunctionSymbol p, int n) {

		// Some lists for storing the arguments of C1 and C2:
		List<Term> args_C1 = new LinkedList<Term>();
		List<Term> args_C2 = new LinkedList<Term>();
		
		for (int k = 0; k < n; k++)
			if (k == i) {
				args_C1.add(u); // note that u = l1.getChild(k)
				args_C2.add(D);
			}
			else if (k == res.j) {
				// 0x25A1 is the UFT-16 encoding of
				// the white square character.
				args_C1.add(res.tai ? D : new Hole("" + '\u25A1'));
				// 0x25EF is the UFT-16 encoding of
				// the large white circle character.
				args_C2.add(new Hole("" + '\u25EF'));
			}
			else {
				Term s_k = l1.getChild(k), u_k = l2.getChild(k);
				if (s_k.unifyWith(r1.getChild(k)) && s_k.unifyWith(u_k) && s_k.unifyWith(r2.getChild(k))) {
					args_C1.add(s_k);
					args_C2.add(u_k);
				}
				else
					return null;
			}

		Function C1 = new Function(p, args_C1);
		Function C2 = new Function(p, args_C2);

		return new RecurrentPair(C1, C2, D, u);
	}

	/**
	 * Checks whether the provided rule <code>l -> r</code>
	 * satisfies the (decrease) condition at position
	 * <code>i</code> i.e., <code>l = p(u_0,...,u_n)</code>,
	 * <code>r = p(v_0,...,v_n)</code> and
	 * <code>u_i = D[v_i]</code> for a ground context
	 * <code>D</code> (i.e., the only variable of
	 * <code>D</code> is a hole).
	 *  
	 * @param l the left-hand side of the rule to handle
	 * @param r the right-hand side of the rule to handle
	 * @param i an index in <code>[0,n]</code>
	 * @return the context <code>D</code> if
	 * <code>u_i = D[v_i]</code> and <code>D</code> is
	 * ground, and <code>null</code> otherwise
	 */
	private synchronized static Function decrease(Function l, Function r, int i) {
		Term u_i = l.getChild(i), v_i = r.getChild(i);

		// We check whether u_i = f(..., v_i, ...) i.e.,
		// we only consider the direct children of f,
		// not the inner ones. Moreover, if
		// u_i = f(..., v_i, ..., v_i, ...) i.e., v_i occurs
		// several times in u_i, then only the first occurrence
		// is considered.
		if (u_i instanceof Function) {
			Function f_i = (Function) u_i;
			FunctionSymbol f = f_i.getRootSymbol();
			int m = f.getArity();
			for (int squareHole = 0; squareHole < m; squareHole++)
				if (f_i.getChild(squareHole).deepEquals(v_i))
					// Here, we have u_i = f(..., v_i, ...). Hence,
					// we build D = f(..., square hole, ...).
					return buildContextD(f_i, squareHole, f, m);
		}

		return null;
	}

	/**
	 * Builds the context <code>D</code> from the
	 * specified arguments.
	 * 
	 * @param u_i a function which is equal to
	 * <code>D[v_i]</code> for some <code>v_i</code>
	 * @param squareHole the position of <code>v_i</code> in
	 * <code>u_i</code>, which corresponds to the position of
	 * the square hole in <code>D</code>
	 * @param f the root symbol of <code>u_i</code>
	 * @param m the arity of <code>f</code>
	 * @return the context <code>D</code> if it it ground,
	 * and <code>null</code> otherwise
	 */
	private synchronized static Function buildContextD(
			Function u_i, int squareHole, FunctionSymbol f, int m) {
		// Here, we have u_i = f(...) with m = arity(f) and
		// 0 <= squareHole < m.

		// A list for storing the arguments of D.
		List<Term> args = new LinkedList<Term>();

		Term u_i_j;
		for (int j = 0; j < m; j++)
			if (j == squareHole)
				// 0x25A1 is the UFT-16 encoding of
				// the white square character.
				args.add(new Hole("" + '\u25A1'));
			else if ((u_i_j = u_i.getChild(j)).isGround())
				args.add(u_i_j);
			else
				// Here, D is not ground.
				return null;

		return new Function(f, args);
	}
	
	/**
	 * Checks whether the provided rules <code>l1 -> r1</code>
	 * and <code>l2 -> r2</code> satisfy (transmit after increase)
	 * or (transmit during increase) at position <code>i</code>.
	 * 
	 * More precisely, let 
	 * <code>p(s_0,...,s_n) -> p(t_0,...,t_n) = l1 -> r1</code>,
	 * <code>p(u_0,...,u_n) -> p(v_0,...,v_n) = l2 -> r2</code>.
	 * Suppose that for some <code>j</code>, one of the following
	 * holds:
	 * <ul>
	 *   <li>(transmit after increase) <code>v_j = D^l[u_j]</code>
	 *   and <code>t_i = D^l'[s_j]</code>, with <code>l</code> a
	 *   positive integer and <code>l</code> a non-negative integer</li>
	 *   <li>(transmit during increase) <code>v_j = D^l'[u_j]</code>
	 *   and <code>t_i = D^l[s_j]</code>, with <code>l</code> a
	 *   positive integer and <code>l</code> a non-negative integer</li>
	 * </ul>.
	 * Then <code>(j, true)</code> is returned if (transmit after increase)
	 * holds, <code>(j, false)</code> is returned if (transmit during increase)
	 * holds, and <code>null</code> is returned otherwise.
	 * 
	 * @param l1 the left-hand side of the first rule
	 * @param r1 the right-hand side of the first rule
	 * @param l2 the left-hand side of the second rule
	 * @param r2 the right-hand side of the second rule
	 * @param i the decreasing position
	 * @param n the arity of <code>p</code>
	 * @param D the context of the decreasing position
	 * @return <code>(j, true)</code> if (transmit after increase)
	 * holds at <code>j</code>, or <code>(j, false)</code> if
	 * (transmit during increase) holds at <code>j</code>, or
	 * </code>null</code> otherwise
	 */
	private synchronized static TIresult transmitIncrease(
			Function l1, Function r1, Function l2, Function r2,
			int i, int n, Function D) {

		for (int j = 0; j < n; j++) {
			int tow1 = towerOfContextsD(r1.getChild(i), D, l1.getChild(j));
			int tow2 = towerOfContextsD(r2.getChild(j), D, l2.getChild(j));
			if (0 <= tow1 && 0 < tow2)
				// Here, (transmit after increase) holds.
				return new TIresult(j, true);
			if (0 < tow1 && 0 <= tow2)
				// Here, (transmit during increase) holds.
				return new TIresult(j, false);
		}

		// No suitable j was found. 
		return null;
	}

	/**
	 * Checks whether the given position <code>j</code>
	 * is suitable.
	 * 
	 * @param j the position to be checked
	 * @param l1 the left-hand side of the first rule
	 * @param r1 the right-hand side of the first rule
	 * @param l2 the left-hand side of the second rule
	 * @param r2 the right-hand side of the second rule
	 * @param i the decreasing position
	 * @param n the arity of <code>p</code>
	 * @param D the context of the decreasing position
	 * @param u the base term that has been computed
	 * @return <code>true</code> iff the given position
	 * <code>j</code> is suitable
	 */
	private synchronized static boolean checkJ(int j,
			Function l1, Function r1, Function l2, Function r2,
			int i, int n, Function D, Term u) {

		// We check whether s_j is a variable that occurs
		// only once in l1.
		Term s_j = l1.getChild(j);
		if (!s_j.isVariable() || l1.nbOccurrences(s_j) != 1)
			return false;

		// Here, we know that s_j is a variable. 
		Variable v_s_j = (Variable) s_j;

		// We check whether s_j does not occur in t_k
		// for any k in [1,n] \ {i,j}.
		for (int k = 0; k < n; k++)
			if (k != i && k != j && r1.getChild(k).contains(v_s_j))
				return false;

		// We check whether t_j has the form D^k[s_j] or D^k[u].
		Term t_j = r1.getChild(j);
		if (towerOfContextsD(t_j, D, s_j) < 0 && towerOfContextsD(t_j, D, u) < 0)
			return false;

		// We check whether u_j is a variable that occurs
		// once in l2 and once in r2.
		Term u_j = l2.getChild(j);
		if (!u_j.isVariable() ||
				l2.nbOccurrences(u_j) != 1 || r2.nbOccurrences(u_j) != 1)
			return false;

		return true;
	}

	/**
	 * Checks whether the provided term <code>t</code> has the
	 * form <code>D^l[base]</code> for some <code>l</code>.
	 * If so, then returns <code>l</code>. Otherwise, returns
	 * a negative integer.
	 * 
	 * @param t the term to be checked
	 * @param D the context of the decreasing position
	 * @param base a base term
	 * @return <code>l</code> if it exists, otherwise a
	 * negative integer
	 */
	private synchronized static int towerOfContextsD(Term t, Function D, Term base) {		
		// If t is equal to base, then it is equal to D^0[base].
		if (t.deepEquals(base)) return 0;

		// From here, if l exists, then necessarily 0 < l.
		if (t instanceof Function) {
			Function f_t = (Function) t;
			FunctionSymbol f = f_t.getRootSymbol();
			if (f == D.getRootSymbol()) {
				Term D_k;
				int m = f.getArity();
				int tow = -2;
				for (int k = 0; k < m; k++)
					if ((D_k = D.getChild(k)) instanceof Hole) {
						// This should happen exactly once as D contains one hole.
						if ((tow = towerOfContextsD(f_t.getChild(k), D, base)) < 0)
							return -1;
					}
					else if (!D_k.deepEquals(f_t.getChild(k)))
						return -1;
				return tow + 1;
			}
		}

		return -1;
	}

	/**
	 * Builds a recurrent pair from the provided parameters.
	 * 
	 * @param C1 the context C1, which contains the square hole only
	 * @param C2 the context C2, which contains the square hole as well
	 * as the circle hole
	 * @param D the context D, which contains the square hole only
	 * @param u the base term u
	 */
	private RecurrentPair(Function C1, Function C2, Function D, Term u) {
		this.C1 = C1;
		this.C2 = C2;
		this.D = D;
		this.u = u;
	}

	/**
	 * Returns a nonterminating goal from this
	 * recurrent pair.
	 *  
	 * @return a nonterminating goal
	 */
	public Function getNonTerminatingGoal() {
		// We build the nonterminating goal C1[u].

		// A list for storing the arguments of
		// the nonterminating goal.
		List<Term> args = new LinkedList<Term>();

		// The root symbol of C1 and its arity.
		FunctionSymbol p = this.C1.getRootSymbol();
		int n = p.getArity();

		Term t_i;
		for (int i = 0; i < n; i++)
			if ((t_i = this.C1.getChild(i)) instanceof Hole)
				args.add(this.u);
			else if (t_i == this.D) {
				List<Term> args_D = new LinkedList<Term>();
				FunctionSymbol f = this.D.getRootSymbol();
				int m = f.getArity();
				Term D_j;
				for (int j = 0; j < m; j++)
					if ((D_j = this.D.getChild(j)) instanceof Hole)
						args_D.add(this.u);
					else
						args_D.add(D_j);
				args.add(new Function(f, args_D));
			}
			else
				args.add(t_i);

		return new Function(p, args);
	}

	/**
	 * Returns a string representation of this object.
	 * 
	 * @return a string representation of this object
	 */
	@Override
	public String toString() {
		return
				"<C1 = " + this.C1 +
				", C2 = " + this.C2 +
				// 0x0394 is the UFT-16 encoding of Delta
				// ", " + '\u0394' + " = " + this.D +
				", D = " + this.D +
				", u = " + this.u + ">";
	}
	
	/**
	 * A class for handling the result of method
	 * <code>transmitIncrease</code>.
	 * 
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 *
	 */
	private static class TIresult {
		/**
		 *  The position at which (transmit after increase)
		 *  or (transmit during increase) holds.
		 */
		int j;
		
		/**
		 * <code>true</code> iff (transmit after increase) holds.
		 */
		boolean tai;
		
		/**
		 * Builds a result for method <code>transmitIncrease</code>.
		 * 
		 * @param j the position at which (transmit after increase)
		 *  or (transmit during increase) holds
		 * @param tai <code>true</code> iff (transmit after increase)
		 * holds
		 */
		TIresult(int j, boolean tai) {
			this.j = j;
			this.tai = tai;
		}
	}
}
