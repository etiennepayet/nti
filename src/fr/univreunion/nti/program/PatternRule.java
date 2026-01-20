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

package fr.univreunion.nti.program;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternUtils;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A pattern rule (see [Payet, ICLP'25]), resulting from unfolding a program.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class PatternRule {

	/**
	 * The left-hand side of this pattern rule.
	 */
	private final SimplePatternTerm left;

	/**
	 * The right-hand side of this pattern rule.
	 */
	private final SimplePatternTerm right;

	/**
	 * The iteration of the unfolding operator
	 * at which this rule is generated.
	 */
	private final int iteration;

	/**
	 * A ground nonterminating term generated
	 * from this rule.
	 */
	private final Function nonterminating;

	/**
	 * The <code>alpha</code> threshold of this rule.
	 * For all naturals <code>n >= alpha</code> and
	 * all substitutions <code>theta</code>, 
	 * <code>p(n)theta</code> starts an infinite
	 * computation, where <code>p</code> denotes the
	 * left-hand side of this rule.
	 */
	private final int alpha;

	/**
	 * Attempts to produce a ground nonterminating term
	 * and to compute the <code>alpha</code> threshold
	 * of the rule whose left-hand and right-hand sides
	 * are provided (see Def. 14 and Thm. 5 of
	 * [Payet, ICLP'25]).
	 * 
	 * Upon success, the produced nonterminating term
	 * is returned and the computed <code>alpha</code>
	 * is stored in the first cell of the provided array.
	 * 
	 * Upon failure, <code>null</code> is returned and
	 * <code>-1</code> is stored in the first cell of
	 * the provided array.
	 * 
	 * @param left  the left-hand  of the rule of interest
	 * @param right the right-hand of the rule of interest
	 * @param alpha an array for storing the computed
	 * <code>alpha</code> threshold
	 * @return a ground nonterminating term, or
	 * <code>null</code> if nothing could
	 * be computed
	 */
	private static Function produceNonTerminating(
			SimplePatternTerm left, SimplePatternTerm right, int alpha[]) {

		// The default value for alpha (negative means
		// that no nonterminating term could be produced).
		alpha[0] = -1;

		// We do not consider facts.
		if (right != null) {

			// First, we try to compute alpha directly
			// from left and right.
			int a = computeAlpha(left, right);
			if (a < 0) {
				// Here, we failed to compute alpha
				// from left and right. Hence, we try
				// with refactored versions of left
				// and right.
				SimplePatternTerm[] refactored = refactor(left, right);
				if (refactored != null)
					a = computeAlpha(refactored[0], refactored[1]);
			}

			if (0 <= a) {
				// Here, we succeeded in computing alpha.
				alpha[0] = a;
				Term s = left.valueOf(a);

				Function constant = new Function(
						FunctionSymbol.getInstance("0", 0),
						new LinkedList<>());

				return (Function) s.replaceVariables(constant);
			}
		}

		return null;
	}

	/**
	 * Refactor the provided left-hand side
	 * and right-hand side of a pattern rule.
	 * 
	 * @param left the left-hand side of a pattern rule
	 * @param right the right-hand side of a pattern rule
	 * @return an array storing the refactored
	 * left-hand side and right-hand side
	 */
	private static SimplePatternTerm[] refactor(
			SimplePatternTerm left, SimplePatternTerm right) {

		Term base_l = left.getBaseTerm();
		Term base_r = right.getBaseTerm();
		Substitution theta_l = left.getPatternSubs().getTheta();
		Substitution theta_r = right.getPatternSubs().getTheta();

		Substitution eta = new Substitution();
		if (!base_l.isMoreGeneralThan(base_r, eta))
			return null;

		// From here, base_l is more general than base_r for eta.

		// The substitutions of the refactored pattern terms.
		Substitution theta_l_2 = new Substitution(theta_l);
		Substitution theta_r_2 = new Substitution(theta_r);

		for (Map.Entry<Variable, Term> e : eta) {
			// We consider the next mapping x -> t from eta.
			Variable x = e.getKey();
			Term t = e.getValue();

			if (x == t) continue;

			// If theta_l(x) or theta_r(x) is a hat function
			// then we stop.
			if (left.getPatternSubs().inPumpingDomain(x) ||
					right.getPatternSubs().inPumpingDomain(x))
				return null;

			// From here, x != t and theta_l(x) and
			// theta_r(x) are not hat functions.

			Term c = PatternUtils.getContext(t, x, new int[1]);
			if (c != null) {
				// Here, t = c^a(x) for some ground 1-context c and some natural a.
				// We add x->c^{0,0}(theta_l(x)) and x->c^{0,0}(theta_r(x))
				// to the refactored substitutions.
				HatFunctionSymbol symb = HatFunctionSymbol.getInstance(c, x);
				HatFunction hf_l = new HatFunction(symb, theta_l.getOrDefault(x, x), 0, 0);
				HatFunction hf_r = new HatFunction(symb, theta_r.getOrDefault(x, x), 0, 0);
				theta_l_2.addReplace(x, hf_l);
				theta_r_2.addReplace(x, hf_r);
			}
		}

		SimplePatternSubstitution rho_l = SimplePatternSubstitution.getInstance(theta_l_2);
		SimplePatternSubstitution rho_r = SimplePatternSubstitution.getInstance(theta_r_2);

		if (rho_l == null || rho_r == null) return null;

		SimplePatternTerm[] refactored = new SimplePatternTerm[2];
		refactored[0] = SimplePatternTerm.getInstance(base_l, rho_l);
		refactored[1] = SimplePatternTerm.getInstance(base_r, rho_r);

		return refactored;
	}

	/**
	 * Computes the <code>alpha</code> threshold of the
	 * rule whose components are provided.
	 * 
	 * It is supposed that the rule is not a fact, i.e., 
	 * <code>right</code> is not <code>null</code>.
	 * 
	 * @param left  the left-hand  of the rule of interest
	 * @param right the right-hand of the rule of interest
	 * @return the <code>alpha</code> threshold, or a
	 * negative value in case of failure
	 */
	private static int computeAlpha(
			SimplePatternTerm left, SimplePatternTerm right) {

		Term base_l = left.getBaseTerm();
		Term base_r = right.getBaseTerm();
		Substitution theta_l = left.getPatternSubs().getTheta();
		Substitution theta_r = right.getPatternSubs().getTheta();

		Substitution eta = new Substitution();
		if (base_l.isVariantOf(base_r, eta)) {
			// We check whether base_l is "ground", i.e.,
			// all its variables are included in the domain
			// of theta_l.
			if (theta_l.getDomain().containsAll(base_l.getVariables())) {

				theta_l = theta_l.renameWith(eta);

				int[] coef = checkValidity(theta_l, theta_r);
				if (coef != null)
					return computeAlphaAux(coef);
				else {
					LinearSystem sys = getLinearSystem(theta_l, theta_r);
					if (sys != null && sys.solveGauss())
						return 0;
				}
			}
		}

		return -1;
	}

	/**
	 * Computes the <code>alpha</code> threshold 
	 * from the provided array
	 * <code>coef = [a, a', b, b', d, d', k]</code>,
	 * i.e., the "closest to 0" natural that is greater
	 * than or equal to 
	 * <code>(a * k - (d' - d)) / (a' - a)</code>.
	 * 
	 * @param coef the array <code>[a, a', b, b', d, d', k]</code>
	 * @return the <code>alpha</code> threshold
	 */
	private static int computeAlphaAux(int[] coef) {
		// The value to return at the end.
		int alpha = 0;

		// coef = [a, a', b, b', d, d', k] where a <= a', b <= b' and 0 <= k.

		int a  = coef[0];
		int aa = coef[1]; // a'

		if (a < aa) {
			// We have to compute (a * k - (d' - d)) / (a' - a)
			// and to return the "closest to 0" natural that is
			// greater than or equal to it.

			int numerator = a * coef[6] - (coef[5] - coef[4]);

			if (0 < numerator) {
				int denominator = aa - a;
				// Here, 0 < numerator / denominator. 
				int i = (numerator % denominator == 0 ? 0 : 1);
				alpha = numerator / denominator + i;
			}
			// Else, numerator / denominator <= 0, hence we return 0.
		}
		// Else, alpha = 0.
		// This includes the case where we detected (NT2)
		// i.e., a == aa == -1.

		return alpha;
	}

	/**
	 * Checks whether the provided substitutions are
	 * valid for producing a nonterminating term.
	 * 
	 * @param theta_l the substitution <code>theta</code>
	 * on the left-hand side of this rule
	 * @param theta_r the substitution <code>theta</code>
	 * on the right-hand side of this rule
	 * @return the array <code>[a, a', b, b', d, d', k]</code>
	 * if the substitutions are valid, or <code>null</code>
	 * otherwise
	 */
	private static int[] checkValidity(Substitution theta_l, Substitution theta_r) {

		int a_l = -1, b_l = -1, d_l = -1;
		int a_r = -1, b_r = -1, d_r = -1;
		int e = -1;
		int k = -1;

		// Dom(theta_l) U Dom(theta_r):
		Set<Variable> dom = theta_l.getDomain();
		dom.addAll(theta_r.getDomain());

		// A map for checking the condition:
		// \forall i,j : (t_i \in X \land t_i = t_j) => c_i = c_j.
		Map<Term, Term> map = new HashMap<>();

		// A substitution for checking whether
		// t_i on the left is more general than
		// t_i on the right.
		Substitution rho = new Substitution();

		// We check whether theta_l and theta_r have the required form.
		for (Variable x : dom) {

			int[]  ab_l = new int[2];
			Term[] ct_l = new Term[2];
			getDetails(theta_l.getOrDefault(x, x), x, ab_l, ct_l);

			int[]  ab_r = new int[2];
			Term[] ct_r = new Term[2];
			getDetails(theta_r.getOrDefault(x, x), x, ab_r, ct_r);

			// We check c on the left and c on the right.
			if (!ct_l[0].deepEquals(ct_r[0])) return null;
			// We check t on the left and t on the right.
			Term t = ct_l[1]; 
			if (!t.isMoreGeneralThan(ct_r[1], rho)) return null;

			if (ab_l[0] == 0 && ab_l[1] == 0 && 
					ab_r[0] == 0 && ab_r[1] == 0 &&
					t.isGround())
				// Here, theta_l(x) = c_l^{0,0}(t_l)
				// and   theta_r(x) = c_r^{0,0}(t_r)
				// where t_l = t_r is ground.
				// Hence t_l = t_r is part of the
				// general context c of Def. 14 of
				// [Payet, ICLP'25].
				continue;

			if (t.isVariable()) {
				// We check a on the left and a on the right.
				// We also check d on the left and d on the right.
				if (a_l < 0) {
					// This is the first variable t we encounter. 
					a_l = ab_l[0];
					a_r = ab_r[0];
					if (a_l > a_r) return null;
					d_l = ab_l[1];
					d_r = ab_r[1];
				}					
				else if (ab_l[0] != a_l || ab_r[0] != a_r
						|| ab_l[1] != d_l || ab_r[1] != d_r) return null;
				// We check if the 1-context that embeds t
				// is equal to the 1-contexts that embed t
				// already met before.
				if (!checkVariable(t, ct_l[0], map)) return null;
			}
			else if (t.isGround()) {
				// If ab_l[0] == ab_l[1] == ab_r[0] == ab_r[1] == 0
				// then t is considered as a part of the context c.
				if (ab_l[0] != 0 || ab_l[1] != 0 || ab_r[0] != 0 || ab_r[1] != 0) {
					// We check a on the left and a on the right.
					if (e < 0) {
						// This is the first ground t we encounter.
						e = ab_l[0];
						if (e <= 0 || ab_r[0] != e) return null;
					}
					else if (ab_l[0] != e || ab_r[0] != e) return null;
					// We check b on the left and b on the right.
					if (b_l < 0) {
						// This is the first ground t we encounter.
						b_l = ab_l[1];
						b_r = ab_r[1];
						if (b_l > b_r) return null;
					}
					else if (ab_l[1] != b_l || ab_r[1] != b_r) return null;
				}
			}
			else return null;
		}

		/*
		if (a_l == -1 || a_r == -1 || b_l == -1 || b_r == -1 || d_l == -1 || d_r == -1)
			return null;

		if (a_l == a_r && (d_r - d_l - a_l * (b_r - b_l)) < 0) return null;
		 */

		if (a_l == -1 || a_r == -1 || d_l == -1 || d_r == -1) {
			// Here, we found no variable t. Hence we detect the form (NT2).
			if ((b_r - b_l) % e != 0) return null;
			k = (b_r - b_l) / e; // here, k is a natural
		}
		else if (b_l == -1 || b_r == -1 || e == -1) {
			// Here, we found no ground t. Hence we detect the form (NT1).
			if (a_l == a_r && d_l > d_r) return null;
			k = 0;
		}
		else {
			// Here, we found a ground t and a variable t.
			// Hence we detect the form (NT).
			if ((b_r - b_l) % e != 0) return null;
			k = (b_r - b_l) / e; // here, k is a natural
			if (a_l == a_r && (d_r - d_l - a_l * k) < 0) return null;
		}

		return new int[] {a_l, a_r, b_l, b_r, d_l, d_r, k};
	}

	/**
	 * The term <code>s</code> is supposed to have
	 * the form <code>c^{a,b}(t)</code>. Stores
	 * <code>a</code> and <code>b</code> in the
	 * array <code>ab</code> and <code>c</code>
	 * and <code>t</code> in the array <code>ct</code>.
	 * 
	 * @param s a term of the form <code>c^{a,b}(t)</code>
	 * @param emptyContext the empty context to store
	 * in <code>ct</code> if <code>c</code> is empty
	 * @param ab an array to store <code>a</code> and
	 * <code>b</code>
	 * @param ct an array to store <code>c</code> and
	 * <code>t</code>
	 */
	private static void getDetails(Term s, Variable emptyContext, int[] ab, Term[] ct) {
		if (s instanceof HatFunction) {
			HatFunction hf = (HatFunction) s;
			ab[0] = hf.getA();
			ab[1] = hf.getB();
			ct[0] = hf.getRootSymbol().getSimpleContext();
			ct[1] = hf.getArgument();
		}
		else { // Here, s = emptyContext^{0,0}(s)
			ab[0] = 0;
			ab[1] = 0;
			ct[0] = emptyContext;
			ct[1] = s;
		}		
	}

	/**
	 * Checks if <code>c</code> is equal to the term
	 * associated with <code>s</code> in <code>map</code>.
	 * 
	 * If <code>map</code> has no value for <code>s</code>
	 * then the mapping <code>s -> c</code> is added to it.
	 * 
	 * @param s a term to check
	 * @param c a context to check
	 * @param map a map associating terms to contexts
	 * @return <code>true</code> iff the term
	 * associated with <code>s</code> in <code>map</code>
	 * is equal to <code>c</code> 
	 */
	private static boolean checkVariable(Term s, Term c, Map<Term, Term> map) {
		Term c_s = map.get(s);

		if (c_s != null) return c_s.deepEquals(c);

		map.put(s, c);
		return true;
	}

	/**
	 * Attempts to extract a square linear system of
	 * equations from the provided substitutions.
	 *  
	 * @param theta_l the substitution <code>theta</code>
	 * on the left-hand side of this rule
	 * @param theta_r the substitution <code>theta</code>
	 * on the right-hand side of this rule
	 * @return a square linear system of equations, or
	 * <code>null</code> in case of failure
	 */
	public static LinearSystem getLinearSystem(Substitution theta_l, Substitution theta_r) {
		// Dom(theta_l) U Dom(theta_r):
		Set<Variable> dom = theta_l.getDomain();
		dom.addAll(theta_r.getDomain());

		// The number of rows of the constructed system.
		int n = dom.size();

		// The number of variables of the constructed
		// system (to be computed).
		int p = -1;

		LinkedList<LinkedList<Integer>> ab_l_list = new LinkedList<>();
		LinkedList<LinkedList<Integer>> ab_r_list = new LinkedList<>();

		// We extract the number of variables and
		// the coefficients of the linear system
		// from theta_l and theta_r.
		for (Variable x : dom) {
			LinkedList<Integer> ab_l = new LinkedList<>();
			Term[] ct_l = new Term[2];
			getDetailsAllExponents(theta_l.getOrDefault(x, x), x, ab_l, ct_l);

			LinkedList<Integer> ab_r = new LinkedList<>();
			Term[] ct_r = new Term[2];
			getDetailsAllExponents(theta_r.getOrDefault(x, x), x, ab_r, ct_r);

			// We check c on the left and c on the right
			// (they must be equal).
			if (!ct_l[0].deepEquals(ct_r[0])) return null;
			// We check t on the left and t on the right
			// (they must be ground).
			if (!ct_l[1].isGround() || !ct_r[1].isGround()) return null;

			// We consider the special case where
			// theta_l(x) and theta_r(x) are not
			// hat functions. 
			if (ab_l.isEmpty() && ab_r.isEmpty()) {
				// If t on the left is not equal to
				// t on the right then we give up. 
				if (!ct_l[1].deepEquals(ct_r[1])) return null;
				// Otherwise, we have 
				// theta_l(x) = c_l^{0,...,0}(t_l) and
				// theta_r(x) = c_r^{0,...,0}(t_r)
				// where t_l = t_r is ground.
				// Hence t_l = t_r is part of the
				// general context c of Def. 14 of
				// [Payet, ICLP'25].
				// Hence, x does not correspond to
				// a row of the constructed system,
				// i.e., we decrement n.
				n--;
				continue;
			}

			ab_l_list.add(ab_l);
			ab_r_list.add(ab_r);

			p = Math.max(p, Math.max(ab_l.size() - 1, ab_r.size() - 1));
		}

		// We construct the matrices
		// of the linear system.
		int[][] a = new int[n][];
		int[][] b = new int[n][];

		Iterator<LinkedList<Integer>> it_l = ab_l_list.iterator();
		Iterator<LinkedList<Integer>> it_r = ab_r_list.iterator();
		for (int i = 0; i < n; i++) {
			a[i] = new int[p];
			b[i] = new int[p + 1];

			Iterator<Integer> ab_l = it_l.next().descendingIterator();
			Iterator<Integer> ab_r = it_r.next().descendingIterator();
			b[i][p] = ab_r.next() - ab_l.next();
			for (int j = p - 1; 0 <= j; j--) {
				a[i][j] = ab_l.hasNext() ? ab_l.next() : 0;
				b[i][j] = ab_r.hasNext() ? ab_r.next() : 0;
			}				
		}

		return new LinearSystem(n, p, a, b);
	}

	/**
	 * The term <code>s</code> is supposed to have
	 * the form <code>c^{a_1,...,a_l,b}(t)</code>.
	 * Stores <code>a_1,...,a_l,b</code> in the
	 * list <code>ab</code> and <code>c</code>
	 * and <code>t</code> in the array <code>ct</code>.
	 * 
	 * @param s a term of the form
	 * <code>c^{a_1,...,a_l,b}(t)</code>
	 * @param emptyContext the empty context to store
	 * in <code>ct</code> if <code>c</code> is empty
	 * @param ab a list to store
	 * <code>a_1,...,a_l,b</code>
	 * @param ct an array to store <code>c</code> and
	 * <code>t</code>
	 */
	private static void getDetailsAllExponents(
			Term s, Variable emptyContext, List<Integer> ab, Term[] ct) {

		if (s instanceof HatFunction) {
			HatFunction hf = (HatFunction) s;
			ab.addAll(hf.getExponents());
			ct[0] = hf.getRootSymbol().getSimpleContext();
			ct[1] = hf.getArgument();
		}
		else {
			// Here, s = emptyContext^{0,...,0}(s), i.e.,
			// as many 0's as we want. To reflect that,
			// we make the list ab empty.
			ab.clear();
			ct[0] = emptyContext;
			ct[1] = s;
		}		
	}

	/**
	 * Builds a pattern rule which has the provided
	 * left-hand side and right-hand side.
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @throws IllegalArgumentException if the given
	 * left-hand side is <code>null</code> or if the
	 * given iteration is negative
	 */
	public PatternRule(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		this.left = left;
		this.right = right;
		this.iteration = iteration;
		int[] alpha = new int[1];
		this.nonterminating = produceNonTerminating(left, right, alpha);
		this.alpha = alpha[0];
	}

	/**
	 * Builds a pattern rule from the provided elements.
	 * 
	 * For internal uses only.
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @param nonterminating a ground nonterminating term
	 * generated from this rule
	 * @param alpha the <code>alpha</code> threshold of
	 * this rule
	 */
	protected PatternRule(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration, Function nonterminating, int alpha) {

		this.left = left;
		this.right = right;
		this.iteration = iteration;
		this.nonterminating = nonterminating;
		this.alpha = alpha;
	}

	/**
	 * Returns a deep copy of this pattern rule, i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * 
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this pattern rule
	 */
	public PatternRule deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a deep copy of this pattern rule, i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern rule
	 */
	public abstract PatternRule deepCopy(Map<Term, Term> copies);

	/**
	 * Returns the left-hand side of this pattern rule.
	 * 
	 * @return the left-hand side of this pattern rule
	 */
	public SimplePatternTerm getLeft() {
		return this.left;
	}

	/**
	 * Returns the right-hand side of this pattern rule.
	 * 
	 * @return the right-hand side of this pattern rule
	 */
	public SimplePatternTerm getRight() {
		return this.right;
	}

	/**
	 * Returns the iteration of the unfolding operator
	 * at which this rule is generated.
	 * 
	 * @return the iteration of the unfolding operator
	 * at which this rule is generated
	 */
	public int getIteration() {
		return this.iteration;
	}

	/**
	 * Returns the <code>alpha</code> threshold of this rule.
	 * For all naturals <code>n >= alpha</code> and all
	 * substitutions <code>theta</code>, <code>p(n)theta</code>
	 * starts an infinite computation, where <code>p</code>
	 * denotes the left-hand side of this rule.
	 * 
	 * @return the <code>alpha</code> threshold of this rule
	 */
	public int getAlpha() {
		return this.alpha;
	}

	/**
	 * Returns a ground nonterminating term produced from
	 * this unfolded pattern rule.
	 *  
	 * @return a nonterminating term, or <code>null</code>
	 * if no nonterminating term can be produced from this
	 * rule
	 */
	public Function getNonTerminatingTerm() {
		return this.nonterminating;
	}

	/**
	 * Returns a string representation of this
	 * pattern rule relatively to the given set
	 * of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	public abstract String toString(Map<Variable, String> variables);
	
	/**
	 * Returns a string representation of this
	 * pattern rule.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
