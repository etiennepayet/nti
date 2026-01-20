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

package fr.univreunion.nti.term.pattern.simple;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.program.lp.nonloop.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.PatternTerm;
import fr.univreunion.nti.term.pattern.PatternUtils;

/**
 * A simple pattern term, i.e., a pattern term
 * <code>(s, eta)</code> such that 
 * <code>eta = (sigma_1, ..., sigma_l, mu)</code>
 * with, for all <code>x \in Var(s)</code>,
 * <code>sigma_i(x) = c^{a_i}(x)</code> and
 * <code>mu(x) = c^b(u)</code> for
 * some 1-context <code>c</code>,
 * some <code>a_1,...,a_l,b \in \nat</code> and
 * some <code>u \in T(Sigma,X)</code>.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class SimplePatternTerm extends PatternTerm implements Iterable<Position> {

	/**
	 * An element of <code>upsilon(p)</code>, where
	 * <code>p</code> denotes this pattern term.
	 */
	private final Term upsilon;

	/**
	 * Builds a simple pattern term from the specified elements.
	 * 
	 * <b>It is supposed that <code>eta</code> has the correct
	 * form for building simple pattern terms (NOT CHECKED)</b>.
	 * 
	 * @param t the base term of this pattern term
	 * @param eta the pattern substitution of this pattern term
	 * @param upsilon the term <code>upsilon(p)</code> where
	 * <code>p</code> denotes this pattern term
	 */
	private SimplePatternTerm(Term t, SimplePatternSubstitution eta, Term upsilon) {
		super(t, eta);
		this.upsilon = upsilon;
	}

	/**
	 * Static factory method.
	 * 
	 * Builds a simple pattern term from the specified elements.
	 * 
	 * <b>It is supposed that <code>sigma</code> only consists
	 * of mappings of the form <code>x -> c(x)</code> where
	 * <code>c</code> is a simple context whose hole is
	 * <code>x</code> (NOT CHECKED)</b>.
	 * 
	 * @param t the base term of this pattern term
	 * @param sigma the pumping substitution of this pattern term
	 * @param mu the closing substitution of this pattern term
	 * @return a simple pattern term, or <code>null</code>
	 * if no pattern term could be constructed from the
	 * specified elements
	 */
	public static SimplePatternTerm getInstance(
			Term t, Substitution sigma, Substitution mu) {

		SimplePatternSubstitution theta =
				SimplePatternSubstitution.getInstance(Arrays.asList(sigma, mu));

		if (theta != null)
			return getInstance(t, theta);

		return null;
	}

	/**
	 * Static factory method.
	 * 
	 * Builds a simple pattern term from the specified
	 * elements.
	 * 
	 * BEWARE: the mappings of eta may be modified
	 * by this method.
	 * 
	 * @param t the base term of this pattern term
	 * @param eta the pattern substitution of this
	 * pattern term
	 * @return a simple pattern term, or <code>null</code>
	 * if no pattern term could be constructed from the
	 * specified elements
	 */
	public static SimplePatternTerm getInstance(
			Term t, PatternSubstitution eta) {

		if (eta instanceof SimplePatternSubstitution) {
			SimplePatternSubstitution rho = (SimplePatternSubstitution) eta;

			Substitution sigma = rho.getTheta().restrictTo(t.getVariables());
			// If t is a function f(t_1,...,t_n), then we move all ground
			// t_i's to sigma, i.e., we replace t_i by a new variable x_i
			// and we add x_i -> t_i to sigma:
			t = t.toSubstitution(sigma);
			// Then, we simplify t and sigma:
			t = PatternUtils.simplify(t, sigma); // also simplifies sigma
			// Finally, we compute upsilon:
			Term upsilon = t.apply(sigma);

			SimplePatternSubstitution theta = SimplePatternSubstitution.getInstance(sigma);
			if (theta != null)
				return new SimplePatternTerm(t, theta, upsilon);
		}

		return null;
	}

	/**
	 * Static factory method.
	 * 
	 * Builds the simple pattern term <code>t^*</code>.
	 * 
	 * @param t the base term of this pattern term
	 * @return a simple pattern term
	 */
	public static SimplePatternTerm getInstance(Term t) {
		return new SimplePatternTerm(t, SimplePatternSubstitution.getInstance(), t);
	}

	/**
	 * Returns a deep copy of this pattern term, i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * 
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this pattern term
	 */
	@Override
	public SimplePatternTerm deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a deep copy of this pattern term, i.e.,
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
	 * @return a deep copy of this pattern term
	 */
	@Override
	public SimplePatternTerm deepCopy(Map<Term, Term> copies) {
		return new SimplePatternTerm(this.getBaseTerm().deepCopy(copies),
				this.getPatternSubs().deepCopy(copies),
				this.upsilon.deepCopy(copies));
	}

	/**
	 * Returns the subterm of this pattern term
	 * at the given position.
	 * 
	 * @param p a position
	 * @return the subterm of this pattern term
	 * at position <code>p</code>, or
	 * <code>null</code> if <code>p</code> is not
	 * a valid position in this pattern term
	 */
	public SimplePatternTerm get(Position p) {
		Term base_p = this.getBaseTerm().get(p);

		if (base_p == null) return null;

		return SimplePatternTerm.getInstance(base_p, this.getPatternSubs());
	}

	/**
	 * Returns the term <code>upsilon(p)</code> where
	 * <code>p</code> denotes this pattern term.
	 * 
	 * @return <code>upsilon(p)</code> where
	 * <code>p</code> denotes this pattern term
	 */
	public Term getUpsilon() {
		return this.upsilon;
	}

	/**
	 * Returns the pattern substitution of
	 * this simple pattern term.
	 * 
	 * @return the pattern substitution of
	 * this simple pattern term
	 */
	@Override
	public SimplePatternSubstitution getPatternSubs() {
		// The pattern substitution of this simple pattern term
		// should be simple (see the constructors of this class).
		return (SimplePatternSubstitution) super.getPatternSubs();
	}
	
	/**
	 * Computes the values to use to weaken
	 * this pattern term w.r.t. the provided
	 * one.
	 * 
	 * It is supposed that the arity of this
	 * pattern term and that of <code>p</code>
	 * are both equal to 1.
	 * 
	 * @param p a pattern term for weakening
	 * this pattern term
	 * @return the values to use for weakening
	 */
	public int[] getWeakeningValues(SimplePatternTerm p) {

		int i_fun = -1;
		int i_hat = -1;

		// We consider the disagreement positions of this
		// pattern term and p.
		for (Position pos : p.upsilon.dpos(this.upsilon, true)) {
			Term this_pos = this.upsilon.get(pos);
			Term p_pos    = p.upsilon.get(pos);
			if (this_pos instanceof HatFunction) {
				HatFunction hf1 = (HatFunction) this_pos;

				HatFunctionSymbol g = hf1.getRootSymbol();
				int a1 = hf1.getA();
				int b1 = hf1.getB();
				// Here, this_pos = c^{a1,b1}(u1).
				if (p_pos instanceof Function) {
					int n[] = new int[1];
					Term u = PatternUtils.towerOfContexts(
							p_pos, g.getSimpleContext(), g.getVariable(), n);
					int k = n[0];
					if (0 < k && b1 < k) {
						// Here, p_pos = c^k(u), i.e., p_pos = c^{0,k}(u).
						// As 0 <= a1, we should have k <= b1.
						int kb1 = k - b1;
						if (kb1 % a1 != 0) return null;
						int i = kb1 / a1;
						if (i_fun < 0) i_fun = i;
						else if (i != i_fun) return null;
					}
					else if (k == 0 && b1 == 0 && u.deepEquals(hf1.getArgument()))
						// Here, we have p_pos = u and this_pos = c^{a1,0}(u).
						i_fun = 0;
				}
				else if (p_pos instanceof HatFunction) {
					if (g == p_pos.getRootSymbol()) {
						HatFunction hf2 = (HatFunction) p_pos;

						int a2 = hf2.getA();
						int b2 = hf2.getB();
						// Here, p_pos = c^{a2,b2}(u2).
						if (a2 <= a1 && b1 < b2) {
							int b2b1 = b2 - b1;
							int d = (b2b1 % a1 == 0 ? 0 : 1);
							i_hat = Math.max(i_hat, b2b1 / a1 + d);
						}
					}
				}
			}
		}

		return new int[] {i_fun, i_hat}; 
	}

	/**
	 * Checks whether this simple pattern term is
	 * more general than the specified one.
	 * 
	 * @param p a simple pattern term
	 * @return <code>true</code> iff this pattern term
	 * is more general than the specified one
	 */
	public boolean isMoreGeneralThan(SimplePatternTerm p) {
		return this.upsilon.isMoreGeneralThan(p.upsilon);
	}

	/**
	 * Checks if this pattern term is a variable.
	 * 
	 * @return <code>true</code> iff this pattern
	 * term is a variable
	 */
	public boolean isVariable() {
		return this.upsilon.isVariable();
	}

	/**
	 * Returns an iterator over the positions of
	 * this pattern term.
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<Position> iterator() {
		return this.getBaseTerm().iterator();
	}

	/**
	 * Attempts to compute the most general unifier of
	 * this pattern term and the provided one.
	 * 
	 * This method implements the unification algorithm
	 * described in [Payet, ICLP'25].
	 * 
	 * Neither this pattern term nor the provided one are
	 * modified by this method.
	 * 
	 * @param p a pattern term
	 * @return the most general unifier of this pattern
	 * term and the provided one, or <code>null</code>
	 * in case of failure
	 */
	@Override
	public SimplePatternSubstitution unifyWith(SimplePatternTerm p) {
		// We try to unify upsilon(p) and upsilon(this_term).
		Substitution theta = new Substitution();
		if (this.upsilon.isUnifiableWith(p.upsilon, theta))
			return SimplePatternSubstitution.getInstance(theta);

		return null;
	}

	/**
	 * Attempts to compute the most general unifier of this
	 * pattern term with the left-hand side of the provided
	 * pattern rule. If the provided rule is a fact (i.e.,
	 * its right-hand side is empty), then also attempts to
	 * compute the most general unifier of this pattern term
	 * with weakened versions of the left-hand side of the
	 * provided rule.
	 * 
	 * Neither this pattern term nor the provided pattern
	 * rule are modified by this method.
	 * 
	 * @param r a pattern rule
	 * @return a collection of most general unifiers
	 */
	@Override
	public Collection<SimplePatternSubstitution> unifyWith(PatternRuleLp r) {

		// The value to return at the end.
		Collection<SimplePatternSubstitution> result = new LinkedList<>();

		// First, we try to unify this pattern term
		// with the left-hand side of r.
		SimplePatternSubstitution theta = this.unifyWith(r.getLeft());

		if (theta != null)
			// If success then we consider theta.
			result.add(theta);

		// We also try to weaken r and to unify
		// this pattern term with the computed
		// weakened terms.
		Substitution rho = new Substitution();
		for (Term weak : r.weakenLeftIfFact(this)) {
			if (this.upsilon.isUnifiableWith(weak, rho)) {
				SimplePatternSubstitution eta = SimplePatternSubstitution.getInstance(rho);
				if (eta != null) result.add(eta);
			}
			rho.clear();
		}

		return result;
	}
	
	/**
	 * Performs the following actions.
	 * <ol>
	 * <li>
	 * Replaces each mapping
	 * <code>x -> c^{a,b}(u)</code> in the
	 * simple pattern substitution of this
	 * pattern term by
	 * <code>x -> c^{a,a*i_hat+b}(u)</code>.
	 * Indeed,
	 * <code>c^{a,a*i_hat+b}(u)</code>
	 * describes the set
	 * <code>{c^{a*n+a*i_hat+b}(u) | n \in \nat}</code>
	 * = <code>{c^{a*(n+i_hat)+b}(u) | n \in \nat}</code>
	 * = <code>{c^{a*n+b}(u) | n >= i_hat}</code>
	 * which is included in
	 * <code>{c^{a*n+b}(u) | n \in \nat}</code>.
	 * </li>
	 * 
	 * <li>Replaces each mapping
	 * <code>x -> c^{a,b}(u)</code> in the
	 * simple pattern substitution of this
	 * pattern term by
	 * <code>x -> c^{a,a,a*i_hat+b}(u)</code>.
	 * Indeed,
	 * <code>c^{a,a,a*i_hat+b}(u)</code>
	 * describes the set
	 * <code>{c^{a*n+a*m+a*i_hat+b}(u) | n,m \in \nat}</code>
	 * = <code>{c^{a*(n+m+i_hat)+b}(u) | n,m \in \nat}</code>
	 * = <code>{c^{a*n+b}(u) | n >= i_hat}</code>
	 * which is included in
	 * <code>{c^{a*n+b}(u) | n \in \nat}</code>.
	 * </li>
	 * </ol>
	 * 
	 * This pattern term (hence its pattern
	 * substitution) are not modified by this
	 * method. 
	 * 
	 * @param i_hat a weakening coefficient
	 * to use
	 * @param rho1 a substitution to fill
	 * with mappings of the form
	 * <code>x -> c^{a,a*i_hat+b}(u)</code>
	 * @param rho2 a substitution to fill
	 * with mappings of the form
	 * <code>x -> c^{a,a,a*i_hat+b}(u)</code>
	 */
	public void weaken(int i_hat,
			Substitution rho1, Substitution rho2) {

		for (Map.Entry<Variable, Term> e : this.getPatternSubs().getTheta()) {
			Variable x = e.getKey();
			Term theta_x = e.getValue();

			if (theta_x instanceof HatFunction) {
				HatFunction hf = (HatFunction) theta_x;
				HatFunctionSymbol f = hf.getRootSymbol();
				Term u = hf.getArgument();
				int a = hf.getA();
				int b = hf.getB();
				LinkedList<Integer> ab = new LinkedList<>();
				ab.add(a); ab.add(a * i_hat + b);

				rho1.add(x, new HatFunction(f, u, ab)); // ab = [a,b]

				ab.addFirst(a);
				rho2.add(x, new HatFunction(f, u, ab));  // ab = [a,a,b]
			}
			else {
				rho1.add(x, theta_x);
				rho2.add(x, theta_x);
			}
		}
	}

	/**
	 * Returns a string representation of this
	 * simple pattern term relatively to the
	 * given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	@Override
	public String toString(Map<Variable,String> variables) {
		return this.upsilon.toString(variables, false);
	}
}
