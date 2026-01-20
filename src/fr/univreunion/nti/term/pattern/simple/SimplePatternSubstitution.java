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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.PatternUtils;

/**
 * A simple pattern substitution, i.e., a function
 * from variables to terms containing no hat symbol
 * or a hat symbol only at the root position.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class SimplePatternSubstitution extends PatternSubstitution {

	/**
	 * The mappings of this simple pattern substitution.
	 */
	private final Substitution theta;

	/**
	 * Builds an empty simple pattern substitution.
	 */
	private SimplePatternSubstitution() {
		super();
		this.theta = new Substitution();
	}

	/**
	 * Builds a simple pattern substitution from
	 * the provided list of pumping and closing
	 * substitutions, which are supposed to have
	 * the correct form (i.e., mappings of the
	 * form x -> c^a(x) for the pumping substitutions).
	 * 
	 * The length of the provided list must be at
	 * least 2 (i.e., the list must contain at least
	 * a pumping substitution and a closing substitution).
	 * 
	 * @param substitutions the pumping and closing
	 * substitutions of this simple pattern substitution
	 * @param theta the mappings of this simple pattern
	 * substitution
	 * @throws IllegalArgumentException if the provided
	 * list is <code>null</code> or is too short
	 */
	private SimplePatternSubstitution(List<Substitution> substitutions, Substitution theta) {
		super(substitutions);
		this.theta = theta;
	}

	/**
	 * Static factory method.
	 * 
	 * Builds an empty simple pattern substitution.
	 * 
	 * @return an empty simple pattern substitution
	 */
	public static SimplePatternSubstitution getInstance() {
		return new SimplePatternSubstitution();
	}

	/**
	 * Static factory method.
	 * 
	 * Builds a simple pattern substitution
	 * from the provided substitution.
	 * 
	 * @return a simple pattern substitution,
	 * or <code>null</code> if no pattern
	 * substitution could be constructed from
	 * the specified element
	 */
	public static SimplePatternSubstitution getInstance(Substitution theta) {
		List<Substitution> upsilon = upsilonInv(theta);
		if (upsilon != null && 2 <= upsilon.size()) 
			return new SimplePatternSubstitution(upsilon, new Substitution(theta));

		return null;
	}

	/**
	 * Static factory method.
	 * 
	 * Builds a simple pattern substitution
	 * from the provided element.
	 * 
	 * @return a simple pattern substitution,
	 * or <code>null</code> if no pattern
	 * substitution could be constructed from
	 * the specified element
	 */
	public static SimplePatternSubstitution getInstance(List<Substitution> substitutions) {
		// The union of the domains of all provided substitutions.
		Set<Variable> dom = new HashSet<>();
		for (Substitution sigma : substitutions)
			dom.addAll(sigma.getDomain());

		// We build the mappings of this simple pattern substitution.
		Substitution theta = new Substitution();
		for (Variable x : dom) {
			List<Term> list_x = new LinkedList<>();
			for (Substitution sigma : substitutions)
				list_x.add(sigma.getOrDefault(x, x));
			Term t = hatFunctionFrom(x, list_x);
			if (t == null) return null;
			theta.add(x, t);
		}

		return new SimplePatternSubstitution(substitutions, theta);
	}

	/**
	 * Computes the composition of this pattern substitution
	 * with the provided one.
	 * 
	 * Neither this pattern substitution nor the provided
	 * one are modified by this method.
	 *  
	 * @param eta the pattern substitution to compose with
	 * this one
	 * @return the result of the composition, or
	 * <code>null</code> in case of failure
	 */
	@Override
	public SimplePatternSubstitution composeWith(PatternSubstitution eta) {

		if (eta instanceof SimplePatternSubstitution)
			return getInstance(this.theta.composeWith(
					((SimplePatternSubstitution) eta).theta));

		return null;
	}

	/**
	 * Returns a deep copy of this pattern substitution
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this pattern substitution
	 */
	@Override
	public SimplePatternSubstitution deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a deep copy of this pattern substitution
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * 
	 * The specified map is used to store subterm
	 * copies and is constructed incrementally.
	 * 
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern substitution
	 */
	@Override
	public SimplePatternSubstitution deepCopy(Map<Term, Term> copies) {
		return getInstance(this.theta.deepCopy(copies));
	}

	/**
	 * Returns the mappings of this simple
	 * pattern substitution.
	 * 
	 * @return the mappings of this simple
	 * pattern substitution
	 */
	public Substitution getTheta() {
		return this.theta;
	}

	/**
	 * Returns a string representation of this
	 * simple pattern substitution relatively
	 * to the given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	@Override
	public String toString(Map<Variable,String> variables) {
		return this.theta.toString(variables);
	}

	/**
	 * Returns a string representation of this
	 * simple pattern substitution.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}

	/**
	 * Attempts to compute a list of pumping and
	 * closing substitutions corresponding to the
	 * provided substitution.
	 * 
	 * @param theta a substitution
	 * @return a list of pumping and closing substitutions,
	 * or <code>null</code> in case of failure
	 */
	private static List<Substitution> upsilonInv(Substitution theta) {
		// The list of substitutions to return at the end.
		LinkedList<Substitution> substitutions = new LinkedList<>();

		// First, we compute the max arity of the hat functions
		// occurring in Range(theta).
		int ar = 0;
		for (Map.Entry<Variable, Term> e : theta) {
			Term theta_x = e.getValue();
			if (theta_x instanceof HatFunction)
				// The arity of a hat function is at least 1.
				ar = Math.max(ar, ((HatFunction) theta_x).getArity());
		}

		// Here, ar >= 0. Moreover, ar > 0 iff we have
		// found a hat function.

		// We create the pumping and closing substitutions.
		// As ar >= 0, there is at least a closing substitution.
		for (int i = 0; i <= ar; i++)
			substitutions.add(new Substitution());

		// We fill the pumping and closing substitutions.
		for (Map.Entry<Variable, Term> e : theta) {
			Variable x = e.getKey();
			Term theta_x = e.getValue();

			if (theta_x instanceof HatFunction) {
				// Here, theta_x = c^{a_1,...,a_l,b}(v).
				HatFunction hf = (HatFunction) theta_x;
				HatFunctionSymbol f = hf.getRootSymbol();
				Term c = f.getSimpleContext();
				Variable x_c = f.getVariable();
				Term v = hf.getArgument();

				// We check whether v contains inner 
				// subterms that are hat functions.
				if (!v.getHatSubterms().isEmpty()) return null;

				Iterator<Integer> it_hf = hf.exponentsDescendingIterator();
				Iterator<Substitution> it_subs = substitutions.descendingIterator();

				// We add the mapping x->c^b(v) to
				// the closing substitution.
				it_subs.next().add(x, PatternUtils.embed(c, x_c, it_hf.next(), v));

				// For each i, we add the mapping x->c^{a_i}(x)
				// to the pumping substitution sigma_i.
				while (it_hf.hasNext())
					it_subs.next().add(x, PatternUtils.embed(c, x_c, it_hf.next(), x));
			}
			else {
				// Here, theta_x is not a hat function.
				// We add the mapping x->theta_x to the
				// closing substitution, but only if 
				// theta_x does not contain inner subterms
				// that are hat functions.
				if (!theta_x.getHatSubterms().isEmpty()) return null;
				substitutions.getLast().add(x, theta_x);
			}
		}

		if (substitutions.size() < 2)
			// Here there is only a closing substitution because
			// we did not encounter hat functions. Then, we also
			// add an empty pumping substitution.
			substitutions.addFirst(new Substitution());

		return substitutions;
	}

	/**
	 * The provided list has the form
	 * <code>[sigma_1(x),...,sigma_l(x),mu(x)]</code>
	 * for pumping substitutions <code>sigma_i</code>
	 * and a closing substitution <code>mu</code>.
	 * If for all <code>1 <= i <= l</code> we have
	 * <code>sigma_i(x) == x</code> then this method
	 * returns <code>mu(x)</code>.
	 * Else, it computes the smallest ground 1-context
	 * <code>c</code> such that
	 * <code>sigma_i(x) = c^{a_i}(x)</code>
	 * and <code>mu(x) = c^b(t)</code> for some naturals
	 * <code>a_i</code> and <code>b</code> and some term
	 * <code>t</code>. Then, it returns the term
	 * <code>c^{a_1,...,a_l,b}(t)</code>, or
	 * <code>null</code> if no such <code>c</code> could
	 * be computed.
	 * 
	 * It is supposed that
	 * <code>sigma_1(x),...,sigma_l(x)</code> are terms
	 * whose only variable is <code>x</code>.
	 * 
	 * @param x the unique variable of
	 * <code>sigma_1(x),...,sigma_l(x)</code>
	 * @param list_x the list
	 * <code>[sigma_1(x),...,sigma_l(x),mu(x)]</code>
	 * @return the term <code>c^{a_1,...,a_l,b}(t)</code>, or
	 * <code>null</code> if <code>c</code> could not be
	 * computed
	 */
	private static Term hatFunctionFrom(Variable x, List<Term> list_x) {

		List<Integer> ab = new LinkedList<>();
		Term c = null;
		Term t = null;
		int a[] = new int[1];

		int i = list_x.size() - 1; // used to check if we have reached the closing substitution
		for (Term sigma_x : list_x)
			if (0 < i--) {
				// Here, we haven't reached the last term of list_x
				// yet, i.e., sigma is a pumping substitution.
				if (sigma_x == x)
					ab.add(0);
				else if (sigma_x instanceof Function) {
					// We compute c and a such that sigma_x = c^a(x).
					Term c_x = PatternUtils.getContext((Function) sigma_x, x, a);

					if (c_x == null) return null;

					if (c == null) c = c_x;
					else if (!c_x.deepEquals(c)) return null;

					ab.add(a[0]);
				}
				else return null;
			}
			else {
				// Here, we have reached the last term of list_x,
				// i.e, actually sigma is mu (i.e., the closing
				// substitution).

				// If c == null then x is in the domain of no
				// pumping substitution. In this case, we return
				// mu(x).
				if (c == null) return sigma_x;

				// Here, c != null, i.e., x is in the domain of at
				// least one pumping substitution.
				// We compute b and t such that mu_x = c^b(t).
				t = PatternUtils.towerOfContexts(sigma_x, c, x, a);
				ab.add(a[0]);
			}

		HatFunctionSymbol hat_c = HatFunctionSymbol.getInstance(c, x);
		return new HatFunction(hat_c, t, ab);
	}
}
