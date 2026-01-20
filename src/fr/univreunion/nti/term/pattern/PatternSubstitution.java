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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A pattern substitution, i.e., a tuple
 * <code>(sigma_1, ..., sigma_l, mu)</code> 
 * of substitutions with <code>0 < l</code>:
 * the <code>sigma_i</code>'s are the
 * <em>pumping substitutions</em> and
 * <code>mu</code> is the
 * <em>closing substitution</em>.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternSubstitution implements Iterable<Substitution> {

	/**
	 * The tuple <code>(sigma_1, ..., sigma_l, mu)</code>
	 * of substitutions. This list is not <code>null</code>
	 * and its size is at least 2.
	 */
	private final LinkedList<Substitution> substitutions = new LinkedList<>();

	/**
	 * Builds an empty pattern substitution, i.e.,
	 * a pattern substitution which is the pair
	 * <code>(sigma, mu)</code> where
	 * <code>sigma</code> and <code>mu</code> are
	 * the identity substitution.
	 */
	public PatternSubstitution() {
		this.substitutions.add(new Substitution());
		this.substitutions.add(new Substitution());
	}

	/**
	 * Builds a pattern substitution which is the pair
	 * <code>(sigma, mu)</code>.
	 * 
	 * @param sigma the only pumping substitution
	 * of this pattern substitution
	 * @param mu the closing substitution
	 * of this pattern substitution
	 */
	public PatternSubstitution(Substitution sigma, Substitution mu) {
		this.substitutions.add(sigma);
		this.substitutions.add(mu);
	}

	/**
	 * Builds a pattern substitution whose pumping and
	 * closing substitutions are the provided ones.
	 * 
	 * The length of the provided list must be at
	 * least 2 (i.e., the list must contain at least
	 * a pumping substitution and a closing substitution).
	 * 
	 * @param substitutions the pumping and closing
	 * substitutions of this pattern substitution
	 * @throws IllegalArgumentException if the 
	 * provided list does not have the required form
	 */
	public PatternSubstitution(List<Substitution> substitutions) {
		if (substitutions == null || substitutions.size() < 2)
			throw new IllegalArgumentException(
					"construction of a pattern substitution from an unsufficient number of substitutions");

		this.substitutions.addAll(substitutions);
	}

	/**
	 * Computes the composition of this pattern substitution
	 * with the provided one.
	 * 
	 * Neither this pattern substitution nor the provided one
	 * are modified by this method.
	 * 
	 * This operation is unsupported for the moment.
	 *  
	 * @param eta the pattern substitution to compose with
	 * this one
	 * @return the result of the composition
	 * @throws UnsupportedOperationException
	 */
	public PatternSubstitution composeWith(PatternSubstitution eta) {
		throw new UnsupportedOperationException();
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
	public PatternSubstitution deepCopy() {
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
	public PatternSubstitution deepCopy(Map<Term, Term> copies) {
		List<Substitution> substitutions2 = new LinkedList<>();
		for (Substitution eta : this.substitutions)
			substitutions2.add(eta.deepCopy(copies));

		return new PatternSubstitution(substitutions2);
	}

	/**
	 * Returns the arity of this pattern substitution,
	 * i.e., the integer <code>l</code> if this pattern
	 * substitution has the form
	 * <code>(sigma_1, ..., sigma_l, mu)</code>.
	 * 
	 * @return the arity of this pattern substitution
	 */
	public int getArity() {
		return this.substitutions.size() - 1;
	}

	/**
	 * Returns the closing substitution of
	 * this pattern substitution.
	 * 
	 * @return the closing substitution of
	 * this pattern substitution
	 */
	public Substitution getClosing() {
		return this.substitutions.getLast();
	}

	/**
	 * Returns the pumping substitution 
	 * <code>sigma_i</code> of this
	 * pattern substitution.
	 * 
	 * @return the pumping substitution
	 * <code>sigma_i</code> of this
	 * pattern substitution
	 */
	public Substitution getPumping(int i) {
		return this.substitutions.get(i);
	}

	/**
	 * Returns the pumping substitution
	 * <code>sigma_1</code> of this
	 * pattern substitution.
	 * 
	 * @return the pumping substitution
	 * <code>sigma_1</code> of this
	 * pattern substitution
	 */
	public Substitution getPumping() {
		return this.substitutions.getFirst();
	}
	
	/**
	 * Checks if the provided variable
	 * occurs in the domain of a pumping
	 * substitution of this pattern
	 * substitution.
	 * 
	 * @param x a variable 
	 * @return <code>true</code> iff the
	 * provided variable occurs in the
	 * domain of a pumping substitution
	 */
	public boolean inPumpingDomain(Variable x) {
		Iterator<Substitution> it = this.substitutions.descendingIterator();
		// We skip the closing substitution.
		it.next();
		// We check the pumping substitutions.
		while (it.hasNext())
			if (it.next().getOrDefault(x, x) != x)
				return true;
		
		return false;
	}

	/**
	 * Returns an iterator over the substitutions
	 * of this pattern substitution.
	 * 
	 * If this pattern substitution has the form
	 * <code>(sigma_1, ..., sigma_l, mu)</code> then
	 * the iterator first provides <code>sigma_1</code>,
	 * then <code>sigma_2</code> and so on.
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	public ListIterator<Substitution> iterator() {
		return this.substitutions.listIterator();
	}

	/**
	 * If this pattern substitution has the form
	 * <code>(sigma_1, ..., sigma_l, mu)</code> and
	 * the provided list has the form
	 * <code>[n_1, ..., n_l]</code> then returns the term
	 * <code>(sigma_1^n_1 ... sigma_l^n_l mu)(s)</code>.
	 * 
	 * @param s a term
	 * @param values a list of naturals
	 * @return the term
	 * <code>(sigma_1^n_1 ... sigma_l^n_l mu)(s)</code>
	 * @throws IllegalArgumentException if
	 * <code>values</code> is not a list of naturals
	 * whose size is equal to the arity of this
	 * pattern substitution
	 */
	public Term valueOf(Term s, List<Integer> values) {
		if (values.size() != this.getArity())
			throw new IllegalArgumentException("cannot compute value of term (illegal number of values)");

		Iterator<Substitution> it = this.iterator();
		
		// First, we apply the pumping substitutions.
		for (Integer n_i : values) {
			Substitution sigma_i = it.next();
			// We apply sigma_i n_i times.
			for (int i = 0; i < n_i; i++)
				s = s.apply(sigma_i);
		}

		// Then, we apply the closing substitution.
		s = s.apply(it.next());

		return s;
	}

	/**
	 * Returns a string representation of this
	 * pattern substitution relatively to the
	 * given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	public String toString(Map<Variable,String> variables) {
		StringBuffer s = new StringBuffer();
		int i = 1;
		int l = this.substitutions.size();
		for (Substitution eta : this.substitutions) {
			s.append(eta.toString(variables));
			if (i < l) s.append("^n" + i);
			i += 1;
		}

		return s.toString();
	}

	/**
	 * Returns a string representation of this
	 * pattern substitution.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
