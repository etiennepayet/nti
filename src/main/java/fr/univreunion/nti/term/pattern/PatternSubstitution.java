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

package fr.univreunion.nti.term.pattern;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;

import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Base class for pattern substitutions, i.e., tuples
 * <code>(sigma_1, ..., sigma_l, mu)</code>
 * of substitutions with {@code 0 < l}:
 * the <code>sigma_i</code>'s are the
 * <em>pumping substitutions</em> and
 * <code>mu</code> is the
 * <em>closing substitution</em>.
 * Concrete subclasses define the operations that depend on a
 * specific class of pattern substitutions.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class PatternSubstitution implements Iterable<Substitution> {

	/**
	 * The tuple <code>(sigma_1, ..., sigma_l, mu)</code>
	 * of substitutions. This list is not <code>null</code>
	 * and its size is at least 2.
	 */
	private final List<Substitution> pumpingAndClosingSubstitutions;

	/**
	 * Builds an empty pattern substitution, i.e.,
	 * a pattern substitution which is the pair
	 * <code>(sigma, mu)</code> where
	 * <code>sigma</code> and <code>mu</code> are
	 * the identity substitution.
	 */
	protected PatternSubstitution() {
		this.pumpingAndClosingSubstitutions = new ArrayList<>(2);
		this.pumpingAndClosingSubstitutions.add(new Substitution());
		this.pumpingAndClosingSubstitutions.add(new Substitution());
	}

	/**
	 * Builds a pattern substitution whose pumping and
	 * closing substitutions are the provided ones.
	 * <p>
	 * The length of the provided list must be at
	 * least 2 (i.e., the list must contain at least
	 * a pumping substitution and a closing substitution).
	 *
	 * @param substitutions the pumping and closing
	 * substitutions of this pattern substitution
	 * @throws IllegalArgumentException if the
	 * provided list does not have the required form
	 */
	protected PatternSubstitution(List<Substitution> substitutions) {
		if (substitutions == null || substitutions.size() < 2)
			throw new IllegalArgumentException(
					"construction of a pattern substitution from an unsufficient number of substitutions");

		this.pumpingAndClosingSubstitutions = new ArrayList<>(substitutions);
	}

	/**
	 * Computes the composition of this pattern substitution
	 * with the provided one.
	 * <p>
	 * Neither this pattern substitution nor the provided one
	 * are modified by this method.
	 * <p>
	 * Concrete subclasses that support composition define the
	 * corresponding algorithm.
	 *
	 * @param otherPatternSubstitution the pattern substitution
	 * to compose with this one
	 * @return the result of the composition
	 */
	public abstract PatternSubstitution composeWith(
			PatternSubstitution otherPatternSubstitution);

	/**
	 * Returns a deep copy of this pattern substitution
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @return a deep copy of this pattern substitution
	 */
	public abstract PatternSubstitution deepCopy();

	/**
	 * Returns a deep copy of this pattern substitution
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * <p>
	 * The specified map is used to store subterm
	 * copies and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern substitution
	 */
	public abstract PatternSubstitution deepCopy(Map<Term, Term> copies);

	/**
	 * Returns the arity of this pattern substitution,
	 * i.e., the integer <code>l</code> if this pattern
	 * substitution has the form
	 * <code>(sigma_1, ..., sigma_l, mu)</code>.
	 *
	 * @return the arity of this pattern substitution
	 */
	public int getArity() {
		return this.pumpingAndClosingSubstitutions.size() - 1;
	}

	/**
	 * Returns the closing substitution of
	 * this pattern substitution.
	 *
	 * @return the closing substitution of
	 * this pattern substitution
	 */
	public Substitution getClosing() {
		return this.pumpingAndClosingSubstitutions.getLast();
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
		return this.pumpingAndClosingSubstitutions.getFirst();
	}

	/**
	 * Checks if the provided variable
	 * occurs in the domain of a pumping
	 * substitution of this pattern
	 * substitution.
	 *
	 * @param variable a variable
	 * @return <code>true</code> iff the
	 * provided variable occurs in the
	 * domain of a pumping substitution
	 */
	public boolean inPumpingDomain(Variable variable) {
		// We start immediately before the closing substitution and inspect
		// the pumping substitutions in reverse order.
		for (int substitutionIndex =
				this.pumpingAndClosingSubstitutions.size() - 2;
				substitutionIndex >= 0; substitutionIndex--)
			if (this.pumpingAndClosingSubstitutions.get(substitutionIndex)
					.getOrDefault(variable, variable) != variable)
				return true;

		return false;
	}

	/**
	 * Returns an iterator over the substitutions
	 * of this pattern substitution.
	 * <p>
	 * If this pattern substitution has the form
	 * <code>(sigma_1, ..., sigma_l, mu)</code> then
	 * the iterator first provides <code>sigma_1</code>,
	 * then <code>sigma_2</code> and so on, and finally
	 * <code>mu</code>.
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	public ListIterator<Substitution> iterator() {
		return this.pumpingAndClosingSubstitutions.listIterator();
	}

	/**
	 * Returns a string representation of this
	 * pattern substitution relatively to the
	 * given set of variable symbols.
	 *
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of this pattern
	 * substitution
	 */
	public String toString(Map<Variable,String> variables) {
		StringBuilder result = new StringBuilder();
		int substitutionIndex = 1;
		int substitutionCount = this.pumpingAndClosingSubstitutions.size();
		for (Substitution substitution : this.pumpingAndClosingSubstitutions) {
			result.append(substitution.toString(variables));
			if (substitutionIndex < substitutionCount)
				result.append("^n").append(substitutionIndex);
			substitutionIndex++;
		}

		return result.toString();
	}

	/**
	 * Returns a string representation of this
	 * pattern substitution.
	 *
	 * @return a string representation of this
	 * pattern substitution
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
