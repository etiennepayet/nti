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
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Objects;
import java.util.Set;

/**
 * A substitution.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Substitution implements Iterable<Map.Entry<Variable, Term>> {

	/**
	 * The only mapping of this substitution while it is a singleton.
	 */
	private Variable singleVariable;

	/**
	 * The image of {@link #singleVariable}.
	 */
	private Term singleTerm;

	/**
	 * The mappings of this substitution after it grows beyond one binding.
	 */
	private Map<Variable, Term> mappings;

	/**
	 * Builds an empty substitution.
	 */
	public Substitution() {}

	/**
	 * Copy constructor.
	 *
	 * @param sigma a substitution to copy into this one
	 */
	public Substitution(Substitution sigma) {
		if (sigma.mappings != null)
			this.mappings = new HashMap<>(sigma.mappings);
		else {
			this.singleVariable = sigma.singleVariable;
			this.singleTerm = sigma.singleTerm;
		}
	}

	/**
	 * Adds or replaces one mapping, promoting compact singleton storage to a
	 * hash map when a second domain variable is introduced.
	 *
	 * @param variable the domain variable
	 * @param term the range term
	 */
	private void putMapping(Variable variable, Term term) {
		if (this.mappings != null) {
			this.mappings.put(variable, term);
			return;
		}

		if (this.singleVariable == null) {
			this.singleVariable = variable;
			this.singleTerm = term;
			return;
		}

		if (this.singleVariable.equals(variable)) {
			this.singleTerm = term;
			return;
		}

		this.mappings = new HashMap<>();
		this.mappings.put(this.singleVariable, this.singleTerm);
		this.mappings.put(variable, term);
		this.singleVariable = null;
		this.singleTerm = null;
	}

	/**
	 * Checks whether this substitution maps the specified variable.
	 *
	 * @param variable the variable to check
	 * @return {@code true} iff the variable belongs to this substitution's
	 * domain
	 */
	private boolean containsDomainVariable(Variable variable) {
		if (this.mappings != null)
			return this.mappings.containsKey(variable);
		return this.singleVariable != null &&
				this.singleVariable.equals(variable);
	}

	/**
	 * Adds the mapping <code>v->t</code> to this substitution.
	 * <p>
	 * More precisely, if a mapping of the form <code>v->s</code>
	 * already exists in this substitution and
	 * <code>s.deepEquals(t)=false</code>, then this operation fails
	 * and this method returns <code>false</code>.
	 * <p>
	 * Otherwise, this operation succeeds and this method returns
	 * <code>true</code>:
	 * <p>
	 * - If a mapping of the form <code>v->s</code> already exists
	 * in this substitution and <code>s.deepEquals(t)=true</code>,
	 * then this substitution is left unchanged.
	 * <p>
	 * - If no mapping of the form <code>v->s</code> already exists
	 * in this substitution, then <code>v->t</code> is added to this
	 * substitution, EVEN IF <code>v.deepEquals(t)</code> RETURNS
	 * <code>true</code>.
	 *
	 * @param v a variable
	 * @param t a term
	 * @return <code>true</code> if this operation succeeds and
	 * <code>false</code> otherwise
	 * @throws IllegalArgumentException if <code>v</code> or
	 * <code>t</code> is <code>null</code>
	 */
	public boolean add(Variable v, Term t) {
		if (v == null || t == null)
			throw new IllegalArgumentException(
					"cannot add a null mapping to a substitution");

		Term existingTerm = this.get(v);
		if (existingTerm == null) {
			this.putMapping(v, t);
			return true;
		}
		else return existingTerm.deepEquals(t);
	}

	/**
	 * Adds the mapping <code>v->t</code> to this substitution.
	 * If a mapping <code>v->t'</code> already exists, then it
	 * is replaced.
	 *
	 * @param v a variable
	 * @param t a term
	 * @throws IllegalArgumentException if <code>v</code> or
	 * <code>t</code> is <code>null</code>
	 */
	public void addReplace(Variable v, Term t) {
		if (v == null || t == null)
			throw new IllegalArgumentException(
					"cannot add a null mapping to a substitution");

		this.putMapping(v, t);
	}

	/**
	 * Removes all the mappings from this substitution.
	 */
	public void clear() {
		this.singleVariable = null;
		this.singleTerm = null;
		this.mappings = null;
	}

	/**
	 * Computes the composition of this substitution with
	 * the provided substitution.
	 * <p>
	 * This substitution and <code>theta</code> are not
	 * modified by this method.
	 *
	 * @param theta the substitution to compose with this
	 * substitution
	 * @return the result of composing this substitution
	 * with the provided substitution
	 */
	public Substitution composeWith(Substitution theta) {
		// The value to return at the end.
		Substitution composition = new Substitution();

		// We implement Lemma 2.3 (Composition) of the book
		// [Apt, "From Logic Programming to Prolog", 1997].

		// First, we compute the bindings resulting from
		// those of this substitution.
		for (Map.Entry<Variable, Term> mapping : this) {
			Variable sourceVariable = mapping.getKey();
			Term sourceTerm = mapping.getValue();

			Term composedTerm = sourceTerm.apply(theta);
			if (!sourceVariable.deepEquals(composedTerm))
				composition.putMapping(sourceVariable, composedTerm);
		}

		// Then, we compute the bindings resulting from
		// those of theta.
		for (Map.Entry<Variable, Term> mapping : theta) {
			Variable sourceVariable = mapping.getKey();
			Term sourceTerm = mapping.getValue();

			if (!this.containsDomainVariable(sourceVariable))
				composition.putMapping(sourceVariable, sourceTerm);
		}

		return composition;
	}

	/**
	 * Checks whether this substitution contains
	 * the given variable.
	 *
	 * @param v a variable whose presence in this
	 * substitution is to be tested
	 * @return <code>true</code> iff this substitution
	 * contains <code>v</code>
	 */
	public boolean contains(Variable v) {
		for (Map.Entry<Variable, Term> mapping : this) {
			if (mapping.getKey().contains(v) || mapping.getValue().contains(v))
				return true;
		}

		return false;
	}

	/**
	 * Returns a deep copy of this substitution i.e., a
	 * substitution where each subterm is also copied,
	 * even variable subterms. The specified map is used
	 * to store subterm copies and is constructed
	 * incrementally.
	 * <p>
	 * Everything is copied: the domain and also the
	 * range of this substitution.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this substitution
	 */
	public Substitution deepCopy(Map<Term, Term> copies) {
		// The value to return at the end.
		Substitution copy = new Substitution();

		for (Map.Entry<Variable, Term> mapping : this)
			copy.putMapping(
					(Variable) mapping.getKey().deepCopy(copies),
					mapping.getValue().deepCopy(copies));

		return copy;
	}

	/**
	 * Returns the term to which the specified variable is
	 * mapped, or <code>null</code> if this substitution
	 * contains no mapping for the variable.
	 *
	 * @param v the variable whose associated term is to
	 * be returned
	 * @return the term to which the specified variable is
	 * mapped, or <code>null</code> if this substitution
	 * contains no mapping for the variable
	 */
	public Term get(Variable v) {
		if (this.mappings != null)
			return this.mappings.get(v);
		return this.singleVariable != null &&
				this.singleVariable.equals(v) ? this.singleTerm : null;
	}

	/**
	 * Returns the term to which the specified variable is
	 * mapped, or <code>defaultValue</code> if this
	 * substitution contains no mapping for the variable.
	 *
	 * @param v the variable whose associated term is to
	 * be returned
	 * @param defaultValue the default mapping of the
	 * variable
	 * @return the term to which the specified variable
	 * is mapped, or <code>defaultValue</code> if this
	 * substitution contains no mapping for the variable
	 */
	public Term getOrDefault(Variable v, Term defaultValue) {
		if (this.mappings != null)
			return this.mappings.getOrDefault(v, defaultValue);
		return this.singleVariable != null &&
				this.singleVariable.equals(v) ? this.singleTerm : defaultValue;
	}

	/**
	 * Returns the domain of this substitution as a set.
	 *
	 * @return the domain of this substitution, as a set
	 */
	public Set<Variable> getDomain() {
		Set<Variable> domain = new HashSet<>();
		if (this.mappings != null)
			domain.addAll(this.mappings.keySet());
		else if (this.singleVariable != null)
			domain.add(this.singleVariable);
		return domain;
	}

	/**
	 * Checks whether this substitution is the empty
	 * (identity) substitution.
	 *
	 * @return <code>true</code> iff this substitution
	 * is empty
	 */
	public boolean isEmpty() {
		return this.mappings == null ?
				this.singleVariable == null : this.mappings.isEmpty();
	}

	/**
	 * Returns an iterator over the mappings of
	 * this substitution.
	 * <p>
	 * It makes no guarantees as to the iteration
	 * order of the set of mappings.
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<Map.Entry<Variable, Term>> iterator() {
		if (this.mappings != null)
			return this.mappings.entrySet().iterator();
		return this.singleVariable == null ?
				Collections.emptyIterator() : new SingleMappingIterator();
	}

	/**
	 * A mutable iterator and entry view over the compact singleton state.
	 */
	private final class SingleMappingIterator
			implements Iterator<Map.Entry<Variable, Term>>,
			Map.Entry<Variable, Term> {

		/** The domain variable exposed by this iterator. */
		private final Variable variable = Substitution.this.singleVariable;

		/** The last value retained after this entry becomes detached. */
		private Term value = Substitution.this.singleTerm;

		/** Whether the singleton entry has not been returned yet. */
		private boolean nextAvailable = true;

		/** Whether removal is currently permitted. */
		private boolean removable;

		/** Returns whether this entry still represents the compact mapping. */
		private boolean isAttached() {
			return Substitution.this.mappings == null &&
					Substitution.this.singleVariable == this.variable;
		}

		@Override
		public boolean hasNext() {
			return this.nextAvailable;
		}

		@Override
		public Map.Entry<Variable, Term> next() {
			if (!this.nextAvailable)
				throw new NoSuchElementException();
			if (!this.isAttached())
				throw new ConcurrentModificationException();
			this.nextAvailable = false;
			this.removable = true;
			return this;
		}

		@Override
		public void remove() {
			if (!this.removable)
				throw new IllegalStateException();
			if (!this.isAttached())
				throw new ConcurrentModificationException();
			this.value = Substitution.this.singleTerm;
			Substitution.this.singleVariable = null;
			Substitution.this.singleTerm = null;
			this.removable = false;
		}

		@Override
		public Variable getKey() {
			return this.variable;
		}

		@Override
		public Term getValue() {
			return this.isAttached() ? Substitution.this.singleTerm : this.value;
		}

		@Override
		public Term setValue(Term replacement) {
			Term previous = this.getValue();
			if (this.isAttached())
				Substitution.this.singleTerm = replacement;
			this.value = replacement;
			return previous;
		}

		@Override
		public boolean equals(Object other) {
			return other instanceof Map.Entry<?, ?> mapping &&
					Objects.equals(this.variable, mapping.getKey()) &&
					Objects.equals(this.getValue(), mapping.getValue());
		}

		@Override
		public int hashCode() {
			return Objects.hashCode(this.variable) ^
					Objects.hashCode(this.getValue());
		}
	}

	/**
	 * Removes the mapping <code>v/s</code> from
	 * this substitution if it is present. If
	 * this mapping is not present, then this
	 * substitution is kept unchanged.
	 *
	 * @param v a variable
	 * @param s a term
	 * @return <code>true</code> if and only if
	 * the mapping <code>v/s</code> was removed
	 * from this substitution
	 */
	public boolean remove(Variable v, Term s) {
		Term mappedTerm = this.get(v);
		if (mappedTerm != null && mappedTerm.deepEquals(s)) {
			if (this.mappings != null)
				this.mappings.remove(v);
			else {
				this.singleVariable = null;
				this.singleTerm = null;
			}
			return true;
		}

		return false;
	}

	/**
	 * Renames this substitution using the provided one,
	 * which is supposed to be a renaming (i.e., it maps
	 * variables to variables).
	 * <p>
	 * This substitution is not modified by this method.
	 *
	 * @param theta a renaming
	 * @return the substitution obtained from renaming
	 * this substitution using the given one, or
	 * <code>null</code> if some variable in the domain
	 * of this substitution is not mapped to a variable
	 * by <code>theta</code>
	 */
	public Substitution renameWith(Substitution theta) {
		// The value to return at the end.
		Substitution renamed = new Substitution();

		for (Map.Entry<Variable, Term> mapping : this) {
			Variable sourceVariable = mapping.getKey();

			Term renamedVariableTerm = theta.getOrDefault(sourceVariable, sourceVariable);
			if (!renamedVariableTerm.isVariable()) return null;

			Variable renamedVariable = (Variable) renamedVariableTerm;
			renamed.add(renamedVariable, mapping.getValue().apply(theta));
		}

		return renamed;
	}

	/**
	 * Computes the substitution obtained from restricting the
	 * domain of this substitution to the specified set.
	 * <p>
	 * This substitution is not modified by this method.
	 *
	 * @param vars a set of variables
	 * @return the substitution obtained from restricting the
	 * domain of this substitution to the specified set
	 */
	public Substitution restrictTo(Collection<Variable> vars) {
		// The value to return at the end.
		Substitution restricted = new Substitution();

		for (Map.Entry<Variable, Term> mapping : this) {
			Variable domainVariable = mapping.getKey();
			if (vars.contains(domainVariable))
				restricted.putMapping(domainVariable, mapping.getValue());
		}

		return restricted;
	}

	/**
	 * Computes the union of this substitution with the
	 * provided one, if possible (i.e., if the domain of
	 * this substitution is disjoint from that of the
	 * provided one).
	 *
	 * @param theta a substitution to add to this one
	 * @return the union of this substitution with the
	 * provided one, or <code>null</code> if it is not
	 * possible to compute the union
	 */
	public Substitution unionWith(Substitution theta) {
		// The value to return at the end.
		Substitution union = new Substitution(this);

		for (Map.Entry<Variable, Term> mapping : theta)
			if (!union.add(mapping.getKey(), mapping.getValue()))
				return null;

		return union;
	}

	/**
	 * Returns a string representation of this substitution
	 * relatively to the given set of variable symbols.
	 *
	 * @param variables a set of pairs <code>(v,s)</code>
	 * where <code>s</code> is the string associated with
	 * variable <code>v</code>
	 * @return a string representation of this substitution
	 */
	public String toString(Map<Variable, String> variables) {
		StringBuilder result = new StringBuilder("{");

		int entryIndex = 0;
		for (Map.Entry<Variable, Term> mapping : this) {
			Variable domainVariable = mapping.getKey();
			Term rangeTerm = mapping.getValue();
			if (entryIndex > 0) result.append(", ");
			result.append(domainVariable.toString(variables, true));
			result.append("->");
			result.append(rangeTerm.toString(variables, false));
			entryIndex++;
		}

		result.append('}');
		return result.toString();
	}

	/**
	 * Returns a string representation of this
	 * substitution.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
