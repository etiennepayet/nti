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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.Trs;

/**
 * A substitution.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Substitution implements Iterable<Map.Entry<Variable, Term>> {

	/**
	 * The mappings of this substitution.
	 */
	private final Map<Variable, Term> mappings = new HashMap<Variable, Term>();

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
		this.mappings.putAll(sigma.mappings);
	}
	
	/**
	 * Adds the mapping <code>v->t</code> to this substitution.
	 * 
	 * More precisely, if a mapping of the form <code>v->s</code>
	 * already exists in this substitution and
	 * <code>s.deepEquals(t)=false</code>, then this operation fails
	 * and this method returns <code>false</code>.
	 * 
	 * Otherwise, this operation succeeds and this method returns
	 * <code>true</code>:
	 * 
	 * - If a mapping of the form <code>v->s</code> already exists
	 * in this substitution and <code>s.deepEquals(t)=true</code>,
	 * then this substitution is left unchanged.
	 * 
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

		Term s = this.mappings.get(v);
		if (s == null) {
			this.mappings.put(v, t);
			return true;
		}
		else return s.deepEquals(t);
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

		this.mappings.put(v, t);
	}
	
	/**
	 * Removes all of the mappings from this substitution.
	 */
	public void clear() {
		this.mappings.clear();
	}
	
	/**
	 * Checks whether this substitution commutes with the
	 * provided one i.e., for all variable <code>V</code>,
	 * <code>sigma(theta(V)) = theta(sigma(V))</code> where
	 * <code>sigma</code> denotes this substitution.
	 * 
	 * @param theta a substitution 
	 * @return <code>true</code> iff this substitution
	 * commutes with the provided one
	 */
	public boolean commutesWith(Substitution theta) {
		// First, we check whether sigma(theta(v)) = theta(sigma(v))
		// for all variable v in the domain of this substitution.
		for (Variable v : this.mappings.keySet()) {
			Term sigmatheta = v.apply(theta).apply(this);
			Term thetasigma = v.apply(this).apply(theta);
			if (!sigmatheta.deepEquals(thetasigma))
				return false;
		}

		// Then, we check whether sigma(theta(v)) = theta(sigma(v))
		// for all variable v in the domain of theta.
		for (Variable v : theta.mappings.keySet()) {
			Term sigmatheta = v.apply(theta).apply(this);
			Term thetasigma = v.apply(this).apply(theta);
			if (!sigmatheta.deepEquals(thetasigma))
				return false;
		}

		// Here, all the checks succeeded, hence we
		// return true.
		return true;
	}
	
	/**
	 * Computes the composition of this substitution with
	 * the provided substitution.
	 * 
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
		Substitution sigma = new Substitution();

		// We implement Lemma 2.3 (Composition) of the book
		// [Apt, "From Logic Programming to Prolog", 1997].

		// First, we compute the bindings resulting from
		// those of this substitution.
		for (Map.Entry<Variable, Term> e : this.mappings.entrySet()) {
			Variable v = e.getKey();
			Term s = e.getValue();

			Term t = s.apply(theta);
			if (!v.deepEquals(t))
				sigma.mappings.put(v, t);
		}

		// Then, we compute the bindings resulting from
		// those of theta.
		Set<Variable> domThis = this.mappings.keySet();
		for (Map.Entry<Variable, Term> e : theta.mappings.entrySet()) {
			Variable v = e.getKey();
			Term s = e.getValue();

			if (!domThis.contains(v))
				sigma.mappings.put(v, s);
		}

		return sigma;
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
		for (Map.Entry<Variable, Term> e : this.mappings.entrySet()) {
			if (e.getKey().contains(v) || e.getValue().contains(v))
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
	 * 
	 * Everything is copied: the domain and also the
	 * range of this substitution.
	 * 
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
		Substitution sigma = new Substitution();

		for (Map.Entry<Variable, Term> e : this.mappings.entrySet())
			sigma.mappings.put(
					(Variable) e.getKey().deepCopy(copies),
					e.getValue().deepCopy(copies));

		return sigma;
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
		return this.mappings.get(v);
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
		return this.mappings.getOrDefault(v, defaultValue);
	}

	/**
	 * Returns the domain of this substitution as a set.
	 * 
	 * @return the domain of this substitution, as a set
	 */
	public Set<Variable> getDomain() {
		return new HashSet<Variable>(this.mappings.keySet());
	}

	/**
	 * Checks whether this substitution includes
	 * the specified variable in its domain.
	 * 
	 * @param v a variable whose presence in the
	 * domain of this substitution is to be tested
	 * @return <code>true</code> iff this substitution
	 * includes the specified variable in its domain
	 */
	public boolean inDomain(Variable v) {
		return this.mappings.containsKey(v);
	}
	
	/**
	 * Checks whether the set of variables of this
	 * substitution is disjoint from the specified
	 * set.
	 * 
	 * @param vars a set of variables
	 * @return <code>true</code> if and only if the
	 * set of variables of this substitution is
	 * disjoint from the specified set
	 */
	public boolean isDisjointFrom(Collection<Variable> vars) {
		// We check whether each mapping of this substitution
		// is disjoint from vars.
		for (Map.Entry<Variable, Term> e : this.mappings.entrySet())
			if (vars.contains(e.getKey()))
				return false;
			else
				for (Variable v : e.getValue().getVariables())
					if (vars.contains(v))
						return false;

		// If we get there, then no variable of this substitution
		// occurs in vars.
		return true;
	}
	
	/**
	 * Checks whether this substitution is the empty
	 * (identity) substitution.
	 * 
	 * @return <code>true</code> iff this substitution
	 * is empty
	 */
	public boolean isEmpty() {
		return this.mappings.isEmpty();
	}

	/**
	 * Tries to complete <code>matcher</code> into a matcher
	 * of this substitution onto <code>theta</code> i.e.,
	 * tries to complete <code>matcher</code> so that this
	 * substitution is more general than <code>theta</code>
	 * for <code>matcher</code>.
	 * 
	 * This substitution and <code>theta</code> are not modified
	 * by this method. On the contrary, <code>matcher</code>
	 * may be modified, even if this method fails.
	 * 
	 * @param theta a substitution
	 * @param matcher a substitution to complete into a
	 * matcher of this substitution onto <code>theta</code>
	 * @return <code>true</code> iff <code>matcher</code>
	 * could be completed into a matcher of this substitution
	 * onto <code>theta</code>
	 */
	public boolean isMoreGeneralThan(Substitution theta, Substitution matcher) {
		// First, we consider the mappings of this substitution.
		for (Map.Entry<Variable, Term> e : this.mappings.entrySet()) {
			Variable v = e.getKey();
			Term s = e.getValue();
			Term t = theta.mappings.get(v);
			if (t == null) {
				// Here, variable v is not in the domain of theta.
				// Hence, if this substitution is more general than
				// theta for matcher, v is removed by the composition
				// of this substitution with matcher.
				if (s instanceof Variable) {
					// Removal of v is only possible if s is a variable.
					if (!matcher.add((Variable) s, v))
						// We add s/v to matcher. If this fails,
						// we return false.
						return false;
				}
				else return false;
			}
			else if (!s.isMoreGeneralThan(t, matcher))
				return false;
		}

		// Then, we consider the mappings of theta.
		for (Map.Entry<Variable, Term> e : theta.mappings.entrySet()) {
			Variable v = e.getKey();
			Term s = this.mappings.get(v);
			Term t = e.getValue();
			Term u = matcher.mappings.get(v);
			if (s == null) {
				if (u == null) {
					if (!matcher.add(v, t))
						return false;
				}
				else if (t != u) return false;
			}
			else if (!s.apply(matcher).deepEquals(t))
				return false;
		}

		// Finally, we check whether the domains coincide.
		Set<Variable> domThis = new HashSet<Variable>(this.mappings.keySet());
		Set<Variable> domMatcher = matcher.mappings.keySet();
		Set<Variable> domTheta = theta.mappings.keySet();
		domThis.addAll(domMatcher);
		if (domThis.equals(domTheta)) return true;

		return false;
	}

	/**
	 * Returns an iterator over the mappings of
	 * this substitution.
	 * 
	 * It makes no guarantees as to the iteration
	 * order of the set of mappings.
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<Map.Entry<Variable, Term>> iterator() {
		return this.mappings.entrySet().iterator();
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
		Term t = this.mappings.get(v);
		if (t != null && t.deepEquals(s)) {
			this.mappings.remove(v);
			return true;
		}
		
		return false;
	}
	
	/**
	 * Renames this substitution using the provided one,
	 * which is supposed to be a renaming (i.e., it maps
	 * variables to variables).
	 * 
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
		Substitution sigma = new Substitution();
		
		for (Map.Entry<Variable, Term> e : this.mappings.entrySet()) {
			Variable x = e.getKey();
			
			Term t = theta.getOrDefault(x, x);
			if (!t.isVariable()) return null;
			
			Variable y = (Variable) t;
			sigma.add(y, e.getValue().apply(theta));
		}
		
		return sigma;
	}

	/**
	 * Computes the substitution obtained from restricting the
	 * domain of this substitution to the specified set.
	 * 
	 * This substitution is not modified by this method.
	 * 
	 * @param vars a set of variables
	 * @return the substitution obtained from restricting the
	 * domain of this substitution to the specified set
	 */
	public Substitution restrictTo(Collection<Variable> vars) {
		// The value to return at the end.
		Substitution sigma = new Substitution();

		for (Map.Entry<Variable, Term> e : this.mappings.entrySet()) {
			Variable v = e.getKey();
			if (vars.contains(v))
				sigma.mappings.put(v, e.getValue());
		}

		return sigma;
	}
	
	/**
	 * Rewrites the range of this substitution using the rules
	 * of the specified TRS.
	 * 
	 * @param IR a TRS for rewriting this substitution
	 * @return the collection of substitutions resulting from
	 * the rewriting
	 */
	public Collection<Substitution> rewriteWith(Trs IR) {
		// The collection to return at the end.
		Collection<Substitution> result = new LinkedList<Substitution>();

		for (Map.Entry<Variable, Term> e : this.mappings.entrySet())
			for (Term u : e.getValue().rewriteWith(IR)) {
				// We copy this substitution.
				Substitution theta = new Substitution(this);
				// Then, we replace the mapping e.getKey() -> e.getValue()
				// with e.getKey() -> u.
				theta.mappings.put(e.getKey(), u);
			}

		return result;
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
		Substitution eta = new Substitution(this);

		for (Map.Entry<Variable, Term> e : theta)
			// if (eta.mappings.put(e.getKey(), e.getValue()) != null)
			if (!eta.add(e.getKey(), e.getValue()))
				return null;

		return eta;
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
		StringBuffer s = new StringBuffer("{");

		Set<Map.Entry<Variable, Term>> entries = this.mappings.entrySet();
		int k = 0;
		for (Map.Entry<Variable, Term> e : entries) {
			Variable v = e.getKey();
			Term t = e.getValue();
			//if (v != t) {
				if (k > 0) s.append(", ");
				s.append(v.toString(variables, true));
				s.append("->");
				s.append(t.toString(variables, false));
				k++;
			//}
		}

		s.append('}');
		return s.toString();
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
