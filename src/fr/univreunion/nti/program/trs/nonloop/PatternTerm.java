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

package fr.univreunion.nti.program.trs.nonloop;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A pattern term, as defined in [Emmes, Enger, Giesl, IJCAR'12].
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternTerm {

	/**
	 * The base term of this pattern term.
	 */
	private final Term t;

	/**
	 * The pumping substitution of this pattern term.
	 */
	private final Substitution sigma;

	/**
	 * The closing substitution of this pattern term.
	 */
	private final Substitution mu;

	/**
	 * Builds a pattern term whose base term is the
	 * provided term and whose pumping and closing
	 * substitutions are empty.
	 * 
	 * @param t the base term of this pattern term
	 */
	public PatternTerm(Term t) {
		this.t = t;
		this.sigma = new Substitution();
		this.mu = new Substitution();
	}

	/**
	 * Builds a pattern term from the specified elements.
	 * 
	 * @param t the base term of this pattern term
	 * @param sigma the pumping substitution of this pattern term
	 * @param mu the closing substitution of this pattern term
	 */
	public PatternTerm(Term t, Substitution sigma, Substitution mu) {
		this.t = t;
		this.sigma = sigma;
		this.mu = mu;
	}

	/**
	 * Returns the base term of this term.
	 * 
	 * @return the base term of this term
	 */
	public Term getBaseTerm() {
		return this.t;
	}

	/**
	 * Returns the pumping substitution of
	 * this pattern term.
	 * 
	 * @return the pumping substitution of
	 * this pattern term
	 */
	public Substitution getPumping() {
		return this.sigma;
	}

	/**
	 * Returns the closing substitution of
	 * this pattern term.
	 * 
	 * @return the closing substitution of
	 * this pattern term
	 */
	public Substitution getClosing() {
		return this.mu;
	}

	/**
	 * Returns the domain variable of this pattern term
	 * as a set.
	 * 
	 * @return the domain variable of this pattern term,
	 * as a set
	 */
	public Set<Variable> getDomainVariable() {
		Set<Variable> domainVariable = new HashSet<Variable>(this.sigma.getDomain());
		domainVariable.addAll(this.mu.getDomain());

		return domainVariable;
	}

	/**
	 * Checks whether the domain variable of this
	 * pattern term includes the specified term.
	 * 
	 * @param t a term whose presence in the domain
	 * variable of this pattern term is to be tested
	 * @return <code>true</code> iff the domain
	 * variable of this pattern term includes the
	 * specified term
	 */
	public boolean inDomainVariable(Term t) {
		if (t instanceof Variable) {
			Variable v = (Variable) t;
			return this.sigma.inDomain(v) || this.mu.inDomain(v);
		}

		return false;
	}

	/**
	 * Checks whether this pattern term contains
	 * the given variable.
	 * 
	 * @param v a variable whose presence in this
	 * pattern term is to be tested
	 * @return <code>true</code> iff this pattern
	 * term contains <code>v</code>
	 */
	public boolean contains(Variable v) {
		return this.t.contains(v) ||
				this.sigma.contains(v) ||
				this.mu.contains(v);
	}

	/**
	 * Computes <code>p^rho</code> where <code>p</code>
	 * denotes this pattern term and <code>rho</code>
	 * is a domain renaming for <code>p</code> (see
	 * Definition 3 of [Emmes, Enger, Giesl, IJCAR'12])
	 * whose domain is the domain variable of
	 * <code>p</code> and whose range consists of fresh
	 * variables.
	 * 
	 * @return <code>p^rho</code> where <code>p</code>
	 * denotes this pattern term and <code>rho</code>
	 * is a domain renaming for <code>p</code> computed
	 * by this method
	 */
	public PatternTerm rename() {
		// First, we compute the renaming rho.
		Substitution rho = new Substitution();
		for (Variable v : this.getDomainVariable())
			rho.addReplace(v, new Variable());
		
		// Then, we compute p^rho.
		return this.rename(rho);
	}

	/**
	 * Computes <code>p^rho</code> where <code>p</code>
	 * denotes this pattern term. The provided substitution
	 * <code>rho</code> is supposed to be a domain renaming
	 * for <code>p</code> (see Definition 3 of
	 * [Emmes, Enger, Giesl, IJCAR'12]).
	 * 
	 * @param rho a domain renaming for this term
	 * @return <code>p^rho</code> where <code>p</code>
	 * denotes this pattern term
	 */
	public PatternTerm rename(Substitution rho) {
		// First, we compute the inverse of rho.
		Substitution invrho = new Substitution();
		for (Map.Entry<Variable, Term> mapping : rho)
			invrho.add((Variable) mapping.getValue(), mapping.getKey());

		// Then, we rename the base term with rho.
		Term t1 = this.t.apply(rho);

		// We also rename the pumping substitution with rho.
		Substitution sigma1 = new Substitution();
		for (Map.Entry<Variable, Term> mapping : this.sigma)
			sigma1.add((Variable) mapping.getKey().apply(rho),
					mapping.getValue().apply(rho));

		// We also rename the closing substitution with rho.
		Substitution mu1 = new Substitution();
		for (Map.Entry<Variable, Term> mapping : this.mu)
			mu1.add((Variable) mapping.getKey().apply(rho),
					mapping.getValue());

		// The renamed pattern term results from t1, sigma1
		// and the composition of mu1 with the inverse of rho.
		return new PatternTerm(t1, sigma1, mu1.composeWith(invrho));
	}

	/**
	 * Instantiates this pattern term with the provided
	 * substitution. Used for implementing (V) of
	 * [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * It is supposed that the provided substitution
	 * <code>rho</code> is suitable i.e.,
	 * <code>Vars(rho)</code> is disjoint from the domain
	 * variable of this pattern term.
	 * 
	 * @param rho a suitable substitution for instantiating
	 * this pattern term 
	 * @return the result of instantiating this pattern term
	 * with the provided substitution
	 */
	public PatternTerm instantiateWith(Substitution rho) {
		// First, we instantiate the base term with rho.
		Term t1 = this.t.apply(rho);

		// Then, we instantiate the pumping substitution with rho.
		Substitution sigma1 = new Substitution();
		for (Map.Entry<Variable, Term> mapping : this.sigma)
			sigma1.add(mapping.getKey(), mapping.getValue().apply(rho));

		// Finally, we instantiate the closing substitution with rho.
		Substitution mu1 = new Substitution();
		for (Map.Entry<Variable, Term> mapping : this.mu)
			mu1.add(mapping.getKey(), mapping.getValue().apply(rho));

		// The instantiated pattern term results from t1, sigma1 and mu1.
		return new PatternTerm(t1, sigma1, mu1);
	}

	/**
	 * Returns a string representation of this
	 * pattern term relatively to the given set
	 * of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	public String toString(Map<Variable,String> variables) {
		return this.t.toString(variables, false) +
				this.sigma.toString(variables) + "^n" +
				this.mu.toString(variables);
	}

	/**
	 * Returns a string representation of this
	 * pattern term.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<Variable, String>());
	}
}
