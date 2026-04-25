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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.lp.nonloop.PatternRuleLp;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A pattern term, i.e., a pair <code>(t,theta)</code>
 * where <code>t</code> is the <em>base term</code> and
 * <code>theta</code> is the <code>pattern substitution</code>.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternTerm {

	/**
	 * The base term of this pattern term.
	 */
	private final Term t;

	/**
	 * The pumping and closing substitutions
	 * of this pattern term.
	 */
	private final PatternSubstitution theta;

	/**
	 * Builds a pattern term from the specified elements.
	 * 
	 * @param t the base term of this pattern term
	 * @param sigma the only pumping substitution of this pattern term
	 * @param mu the closing substitution of this pattern term
	 */
	public PatternTerm(Term t, Substitution sigma, Substitution mu) {
		this.t = t;
		this.theta = new PatternSubstitution(sigma, mu);
	}

	/**
	 * Builds a pattern term from the specified elements.
	 * 
	 * @param t the base term of this pattern term
	 * @param theta the pattern substitution of this pattern term
	 */
	public PatternTerm(Term t, PatternSubstitution theta) {
		this.t = t;
		this.theta = theta;
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
		for (Substitution eta : this.theta)
			if (eta.contains(v)) return true;

		return this.t.contains(v);
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
	public PatternTerm deepCopy() {
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
	public PatternTerm deepCopy(Map<Term, Term> copies) {
		return new PatternTerm(this.t.deepCopy(copies), this.theta.deepCopy(copies));
	}

	/**
	 * Returns the arity of this pattern term,
	 * i.e., the integer <code>l</code> if the
	 * pattern substitution of this pattern term
	 * has the form
	 * <code>(sigma_1, ..., sigma_l, mu)</code>.
	 * 
	 * @return the arity of this pattern term
	 */
	public int getArity() {
		return this.theta.getArity();
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
	 * Returns the closing substitution of
	 * this pattern term.
	 * 
	 * @return the closing substitution of
	 * this pattern term
	 */
	public Substitution getClosing() {
		return this.theta.getClosing();
	}

	/**
	 * Returns the pumping substitution 
	 * <code>sigma_i</code> of this
	 * pattern term.
	 * 
	 * @return the pumping substitution
	 * <code>sigma_i</code> of this
	 * pattern term
	 */
	public Substitution getPumping(int i) {
		return this.theta.getPumping(i + i);
	}

	/**
	 * Returns the pumping substitution 
	 * <code>sigma_0</code> of this
	 * pattern term.
	 * 
	 * @return the pumping substitution
	 * <code>sigma_0</code> of this
	 * pattern term
	 */
	public Substitution getPumping() {
		return this.theta.getPumping();
	}

	/**
	 * Returns the pattern substitution of
	 * this pattern term.
	 * 
	 * @return the pattern substitution of
	 * this pattern term
	 */
	public PatternSubstitution getPatternSubs() {
		return this.theta;
	}

	/**
	 * Returns the domain variable of this pattern term
	 * as a set.
	 * 
	 * @return the domain variable of this pattern term,
	 * as a set
	 */
	public Set<Variable> getDomainVariable() {
		Set<Variable> domainVariable = new HashSet<>();
		for (Substitution eta : this.theta)
			domainVariable.addAll(eta.getDomain());

		return domainVariable;
	}
	
	/**
	 * Returns the root symbol of this pattern term.
	 * 
	 * @return the root symbol of this pattern term
	 */
	public FunctionSymbol getRootSymbol() {
		return this.getBaseTerm().getRootSymbol();
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
			for (Substitution eta : this.theta)
				if (eta.inDomain(v))
					return true;
		}

		return false;
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

		// Then, we instantiate the closing and pumping
		// substitutions with rho.
		List<Substitution> substitutions = new LinkedList<>();
		for (Substitution eta : this.theta) {
			Substitution sigma = new Substitution();
			for (Map.Entry<Variable, Term> mapping : eta)
				sigma.add(mapping.getKey(), mapping.getValue().apply(rho));
			substitutions.add(sigma);
		}

		// The instantiated pattern term results from 
		// the elements that we have built above.
		return new PatternTerm(t1, new PatternSubstitution(substitutions));
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

		Substitution sigma = this.getPumping();
		Substitution mu = this.getClosing();

		// We also rename the pumping substitution with rho.
		Substitution sigma1 = new Substitution();
		for (Map.Entry<Variable, Term> mapping : sigma)
			sigma1.add((Variable) mapping.getKey().apply(rho),
					mapping.getValue().apply(rho));

		// We also rename the closing substitution with rho.
		Substitution mu1 = new Substitution();
		for (Map.Entry<Variable, Term> mapping : mu)
			mu1.add((Variable) mapping.getKey().apply(rho),
					mapping.getValue());

		// The renamed pattern term results from t1, sigma1
		// and the composition of mu1 with the inverse of rho.
		return new PatternTerm(t1, sigma1, mu1.composeWith(invrho));
	}

	/**
	 * Attempts to compute the most general unifier of
	 * this pattern term and the provided one.
	 * 
	 * Neither this pattern term nor the provided one are
	 * modified by this method.
	 * 
	 * This operation is unsupported for the moment.
	 * 
	 * @param p a pattern term
	 * @return the most general unifier of this pattern
	 * term and the provided one, or <code>null</code>
	 * in case of failure
	 * @throws UnsupportedOperationException
	 */
	public PatternSubstitution unifyWith(SimplePatternTerm p) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Attempts to compute the most general unifier of this
	 * pattern term with the left-hand side of the provided
	 * pattern rule. In case of failure, also attempts to
	 * compute the most general unifier with variations (e.g., 
	 * weakened versions) of the left-hand side of the provided
	 * pattern rule.
	 * 
	 * Neither this pattern term nor the provided pattern
	 * rule are modified by this method.
	 * 
	 * This operation is unsupported for the moment.
	 * 
	 * @param r a pattern rule
	 * @return a collection of most general unifiers
	 * @throws UnsupportedOperationException
	 */
	public Collection<? extends PatternSubstitution> unifyWith(PatternRuleLp r) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Computes <code>p(n)</code>, where
	 * <code>p</code> denotes this pattern
	 * term.
	 * 
	 * @param n a natural
	 * @return <code>p(n)</code>, where
	 * <code>p</code> denotes this pattern
	 * term
	 */
	public Term valueOf(int n) {
		Term s = this.t;

		// We apply sigma n times.
		Substitution sigma = this.theta.getPumping();
		for (int i = 0; i < n; i++)
			s = s.apply(sigma);

		// We apply mu.
		Substitution mu = this.theta.getClosing();
		s = s.apply(mu);

		return s;
	}
	
	/**
	 * If the arity of this pattern term is
	 * <code>l</code> and the provided list
	 * has the form
	 * <code>[n_1, ..., n_l]</code> then returns
	 * the term <code>p(n_1, ..., n_l)</code>,
	 * where <code>p</code> denotes this
	 * pattern term.
	 * 
	 * @param values a list of naturals
	 * @return <code>p(n_1, ..., n_l)</code>,
	 * where <code>p</code> denotes this
	 * pattern term and <code>n_1, ..., n_l</code>
	 * are the elements of the provided list
	 */
	public Term valueOf(List<Integer> values) {
		return this.theta.valueOf(this.t, values);
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
				this.theta.toString(variables) ;
	}

	/**
	 * Returns a string representation of this
	 * pattern term.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
