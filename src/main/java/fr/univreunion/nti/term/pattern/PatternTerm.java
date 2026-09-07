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

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Base class for pattern terms, i.e., pairs <code>(t,eta)</code>
 * where <code>t</code> is the <em>base term</em> and
 * <code>eta</code> is the <em>pattern substitution</em>.
 * Concrete subclasses define the operations that depend on a
 * specific class of pattern terms.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class PatternTerm {

	/**
	 * The base term of this pattern term.
	 */
	private final Term baseTerm;

	/**
	 * The pattern substitution of this pattern term.
	 */
	private final PatternSubstitution patternSubstitution;

	/**
	 * Builds a pattern term from the specified elements.
	 *
	 * @param baseTerm the base term of this pattern term
	 * @param patternSubstitution the pattern substitution of this pattern term
	 */
	protected PatternTerm(
			Term baseTerm, PatternSubstitution patternSubstitution) {
		this.baseTerm = baseTerm;
		this.patternSubstitution = patternSubstitution;
	}

	/**
	 * Checks whether this pattern term contains
	 * the given variable.
	 *
	 * @param variable a variable whose presence in this
	 * pattern term is to be tested
	 * @return <code>true</code> iff this pattern
	 * term contains <code>v</code>
	 */
	public boolean contains(Variable variable) {
		for (Substitution substitution : this.patternSubstitution)
			if (substitution.contains(variable)) return true;

		return this.baseTerm.contains(variable);
	}

	/**
	 * Returns a deep copy of this pattern term, i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @return a deep copy of this pattern term
	 */
	public abstract PatternTerm deepCopy();

	/**
	 * Returns a deep copy of this pattern term, i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern term
	 */
	public abstract PatternTerm deepCopy(Map<Term, Term> copies);

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
		return this.patternSubstitution.getArity();
	}

	/**
	 * Returns the base term of this term.
	 *
	 * @return the base term of this term
	 */
	public Term getBaseTerm() {
		return this.baseTerm;
	}

	/**
	 * Returns the closing substitution of
	 * this pattern term.
	 *
	 * @return the closing substitution of
	 * this pattern term
	 */
	public Substitution getClosing() {
		return this.patternSubstitution.getClosing();
	}

	/**
	 * Returns the pumping substitution
	 * <code>sigma_1</code> of this
	 * pattern term.
	 *
	 * @return the pumping substitution
	 * <code>sigma_1</code> of this
	 * pattern term
	 */
	public Substitution getPumping() {
		return this.patternSubstitution.getPumping();
	}

	/**
	 * Returns the pattern substitution of
	 * this pattern term.
	 *
	 * @return the pattern substitution of
	 * this pattern term
	 */
	public PatternSubstitution getPatternSubstitution() {
		return this.patternSubstitution;
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
	 * Attempts to compute the most general unifier of
	 * this pattern term and the provided one.
	 * <p>
	 * Neither this pattern term nor the provided one are
	 * modified by this method.
	 * <p>
	 * Concrete subclasses that support unification define the
	 * corresponding algorithm.
	 *
	 * @param otherPatternTerm a pattern term
	 * @return the most general unifier of this pattern
	 * term and the provided one, or <code>null</code>
	 * in case of failure
	 */
	public abstract PatternSubstitution unifyWith(SimplePatternTerm otherPatternTerm);

	/**
	 * Attempts to compute the most general unifier of this
	 * pattern term with the left-hand side of the provided
	 * pattern rule. In case of failure, also attempts to
	 * compute the most general unifier with variations (e.g.,
	 * weakened versions) of the left-hand side of the provided
	 * pattern rule.
	 * <p>
	 * Neither this pattern term nor the provided pattern
	 * rule are modified by this method.
	 * <p>
	 * Concrete subclasses that support unification define the
	 * corresponding algorithm.
	 *
	 * @param patternRule a pattern rule
	 * @return a collection of most general unifiers
	 */
	public abstract Collection<PatternSubstitution> unifyWith(PatternRuleLp patternRule);

	/**
	 * Instantiates this pattern term at the specified index. A negative index
	 * performs no pumping iteration and therefore behaves like zero.
	 *
	 * @param index an instantiation index
	 * @return the instantiated term
	 */
	public Term instantiateAt(int index) {
		Term instantiatedTerm = this.baseTerm;

		// We apply the pumping substitution index times.
		Substitution pumpingSubstitution =
				this.patternSubstitution.getPumping();
		for (int applicationIndex = 0;
				applicationIndex < index; applicationIndex++)
			instantiatedTerm = instantiatedTerm.apply(pumpingSubstitution);

		// We apply the closing substitution.
		Substitution closingSubstitution =
				this.patternSubstitution.getClosing();
		instantiatedTerm = instantiatedTerm.apply(closingSubstitution);

		return instantiatedTerm;
	}

	/**
	 * Returns a string representation of this
	 * pattern term relatively to the given set
	 * of variable symbols.
	 *
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of this pattern
	 * term
	 */
	public String toString(Map<Variable, String> variables) {
		return this.baseTerm.toString(variables, false) +
				this.patternSubstitution.toString(variables);
	}

	/**
	 * Returns a string representation of this
	 * pattern term.
	 *
	 * @return a string representation of this
	 * pattern term
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
