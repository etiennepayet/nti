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

package fr.univreunion.nti.program.lp.nonloop;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.program.PatternRule;
import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A pattern rule in logic programming, as defined in [Payet, ICLP'25].
 * 
 * It results from unfolding a logic program rule using the pattern
 * unfolding operator T^{\pi}_{P,B} of [Payet, ICLP'25]. As we use
 * sets B that are generated from Prop. 2 of [Payet, ICLP'25], we
 * only consider pattern rules whose left-hand and right-hand sides
 * are simple pattern terms.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternRuleLp extends PatternRule implements NonTerminationWitness {

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
	private PatternRuleLp(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		super(left, right, iteration);
	}

	/**
	 * Builds a pattern rule from the provided elements.
	 * 
	 * For internal use only.
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
	private PatternRuleLp(SimplePatternTerm left, SimplePatternTerm right,
			int iteration, Function nonterminating, int alpha) {

		super(left, right, iteration, nonterminating, alpha);
	}

	/**
	 * Static factory method.
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified elements
	 */
	public static PatternRuleLp getInstance(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		if (left != null && 0 <= iteration)
			return new PatternRuleLp(left, right, iteration);

		return null;
	}

	/**
	 * Static factory method.
	 * 
	 * Builds a pattern rule which has the provided
	 * left-hand side and an empty right-hand side
	 * (i.e., <code>e*</code> in [Payet, ICLP'25]).
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified elements
	 */
	public static PatternRuleLp getInstance(
			SimplePatternTerm left, int iteration) {

		if (left != null && 0 <= iteration)
			return new PatternRuleLp(left, null, iteration);

		return null;
	}

	/**
	 * Static factory method.
	 * 
	 * Constructs a pattern rule from the given elements.
	 * 
	 * @param left the base term on the left-hand side of this
	 * pattern rule
	 * @param thetaLeft the pattern substitution on the left-hand
	 * side of this pattern rule
	 * @param right the base term on the right-hand side of this
	 * pattern rule
	 * @param thetaRight the pattern substitution on the right-hand
	 * side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified elements
	 */
	public static PatternRuleLp getInstance(
			Function left,  PatternSubstitution thetaLeft,
			Function right, PatternSubstitution thetaRight,
			int iteration) {

		if (thetaLeft instanceof SimplePatternSubstitution &&
				thetaRight instanceof SimplePatternSubstitution &&
				left != null && 0 <= iteration)
			return new PatternRuleLp(
					SimplePatternTerm.getInstance(left,  (SimplePatternSubstitution) thetaLeft),
					SimplePatternTerm.getInstance(right, (SimplePatternSubstitution) thetaRight),
					iteration);

		return null;
	}

	/**
	 * Static factory method.
	 * 
	 * Builds a pattern rule which has an empty right-hand side
	 * (i.e., <code>e*</code> in [Payet, ICLP'25]).
	 * 
	 * @param left the base term on the left-hand side of this
	 * pattern rule
	 * @param thetaLeft the pattern substitution on the left-hand
	 * side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified elements
	 */
	public static PatternRuleLp getInstance(
			Function left, PatternSubstitution thetaLeft,
			int iteration) {

		if (thetaLeft instanceof SimplePatternSubstitution &&
				left != null && 0 <= iteration)
			return new PatternRuleLp(
					SimplePatternTerm.getInstance(left, (SimplePatternSubstitution) thetaLeft),
					null,
					iteration);

		return null;
	}

	/**
	 * Returns a deep copy of this pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this pattern rule
	 */
	@Override
	public PatternRuleLp deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a deep copy of this pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern rule
	 */
	@Override
	public PatternRuleLp deepCopy(Map<Term, Term> copies) {
		SimplePatternTerm right = this.getRight();
		Function nonterminating = this.getNonTerminatingTerm();

		return new PatternRuleLp(
				this.getLeft().deepCopy(copies), 
				(right == null ? null : right.deepCopy(copies)),
				this.getIteration(),
				(nonterminating == null ? null : (Function) nonterminating.deepCopy(copies)),
				this.getAlpha());
	}

	/**
	 * Checks whether this rule is a fact, i.e., it
	 * has an empty right-hand side (<code>e*</code>
	 * in [Payet, ICLP'25]).
	 * 
	 * @return <code>true</code> iff this rule is a fact
	 */
	public boolean isFact() {
		return this.getLeft() != null && this.getRight() == null;
	}

	/**
	 * Adds the provided binary rule to this 
	 * nontermination witness.
	 * 
	 * @param R a rule to be added to this witness
	 * @return the witness resulting from adding the
	 * provided rule to this witness
	 */
	@Override
	public NonTerminationWitness add(BinaryRuleLp R) {
		return this;
	}

	/**
	 * Checks whether this object is a nontermination
	 * witness of the given mode.
	 * 
	 * @param m a mode whose nontermination is to be proved
	 * @return a (non-<code>null</code>) nonterminating
	 * atomic query corresponding to <code>m</code> or
	 * <code>null</code>, if this object is not a 
	 * nontermination witness of <code>m</code>
	 */
	@Override
	public Function provesNonTerminationOf(Mode m) {
		Function nonterminating = this.getNonTerminatingTerm();

		if (nonterminating != null &&
				nonterminating.getRootSymbol() == m.getPredSymbol())
			return nonterminating;

		return null;
	}

	/**
	 * Returns a short String representation of this witness.
	 * 
	 * @return a short String representation of this witness
	 */
	@Override
	public String getShortDescription() {
		return "(extracted from a LP pattern rule [Payet, ICLP'25])";
	}

	/**
	 * If this pattern rule is a fact then
	 * attempts to weaken it based on its
	 * left-hand side and the provided
	 * pattern term. 
	 * 
	 * If this pattern rule is not a fact then
	 * the returned collection is empty.
	 * 
	 * For the moment, we perform weakening only
	 * if the arity of the left-hand side of this
	 * pattern rule and that of <code>p</code>
	 * are both equal to 1.
	 *
	 * @param p a pattern term for weakening
	 * this pattern rule
	 * @return a collection of weakened versions
	 * of the left-hand side of this pattern rule
	 * (each produced weakened version is an
	 * upsilon term)
	 */
	public Collection<Term> weakenLeftIfFact(SimplePatternTerm p) {
		// The collection to return at the end.
		Collection<Term> result = new LinkedList<>();

		// We perform weakening only if this rule is
		// a fact, its left-hand side has the same
		// root symbol as p and the arity of its
		// left-hand side and that of p are both
		// equal to 1.
		SimplePatternTerm left = this.getLeft(); // not null (see instance creation methods above)
		if (this.isFact() &&
				left.getUpsilon().getRootSymbol() == p.getUpsilon().getRootSymbol() &&
				left.getArity() == 1 && p.getArity() == 1) {

			// The values to use for weakening this
			// pattern rule are those to use for
			// weakening the left-hand side of this
			// rule w.r.t. p.
			int[] weakeningValues = left.getWeakeningValues(p);

			if (weakeningValues != null) {
				// Here, some weakening values could be computed.

				int i_fun = weakeningValues[0];
				int i_hat = weakeningValues[1];

				if (0 <= i_fun && i_hat < 0)
					// Here, we compute left(i_fun), which is
					// an element of {left(n) | n \in \nat}.
					result.add(left.valueOf(i_fun));

				else if (i_fun < 0 && 0 <= i_hat) {
					// Here, we replace each mapping
					// x -> c^{a,b}(u) in left.theta by
					// x -> c^{a,a*i_hat+b}(u). Indeed,
					// c^{a,a*i_hat+b}(u) describes the set
					// {c^{a*n+a*i_hat+b}(u) | n \in \nat} =
					// {c^{a*(n+i_hat)+b}(u) | n \in \nat} =
					// {c^{a*n+b}(u) | n >= i_hat}
					// which is included in
					// {c^{a*n+b}(u) | n \in \nat}.
					//
					// We also replace each mapping
					// x -> c^{a,b}(u) in left.theta by
					// x -> c^{a,a,a*i_hat+b}(u). Indeed,
					// c^{a,a,a*i_hat+b}(u) describes the set
					// {c^{a*n+a*m+a*i_hat+b}(u) | n,m \in \nat} =
					// {c^{a*(n+m+i_hat)+b}(u) | n,m \in \nat} =
					// {c^{a*n+b}(u) | n >= i_hat}
					// which is included in
					// {c^{a*n+b}(u) | n \in \nat}.
					Substitution rho1 = new Substitution();
					Substitution rho2 = new Substitution();

					left.weaken(i_hat, rho1, rho2);

					result.add(left.getBaseTerm().apply(rho1));					
					result.add(left.getBaseTerm().apply(rho2));
				}
			}
		}

		return result;
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
	@Override
	public String toString(Map<Variable, String> variables) {
		SimplePatternTerm right = this.getRight();
		Function nonterminating = this.getNonTerminatingTerm();

		// The alpha Greek letter (Unicode U+1D6FC), where
		// U+1D6FC = \uD835\uDEFC in UTF-16 (surrogate pair)
		String alpha = "\uD835\uDEFC";
		// The theta Greek letter (Unicode U+1D6F3), where
		// U+1D6F3 = \uD835\uDEF3 in UTF-16 (surrogate pair):
		String theta = "\uD835\uDEF3";

		String end =
				(nonterminating == null ? "" :
					" (R is special with " +
					alpha + "(R) = " + this.getAlpha() +
					" and p(" + alpha + "(R))" + theta + " = " + nonterminating +
					" where " + theta +
						" maps all variables to the constant 0, see Def. 14 + Thm. 5 of [Payet, ICLP'15])");

		return
				(nonterminating == null ? "" : "Pattern rule R = ") +
				this.getLeft().toString(variables) +
				" :- " +
				(right == null ? "e*" : right.toString(variables)) +
				end;
		// (nonterminating == null ? ":?" : ":" + nonterminating.toString(variables, false)));
	}
}
