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

package fr.univreunion.nti.program.lp.patternunfolding;

import java.util.Collection;
import java.util.Map;

import fr.univreunion.nti.program.pattern.PatternRule;
import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A pattern rule in logic programming, as defined by E. Payet in
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.
 *
 * <p>It results from unfolding a logic program rule using the pattern
 * unfolding operator T^{\pi}_{P,B} of that article. As we use sets B that are
 * generated from its Proposition 2, we only consider pattern rules whose
 * left-hand and right-hand sides are simple pattern terms.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class PatternRuleLp extends PatternRule implements NonTerminationWitness {

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
	PatternRuleLp(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		super(left, right, iteration);
	}

	/**
	 * Builds a pattern rule from the provided elements.
	 * <p>
	 * For internal use only.
	 *
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @param nonTerminatingTerm a ground nonterminating term
	 * generated from this rule
	 * @param alpha the <code>alpha</code> threshold of
	 * this rule
	 */
	PatternRuleLp(SimplePatternTerm left, SimplePatternTerm right,
			int iteration, Function nonTerminatingTerm, int alpha) {

		super(left, right, iteration, nonTerminatingTerm, alpha);
	}

	/**
	 * Tries to build a pattern rule from the specified left-hand
	 * side, right-hand side and unfolding iteration.
	 *
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified arguments
	 */
	public static PatternRuleLp tryBuild(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		return PatternRuleLpFactory.tryBuild(left, right, iteration);
	}

	/**
	 * Tries to build a pattern fact, i.e., a pattern rule which
	 * has the specified left-hand side and an empty right-hand
	 * side (i.e., <code>e*</code> in the Payet (2025) article cited in the
	 * class documentation).
	 *
	 * @param left the left-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified arguments
	 */
	public static PatternRuleLp tryBuildFact(
			SimplePatternTerm left, int iteration) {

		return PatternRuleLpFactory.tryBuildFact(left, iteration);
	}

	/**
	 * Tries to build a pattern rule from the specified base terms,
	 * pattern substitutions and unfolding iteration.
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
	 * be constructed from the specified arguments
	 */
	public static PatternRuleLp tryBuild(
			Function left,  PatternSubstitution thetaLeft,
			Function right, PatternSubstitution thetaRight,
			int iteration) {

		return PatternRuleLpFactory.tryBuild(
				left, thetaLeft, right, thetaRight, iteration);
	}

	/**
	 * Tries to build a pattern fact from the specified base term,
	 * pattern substitution and unfolding iteration. The produced
	 * rule has an empty right-hand side
	 * (i.e., <code>e*</code> in that article).
	 *
	 * @param left the base term on the left-hand side of this
	 * pattern rule
	 * @param thetaLeft the pattern substitution on the left-hand
	 * side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @return a pattern rule in logic programming,
	 * or <code>null</code> if no pattern rule could
	 * be constructed from the specified arguments
	 */
	public static PatternRuleLp tryBuildFact(
			Function left, PatternSubstitution thetaLeft,
			int iteration) {

		return PatternRuleLpFactory.tryBuildFact(left, thetaLeft, iteration);
	}

	/**
	 * Returns a deep copy of this pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @return a deep copy of this pattern rule
	 */
	@Override
	public PatternRuleLp deepCopy() {
		return PatternRuleLpCopier.deepCopy(this);
	}

	/**
	 * Returns a deep copy of this pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
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
		return PatternRuleLpCopier.deepCopy(this, copies);
	}

	/**
	 * Checks whether this rule is a fact, i.e., it
	 * has an empty right-hand side (<code>e*</code>
	 * in that article).
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
	 * @param rule a rule to be added to this witness
	 * @return the witness resulting from adding the
	 * provided rule to this witness
	 */
	@Override
	public NonTerminationWitness add(BinaryRuleLp rule) {
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
		return PatternRuleLpWitness.provesNonTerminationOf(this, m);
	}

	/**
	 * Returns a short String representation of this witness.
	 *
	 * @return a short String representation of this witness
	 */
	@Override
	public String getShortDescription() {
		return PatternRuleLpWitness.SHORT_DESCRIPTION;
	}

	/**
	 * If this pattern rule is a fact then
	 * attempts to weaken it based on its
	 * left-hand side and the provided
	 * pattern term.
	 * <p>
	 * If this pattern rule is not a fact then
	 * the returned collection is empty.
	 * <p>
	 * For the moment, we perform weakening only
	 * if the arity of the left-hand side of this
	 * pattern rule and that of <code>patternTerm</code>
	 * are both equal to 1.
	 *
	 * @param patternTerm a pattern term for weakening
	 * this pattern rule
	 * @return a collection of weakened versions
	 * of the left-hand side of this pattern rule
	 * (each produced weakened version is an
	 * upsilon term)
	 */
	public Collection<Term> weakenLeftIfFact(SimplePatternTerm patternTerm) {
		return PatternRuleLpWeakener.weakenLeftIfFact(this, patternTerm);
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
		return PatternRuleLpFormatter.format(this, variables);
	}
}
