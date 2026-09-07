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

package fr.univreunion.nti.program.trs.patternunfolding;

import java.util.Collection;
import java.util.Map;

import fr.univreunion.nti.program.pattern.PatternRule;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A TRS pattern rule obtained by adapting E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025, to term rewriting. The TRS
 * adaptation is described in E. Payet,
 * <a href="https://www.imn.htwk-leipzig.de/~waldmann/WST2025/proceedings/WST2025_paper_2.pdf"><i>Non-Termination
 * of Term Rewrite Systems Using Pattern Unfolding</i></a>, Proceedings of the
 * 20th International Workshop on Termination (WST 2025), 2025.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternRuleTrs extends PatternRule {

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
	private PatternRuleTrs(
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
	PatternRuleTrs(SimplePatternTerm left, SimplePatternTerm right,
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
	 * @return a pattern rule, or <code>null</code> if no pattern
	 * rule could be constructed from the specified arguments
	 */
	public static PatternRuleTrs tryBuild(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		if (left != null && right != null && 0 <= iteration)
			return new PatternRuleTrs(left, right, iteration);

		return null;
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
	 * @return a pattern rule, or <code>null</code> if no pattern
	 * rule could be constructed from the specified arguments
	 */
	public static PatternRuleTrs tryBuild(
			Function left,  PatternSubstitution thetaLeft,
			Function right, PatternSubstitution thetaRight,
			int iteration) {

		if (thetaLeft instanceof SimplePatternSubstitution &&
				thetaRight instanceof SimplePatternSubstitution &&
				left != null && right != null && 0 <= iteration)
			return new PatternRuleTrs(
					SimplePatternTerm.tryBuild(left, thetaLeft),
					SimplePatternTerm.tryBuild(right, thetaRight),
					iteration);

		return null;
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
	public PatternRuleTrs deepCopy() {
		return PatternRuleTrsCopier.deepCopy(this);
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
	public PatternRuleTrs deepCopy(Map<Term, Term> copies) {
		return PatternRuleTrsCopier.deepCopy(this, copies);
	}

	/**
	 * Unfolds this pattern rule forwards with the provided
	 * pattern rule and at the provided position.
	 *
	 * @param r the pattern rule to use for unfolding this rule
	 * @param p a position in the right-hand side of this rule,
	 * at which the unfolding takes place
	 * @param rightAtPosition the subterm at position <code>p</code>
	 * of the right-hand side of this rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this unfolding takes place
	 * @return the resulting unfolded rule
	 */
	public PatternRuleTrs unfoldForwardsWith(
			PatternRuleTrs r,
			Position p, SimplePatternTerm rightAtPosition,
			int iteration) {

		return PatternRuleTrsForwardUnfolder.tryUnfold(
				this, r, p, rightAtPosition, iteration);
	}

	/**
	 * Unfolds this pattern rule once using the
	 * elements of <code>patternRules</code>.
	 * <p>
	 * Also applies the nontermination test of the Payet (2025) TPLP article
	 * cited in the class documentation
	 * to the computed unfolded rules; if the test succeeds for
	 * an unfolded rule, then the corresponding proof argument
	 * is added to <code>proof</code>.
	 *
	 * @param patternRules the set of pattern rules used for
	 * unfolding this pattern rule
	 * @param iteration the current iteration of the
	 * unfolding operator
	 * @param proof a proof to build while unfolding
	 * this pattern rule
	 * @return the resulting unfolded rules
	 */
	public Collection<PatternRuleTrs> unfold(
			Collection<PatternRuleTrs> patternRules,
			int iteration, Proof proof) {

		return PatternRuleTrsUnfolder.unfold(
				this, patternRules, iteration, proof);
	}

	/**
	 * Attempts to weaken this pattern rule
	 * based on the provided pattern terms
	 * <code>subterm</code> and <code>p</code>,
	 * where <code>subterm</code> is supposed
	 * to be a subterm of this pattern rule.
	 * <p>
	 * The values used for weakening this
	 * pattern rule are those computed for
	 * weakening <code>subterm</code> w.r.t.
	 * <code>p</code>.
	 * <p>
	 * The returned collection always includes
	 * this pattern rule.
	 * <p>
	 * For the moment, we perform weakening only
	 * if the arity of <code>p</code>, that of
	 * the left-hand side of this rule and that
	 * of the right-hand side of this rule are
	 * all equal to 1.
	 *
	 * @param subterm a subterm of this pattern
	 * rule
	 * @param p a pattern term for weakening
	 * this pattern rule
	 * @return a collection of weakened versions
	 * of this pattern rule, which always includes
	 * this pattern rule
	 */
	public Collection<PatternRuleTrs> weaken(SimplePatternTerm subterm, SimplePatternTerm p) {
		return PatternRuleTrsWeakener.weaken(this, subterm, p);
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
		Function nonterminating = this.getNonTerminatingTerm();

		return this.getLeft().toString(variables) +
				" -> " + this.getRight().toString(variables) +
				(nonterminating == null ? ":?" : ":" + nonterminating.toString(variables, false));
	}
}
