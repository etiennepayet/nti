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

package fr.univreunion.nti.program.trs.patternunfolding.patternproducer;

import java.util.Collection;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A set of methods for inferring correct pattern rules
 * in term rewriting.
 *
 * <p>The construction implements Proposition 9 of E. Payet,
 * <a href="https://www.imn.htwk-leipzig.de/~waldmann/WST2025/proceedings/WST2025_paper_2.pdf"><i>Non-Termination
 * of Term Rewrite Systems Using Pattern Unfolding</i></a>, Proceedings of the
 * 20th International Workshop on Termination (WST 2025), 2025, adapting
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class CorrectPatternRuleTrsProducer {

	/**
	 * Collects the pattern rules obtained by applying
	 * Proposition 9 of the Payet (WST 2025) paper cited in the class
	 * documentation to the provided
	 * rules, which are supposed to be variable disjoint.
	 * <p>
	 * This method tests all non-variable subterms of the
	 * right-hand side of <code>r1</code> that can play
	 * the role of <code>c(x_1,...,x_m)</code> in
	 * Proposition 9.
	 *
	 * @param r1 a TRS rule to be checked
	 * (it corresponds to the rule <code>r</code>
	 * of Proposition 9)
	 * @param r2 a TRS rule to be checked
	 * (it corresponds to the rule <code>r'</code>
	 * of Proposition 9 and is supposed to be variable
	 * disjoint from <code>r1</code>)
	 * @return the collection of pattern rules produced
	 * by Proposition 9 of that paper, empty if no
	 * candidate yields a rule
	 */
	public static Collection<PatternRuleTrs> collectPatternRulesWithProp9Wst25(
			RuleTrs r1, RuleTrs r2) {
		return Prop9PatternRuleTrsProducer.collectFrom(r1, r2);
	}

	/**
	 * Builds the trivial pattern rule
	 * <code>left^* -> right^*</code> associated
	 * with the provided TRS rule
	 * <code>left -> right</code>.
	 * <p>
	 * This construction does not infer a new pattern:
	 * it only lifts both sides of the original rule to
	 * trivial pattern terms.
	 *
	 * @param r the TRS rule to lift
	 * @return the trivial pattern rule associated with
	 * <code>r</code>
	 */
	public static PatternRuleTrs buildTrivialPatternRule(RuleTrs r) {
		// If r = (left -> right) then we produce
		// the pattern rule (left^* -> right^*).
		SimplePatternTerm left  = SimplePatternTerm.of(r.getLeft());
		SimplePatternTerm right = SimplePatternTerm.of(r.getRight());

		return PatternRuleTrs.tryBuild(left, right, 0);
	}

	/**
	 * Considers the following situations:
	 * <ol>
	 * <li>
	 * <code>r1 = c'(c(s, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2) -> c(x2, c1^b(y2))</code>
	 * </li>
	 * <li>
	 * <code>r1 = c'(c(s, x1, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2, z2) -> c(x2, c1^b(y2), z2)</code>
	 * </li>
	 * </ol>
	 * where
	 * <code>x1, x2, y2, z2</code> are variables,
	 * <code>x2, y2, z2</code> are distinct and
	 * do not occur in <code>c', c, c1</code>,
	 * <code>x1</code> does not occur in
	 * <code>c', c, c1, s</code>,
	 * <code>a, b</code> are non-zero naturals.
	 * Collects the pattern rules obtained by looking for
	 * context-shift candidates in the left-hand side of
	 * the first rule.
	 *
	 * @param r1 the TRS rule whose left-hand side is searched
	 * for candidates
	 * @param r2 the TRS rule used to validate each candidate
	 * @return a collection consisting of the
	 * pattern rules
	 * <code>c'(c(c1^{a,0}(s), y2)) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * or
	 * <code>c'(c(c1^{a,0}(s), y2, c1^{b,0}(y2))) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * for all possible contexts <code>c'</code>
	 * (empty if nothing could be produced)
	 */
	public static Collection<PatternRuleTrs> collectPatternRulesFromContextShift(
			RuleTrs r1, RuleTrs r2) {
		return ContextShiftPatternRuleTrsProducer.collectFrom(r1, r2);
	}

	/**
	 * Attempts to build a pattern rule from two binary
	 * rules that shift two arguments through a common
	 * unary context.
	 * <p>
	 * More precisely, this method considers the following
	 * situation:
	 * <ol>
	 * <li>
	 * <code>r1 = (c(s1, s2) -> t)</code>
	 * </li>
	 * <li>
	 * <code>r2 = (c(c1^a(x2), y2) -> c(x2, y2))</code>
	 * </li>
	 * <li>
	 * <code>r3 = (c(x3, c1^b(y3)) -> c(x3, y3))</code>
	 * </li>
	 * </ol>
	 * where <code>s1, s2, t</code> are terms,
	 * <code>c</code> is a 2-context,
	 * <code>c1</code> is a 1-context,
	 * <code>x2, y2</code> are distinct variables
	 * that do not occur in <code>c, c1</code>,
	 * <code>x3, y3</code> are distinct variables
	 * that do not occur in <code>c, c1</code>,
	 * and <code>a, b</code> are naturals.
	 *
	 * @param r1 the rule providing the initial arguments
	 * @param r2 the rule shifting the first argument
	 * @param r3 the rule shifting the second argument
	 * @return the pattern rule
	 * <code>c(c1^{a,0}(s1), c1^{b,0}(s2)) -> t^*</code>,
	 * or <code>null</code> if the provided rules do not
	 * match this schema
	 */
	public static PatternRuleTrs tryBuildPatternRuleFromTwoContextShifts(
			RuleTrs r1, RuleTrs r2, RuleTrs r3) {
		return TwoContextShiftPatternRuleTrsProducer.tryBuild(r1, r2, r3);
	}

	/** Prevents instantiation. */
	private CorrectPatternRuleTrsProducer() {}
}
