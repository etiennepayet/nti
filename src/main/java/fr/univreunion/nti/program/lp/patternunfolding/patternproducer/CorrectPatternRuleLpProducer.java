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

package fr.univreunion.nti.program.lp.patternunfolding.patternproducer;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A set of methods for inferring correct pattern rules
 * in logic programming.
 *
 * <p>The construction implements Proposition 2 of E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class CorrectPatternRuleLpProducer {

	/**
	 * Disables construction.
	 */
	private CorrectPatternRuleLpProducer() {
	}

	/**
	 * Checks whether <code>sigma</code> is
	 * suitable.
	 *
	 * @param sigma a substitution
	 * @return <code>true</code> iff
	 * <code>sigma</code> is suitable
	 */
	static boolean isSuitable(Substitution sigma) {

		Set<Variable> dom = sigma.getDomain();

		for (Map.Entry<Variable, Term> e : sigma) {
			Variable x = e.getKey();

			// We check whether x is the only
			// variable of Dom(sigma) that occurs in
			// sigma(x).

			Set<Variable> vars = e.getValue().getVariables();
			vars.retainAll(dom);

			if (vars.size() != 1)
				// Here, no variable of dom occurs in s or
				// at least two variables of dom occur in s.
				return false;
			// Here, exactly one variable of dom occurs in s.
			// We check whether it is x.
			if (vars.iterator().next() != x) return false;
		}

		return true;
	}

	/**
	 * Attempts to build the pattern rule obtained by applying
	 * Proposition 2 of the Payet (2025) article cited in the class
	 * documentation to the provided rule.
	 * <p>
	 * The rule is expected to be binary. The method returns
	 * <code>null</code> when the rule does not satisfy the
	 * hypotheses of the proposition, or when the resulting pattern
	 * rule cannot be built.
	 *
	 * @param r the binary rule to be checked
	 * @return the pattern rule produced by Proposition 2 of
	 * that article, or <code>null</code> if no such rule
	 * can be built
	 */
	public static PatternRuleLp tryBuildPatternRuleWithProp2Iclp25(RuleLp r) {
		// r is supposed to be binary, i.e.,
		// of the form left :- right.
		Function left  = r.getHead();
		Function right = r.getBody(0);

		// The pumping substitution of
		// the left-hand side of the
		// returned pattern rule.
		Substitution leftSigma  = new Substitution();
		// The pumping substitution of
		// the right-hand side of the
		// returned pattern rule.
		Substitution rightSigma = new Substitution();

		// First, we complete leftSigma
		// and rightSigma.
		for (Position position : left.dpos(right, true)) {
			Term leftAtPosition = left.get(position);
			Term rightAtPosition = right.get(position);

			if (!completeDisagreementSubstitutions(
					leftAtPosition,
					rightAtPosition,
					leftSigma,
					rightSigma))
				return null;
		}

		// Then, we check whether leftSigma
		// and rightSigma are suitable.
		Set<Variable> dom = leftSigma.getDomain();
		dom.addAll(rightSigma.getDomain()); // dom = Dom(leftSigma) U Dom(rightSigma)
		if (!isSuitable(leftSigma) || !isSuitable(rightSigma))
			return null;

		Map<Term, Term> copies = new HashMap<>();
		return PatternRuleLp.tryBuild(
				SimplePatternTerm.tryBuild(left.deepCopy(copies),
						leftSigma.deepCopy(copies), new Substitution()),
				SimplePatternTerm.tryBuild(right.deepCopy(copies),
						rightSigma.deepCopy(copies), new Substitution()),
				0);
	}

	/**
	 * Completes the left and right pumping substitutions from one
	 * disagreement pair.
	 *
	 * @param leftAtPosition the left subterm at a disagreement position
	 * @param rightAtPosition the right subterm at the same position
	 * @param leftSigma the left-side pumping substitution to complete
	 * @param rightSigma the right-side pumping substitution to complete
	 * @return <code>true</code> iff the disagreement pair is compatible
	 * with the substitutions computed so far
	 */
	private static boolean completeDisagreementSubstitutions(
			Term leftAtPosition,
			Term rightAtPosition,
			Substitution leftSigma,
			Substitution rightSigma) {

		if (leftAtPosition instanceof Variable variable)
			// Here, variable is not equal to rightAtPosition
			// because (leftAtPosition, rightAtPosition) is a
			// disagreement pair.
			return addConsistentMapping(rightSigma, variable, rightAtPosition);

		if (rightAtPosition instanceof Variable variable)
			// Here, variable is not equal to leftAtPosition
			// because (leftAtPosition, rightAtPosition) is a
			// disagreement pair.
			return addConsistentMapping(leftSigma, variable, leftAtPosition);

		return false;
	}

	/**
	 * Adds a mapping to a substitution, or checks that an existing
	 * mapping has the same image.
	 *
	 * @param substitution the substitution to complete
	 * @param variable the variable to map
	 * @param image the expected image of the variable
	 * @return <code>true</code> iff the mapping is compatible with
	 * the substitution
	 */
	private static boolean addConsistentMapping(
			Substitution substitution,
			Variable variable,
			Term image) {

		Term existingImage = substitution.get(variable);
		if (existingImage == null)
			return substitution.add(variable, image);

		return existingImage.deepEquals(image);
	}

	/**
	 * Attempts to build the pattern fact obtained by applying
	 * Proposition 2 of that article to the provided rules.
	 * <p>
	 * The first rule is expected to be a fact and the second one
	 * a binary rule. The method returns <code>null</code> when
	 * the pair does not satisfy the hypotheses of the proposition,
	 * or when the resulting pattern fact cannot be built.
	 *
	 * @param r1 the fact to be checked
	 * @param r2 the binary rule to be checked
	 * @return the pattern fact produced by Proposition 2 of
	 * that article, or <code>null</code> if no such fact
	 * can be built
	 */
	public static PatternRuleLp tryBuildPatternFactWithProp2Iclp25(
			RuleLp r1, RuleLp r2) {

		// It is supposed that r1 is a fact and
		// r2 is binary.

		Function u1 = r1.getHead();
		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);

		return Prop2PatternFactSearch.tryBuild(u1, u2, v2);
	}

	/**
	 * Attempts to build a pattern fact from a binary rule
	 * that shifts terms through a common unary context.
	 * <p>
	 * More precisely, this method considers the following
	 * situations:
	 * <ol>
	 * <li>
	 * <code>r1 = c(s, x')</code> and
	 * <code>r2 = c(c1^a(x), y) :- c(x, c1^b(y))</code>
	 * </li>
	 * <li>
	 * <code>r1 = c(s, x', x')</code> and
	 * <code>r2 = c(c1^a(x), y, z) :- c(x, c1^b(y), z)</code>
	 * </li>
	 * </ol>
	 * where
	 * <code>x',x,y,z</code> are variables,
	 * <code>x,y,z</code> are distinct,
	 * <code>s</code> is a ground term,
	 * <code>c,c1</code> are ground 1-contexts and
	 * <code>a,b</code> are non-zero naturals.
	 *
	 * @param r1 the fact to be checked
	 * @param r2 the binary rule to be checked
	 * @return the pattern fact
	 * <code>c(c1^{a,0}(s), y) :- e^*</code> or
	 * <code>c(c1^{a,0}(s), y, c1^{b,0}(y)) :- e^*</code>
	 * depending on the situation, or <code>null</code>
	 * if no such fact can be built
	 */
	public static PatternRuleLp tryBuildPatternFactFromContextShift(
			RuleLp r1, RuleLp r2) {

		// It is supposed that r1 is a fact
		// and r2 is binary.

		Function u1 = r1.getHead();
		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);

		return ContextShiftPatternFactSearch.tryBuild(u1, u2, v2);
	}

	/**
	 * Attempts to build a pattern fact from two binary rules
	 * that shift two arguments through a common unary context.
	 * <p>
	 * More precisely, this method considers the following situation:
	 * <code>r1 = p(s1, s2)</code> and
	 * <code>r2 = p(c^a(x), y) :- p(x, y)</code>
	 * <code>r3 = p(x, c^b(y)) :- p(x, y)</code>
	 * where <code>s1, s2</code> are variable
	 * disjoint terms, <code>c</code> is a ground
	 * 1-context, <code>x, y</code> are distinct
	 * variables and <code>a, b</code> are naturals.
	 *
	 * @param r1 the fact to be checked
	 * @param r2 the first binary rule to be checked
	 * @param r3 the second binary rule to be checked
	 * @return the pattern fact
	 * <code>p(c^{a,0}(s1), c^{b,0}(s2)) :- e^*</code>,
	 * or <code>null</code> if no such fact can be built
	 */
	public static PatternRuleLp tryBuildPatternFactFromTwoContextShifts(
			RuleLp r1, RuleLp r2, RuleLp r3) {

		// It is supposed that r1 is a fact and
		// r2,r3 are binary.

		Function u1 = r1.getHead();
		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);
		Function u3 = r3.getHead();
		Function v3 = r3.getBody(0);

		return TwoContextShiftPatternFactSearch.tryBuild(u1, u2, v2, u3, v3);
	}
}
