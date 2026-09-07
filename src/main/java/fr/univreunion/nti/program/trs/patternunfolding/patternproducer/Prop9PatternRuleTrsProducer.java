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
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Produces correct TRS pattern rules using Proposition 9 of E. Payet,
 * <a href="https://www.imn.htwk-leipzig.de/~waldmann/WST2025/proceedings/WST2025_paper_2.pdf"><i>Non-Termination
 * of Term Rewrite Systems Using Pattern Unfolding</i></a>, Proceedings of the
 * 20th International Workshop on Termination (WST 2025), 2025. The underlying
 * pattern formalism is from
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class Prop9PatternRuleTrsProducer {

	/** Prevents instantiation. */
	private Prop9PatternRuleTrsProducer() {}

	/**
	 * Collects all pattern rules produced from the provided variable-disjoint rules.
	 *
	 * @param firstRule the rule <code>r</code> of Proposition 9
	 * @param secondRule the rule <code>r'</code> of Proposition 9
	 * @return the produced pattern rules, in candidate-position order
	 */
	static Collection<PatternRuleTrs> collectFrom(
			RuleTrs firstRule, RuleTrs secondRule) {
		// It is supposed that firstRule and secondRule
		// are variable disjoint.

		// The collection to be returned at the end.
		LinkedList<PatternRuleTrs> result = new LinkedList<>();

		FunctionSymbol rootSymbol = firstRule.getLeft().getRootSymbol();
		Term firstRight = firstRule.getRight();

		// We want the context c of Prop. 9 to
		// be non-empty. Hence, we forbid the
		// case where firstRight is a variable.
		if (firstRight instanceof Variable) return result;

		// We consider all possible candidates for the
		// subterm c(x_1,...,x_m) of v in Prop. 9.
		for (Position position : firstRight) {
			Term candidateSubterm = firstRight.get(position);
			if (!(candidateSubterm instanceof Variable) &&
					candidateSubterm.getRootSymbol() == rootSymbol) {
				// We want the context c of Prop. 9 to be
				// non-empty. Hence, we forbid the case
				// where candidateSubterm is a variable.
				PatternRuleTrs patternRule = tryBuildAt(
						firstRule, secondRule, position, candidateSubterm);
				if (patternRule != null) result.add(patternRule);
			}
		}

		return result;
	}

	/**
	 * Attempts to build one rule from one candidate subterm of <code>firstRule</code>.
	 *
	 * @param firstRule the rule <code>r</code> of Proposition 9
	 * @param secondRule the rule <code>r'</code> of Proposition 9
	 * @param position a non-variable position in the right-hand side of
	 * <code>firstRule</code>
	 * @param candidateSubterm the candidate subterm at {@code position}
	 * @return the produced pattern rule, or <code>null</code> if the candidate fails
	 */
	private static PatternRuleTrs tryBuildAt(
			RuleTrs firstRule,
			RuleTrs secondRule,
			Position position,
			Term candidateSubterm) {
		// It is supposed that firstRule and secondRule are
		// variable disjoint.
		// It is supposed that candidateSubterm is a non-variable
		// subterm of the right-hand side of firstRule.

		Prop9CandidateAnalysis analysis = analyzeCandidate(
				firstRule.getLeft(), secondRule.getLeft(), candidateSubterm);
		if (analysis == null) return null;

		// Then, we check whether sigma is suitable and
		// firstLeft corresponds to the same context c
		// as secondLeft and candidateSubterm.
		if (!isSuitable(analysis.sigma()) ||
				!analysis.firstLeftContext().deepEquals(
						analysis.secondLeftContext()) ||
				!analysis.firstLeftContext().deepEquals(candidateSubterm))
			return null;

		// Finally, we consider the context c' of Prop. 9.
		Variable contextVariable = new Variable();
		Term cPrime = firstRule.getRight().replace(position, contextVariable);
		// We check whether c' is ground.
		if (1 < cPrime.getVariables().size()) return null;

		// Here, the pair (firstRule,secondRule) satisfies the conditions
		// of Prop. 9 of [Payet, WST'25]. Hence, we can produce a pattern
		// rule from it.

		// The pumping and closing substitutions
		// of the right-hand side of the produced
		// pattern rule.
		Substitution rho = new Substitution();
		rho.add(contextVariable, cPrime);
		Substitution nu = new Substitution();
		Map<Term, Term> copies = new HashMap<>();
		nu.add(contextVariable, secondRule.getRight().deepCopy(copies));

		return PatternRuleTrs.tryBuild(
				SimplePatternTerm.tryBuild(candidateSubterm.deepCopy(copies),
						analysis.sigma().deepCopy(copies),
						analysis.mu().deepCopy(copies)),
				SimplePatternTerm.tryBuild(contextVariable, rho, nu),
				0);
	}

	/** Analyzes one candidate subterm and computes sigma, mu, and context c. */
	private static Prop9CandidateAnalysis analyzeCandidate(
			Function firstLeft,
			Function secondLeft,
			Term candidateSubterm) {
		Substitution sigma = new Substitution();
		Substitution mu = new Substitution();
		Term firstLeftContext = firstLeft.shallowCopy();
		Term secondLeftContext = secondLeft.shallowCopy();
		Set<Variable> identityVariables = new HashSet<>();

		for (Position candidatePosition : candidateSubterm) {
			Term firstLeftAtPosition = firstLeft.get(candidatePosition);
			if (firstLeftAtPosition == null) return null;

			Term secondLeftAtPosition = secondLeft.get(candidatePosition);
			if (secondLeftAtPosition == null) return null;

			Term candidateAtPosition = candidateSubterm.get(candidatePosition);
			if (!(candidateAtPosition instanceof Variable variable)) continue;

			if (!completeSigma(
					sigma, identityVariables, variable, firstLeftAtPosition) ||
					!completeMu(mu, variable, secondLeftAtPosition))
				return null;

			if (firstLeftAtPosition != variable)
				firstLeftContext = firstLeftContext.replace(
						candidatePosition, variable);
			if (secondLeftAtPosition != variable)
				secondLeftContext = secondLeftContext.replace(
						candidatePosition, variable);
		}

		return new Prop9CandidateAnalysis(
				sigma, mu, firstLeftContext, secondLeftContext);
	}

	/** Completes sigma for one variable occurrence when possible. */
	private static boolean completeSigma(
			Substitution sigma,
			Set<Variable> identityVariables,
			Variable variable,
			Term firstLeftAtPosition) {
		if (identityVariables.contains(variable))
			return firstLeftAtPosition == variable;

		Term sigmaImage = sigma.get(variable);
		if (sigmaImage != null)
			return sigmaImage.deepEquals(firstLeftAtPosition);

		if (variable == firstLeftAtPosition) {
			identityVariables.add(variable);
			return true;
		}

		Set<Variable> variablesAtPosition =
				firstLeftAtPosition.getVariables();
		if (variablesAtPosition.size() != 1 ||
				!variablesAtPosition.contains(variable))
			return false;

		sigma.add(variable, firstLeftAtPosition);
		return true;
	}

	/** Completes mu for one variable occurrence when possible. */
	private static boolean completeMu(
			Substitution mu,
			Variable variable,
			Term secondLeftAtPosition) {
		Term muImage = mu.get(variable);
		if (muImage != null)
			return muImage.deepEquals(secondLeftAtPosition);

		if (variable != secondLeftAtPosition)
			mu.add(variable, secondLeftAtPosition);
		return true;
	}

	/** Checks whether the provided pumping substitution is suitable. */
	private static boolean isSuitable(Substitution sigma) {
		Set<Variable> domain = sigma.getDomain();

		for (Map.Entry<Variable, Term> mapping : sigma) {
			Variable variable = mapping.getKey();

			// We check whether 'variable' is the only
			// variable of Dom(sigma) that occurs in
			// sigma(variable).
			Set<Variable> domainVariables = mapping.getValue().getVariables();
			domainVariables.retainAll(domain);

			if (domainVariables.size() != 1)
				// Here, no variable of dom occurs in sigma(variable) or
				// at least two variables of dom occur in sigma(variable).
				return false;
			// Here, exactly one variable of dom occurs in sigma(variable).
			// We check whether it is 'variable'.
			if (domainVariables.iterator().next() != variable) return false;
		}

		return true;
	}

	/** The substitutions and context computed for one candidate subterm. */
	private record Prop9CandidateAnalysis(
			Substitution sigma,
			Substitution mu,
			Term firstLeftContext,
			Term secondLeftContext) {}
}
