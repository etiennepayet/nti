/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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
import java.util.HashMap;
import java.util.LinkedList;

import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.PatternTerm;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Applies the logic-program pattern unfolding operator to one rule.
 *
 * <p>The operator and its simple-pattern restriction are described in
 * E. Payet,
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10"><i>Recurrent Pairs
 * Revisited</i></a>, LOPSTR 2025, LNCS 16117, pp. 154--164, 2026, and
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class RuleLpPatternUnfolder {

	/**
	 * Unfolds the given rule once using the given collection of rules.
	 * <p>
	 * Applies the T^{\pi}_{P,B} operator of Payet (LOPSTR 2025), cited in
	 * the class documentation, to the provided rule.
	 * <p>
	 * It is supposed that the provided collections consist of
	 * pattern rules (p,q) where both p and q are simple pattern
	 * terms (see Definition 9 of that article).
	 *
	 * @param sourceRule the logic programming rule to unfold
	 * @param unfoldingRules a collection of rules for unfolding
	 * <code>sourceRule</code>
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 * @throws IllegalArgumentException if the given iteration
	 * is negative or zero
	 */
	public static Collection<PatternRuleLp> unfold(
			RuleLp sourceRule,
			Collection<PatternRuleLp> unfoldingRules,
			int iteration) {

		return unfoldWithCandidates(
				sourceRule,
				ignored -> unfoldingRules,
				iteration);
	}

	/**
	 * Unfolds the given rule using candidates selected by left-hand predicate.
	 *
	 * @param sourceRule the logic programming rule to unfold
	 * @param unfoldingRuleIndex the indexed rules available for unfolding
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 */
	static Collection<PatternRuleLp> unfold(
			RuleLp sourceRule,
			PatternUnfoldingRuleIndex unfoldingRuleIndex,
			int iteration) {

		return unfoldWithCandidates(
				sourceRule,
				unfoldingRuleIndex,
				iteration);
	}

	/**
	 * Unfolds the given rule using the provided candidate selector.
	 *
	 * @param sourceRule the logic programming rule to unfold
	 * @param candidateSelector the unfolding-candidate selector
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 */
	private static Collection<PatternRuleLp> unfoldWithCandidates(
			RuleLp sourceRule,
			CandidateSelector candidateSelector,
			int iteration) {

		if (iteration <= 0)
			throw new IllegalArgumentException(
					"unfolding a rule with a negative iteration");

		// The thread running this unfolding.
		Thread currentThread = Thread.currentThread();

		LinkedList<PatternRuleLp> result = new LinkedList<>();

		// Below, we implement a slight modification of T^{\pi}_{P,B}.
		// Generated pattern rules are associated with their iteration
		// number. We generate a new rule in 'result' only when we
		// have used a rule of the immediately preceding iteration.
		// Hence, the instructions
		// {@code if (rule.getIteration() == iteration - 1)...} and
		// {@code if (latestSourceIteration == iteration - 1)...}
		// below before adding something to result.

		LinkedList<PatternRuleLpInProgress> rulesInProgress = new LinkedList<>();
		rulesInProgress.add(new PatternRuleLpInProgress(0));

		int lastIndex = sourceRule.getBodyLength() - 1;
		for (int bodyIndex = 0; bodyIndex <= lastIndex; bodyIndex++) {
			if (currentThread.isInterrupted()) break;

			// Suppose that sourceRule has the form h <- b_1,...,b_n.
			// The invariant of this for loop is: at that point,
			// b_1,...,b_{bodyIndex-1} have been unfolded with facts and
			// the list 'rulesInProgress' contains all the
			// corresponding rules in progress.
			rulesInProgress = unfoldAtBodyIndex(
					sourceRule,
					bodyIndex,
					iteration,
					rulesInProgress,
					candidateSelector.candidatesFor(
							sourceRule.getBody(bodyIndex)),
					result);
		}

		return result;
	}

	/**
	 * Unfolds every rule in progress at one body index.
	 *
	 * @param sourceRule the logic programming rule being unfolded
	 * @param bodyIndex the index of the body atom currently being unfolded
	 * @param iteration the current iteration of the unfolding operator
	 * @param rulesInProgress the rules obtained by unfolding the preceding
	 * body atoms with facts
	 * @param unfoldingRules the pattern rules available for unfolding the
	 * current body atom
	 * @param result the collection receiving completed rules produced at the
	 * current iteration
	 * @return the rules in progress for the next body index
	 */
	private static LinkedList<PatternRuleLpInProgress> unfoldAtBodyIndex(
			RuleLp sourceRule,
			int bodyIndex,
			int iteration,
			Collection<PatternRuleLpInProgress> rulesInProgress,
			Collection<PatternRuleLp> unfoldingRules,
			Collection<PatternRuleLp> result) {
		LinkedList<PatternRuleLpInProgress> nextRulesInProgress =
				new LinkedList<>();
		Thread currentThread = Thread.currentThread();

		for (PatternRuleLpInProgress rule : rulesInProgress) {
			if (currentThread.isInterrupted()) break;

			unfoldRuleInProgress(
					sourceRule,
					bodyIndex,
					iteration,
					rule,
					unfoldingRules,
					nextRulesInProgress,
					result);
		}

		return nextRulesInProgress;
	}

	/**
	 * Unfolds one rule in progress at the selected body index.
	 *
	 * @param sourceRule the logic programming rule being unfolded
	 * @param bodyIndex the index of the body atom currently being unfolded
	 * @param iteration the current iteration of the unfolding operator
	 * @param rule the rule in progress obtained from the preceding body atoms
	 * @param unfoldingRules the pattern rules available for unfolding the
	 * current body atom
	 * @param nextRulesInProgress the collection receiving rules that have used
	 * a fact and must continue at the next body index
	 * @param result the collection receiving completed rules produced at the
	 * current iteration
	 */
	private static void unfoldRuleInProgress(
			RuleLp sourceRule,
			int bodyIndex,
			int iteration,
			PatternRuleLpInProgress rule,
			Collection<PatternRuleLp> unfoldingRules,
			LinkedList<PatternRuleLpInProgress> nextRulesInProgress,
			Collection<PatternRuleLp> result) {
		PatternSubstitution patternSubstitution =
				rule.getPatternSubstitution();
		if (patternSubstitution == null) return;

		// First, unfold this rule with id but only if the
		// resulting rule belongs to the current iteration.
		if (rule.getIteration() == iteration - 1)
			result.add(unfoldWithIdentity(
					sourceRule, bodyIndex, patternSubstitution, iteration));

		if (unfoldingRules.isEmpty()) return;

		PatternTerm currentBodyAtom =
				SimplePatternTerm.tryBuild(
						sourceRule.getBody(bodyIndex),
						patternSubstitution);

		// Then, unfold this rule with the provided unfolding rules.
		Thread currentThread = Thread.currentThread();
		for (PatternRuleLp unfoldingRuleCandidate : unfoldingRules) {
			if (currentThread.isInterrupted()) break;
			if (currentBodyAtom.getRootSymbol() ==
					unfoldingRuleCandidate.getLeft().getRootSymbol())
				result.addAll(unfoldAtIndex(
						sourceRule,
						bodyIndex,
						unfoldingRuleCandidate,
						rule,
						currentBodyAtom,
						nextRulesInProgress,
						iteration));
		}
	}

	/**
	 * Unfolds the selected body atom with identity.
	 *
	 * @param sourceRule the rule whose body atom is unfolded
	 * @param bodyIndex the selected body atom index
	 * @param patternSubstitution the pattern substitution computed
	 * so far during the unfolding
	 * @param iteration the current iteration of the unfolding operator
	 * @return the rule produced by identity unfolding
	 */
	private static PatternRuleLp unfoldWithIdentity(
			RuleLp sourceRule,
			int bodyIndex,
			PatternSubstitution patternSubstitution,
			int iteration) {

		HashMap<Term,Term> copies = new HashMap<>();
		Function unfoldedHead =
				(Function) sourceRule.getHead().deepCopy(copies);
		Function unfoldedBodyAtom =
				(Function) sourceRule.getBody(bodyIndex).deepCopy(copies);
		PatternSubstitution copiedPatternSubstitution =
				patternSubstitution.deepCopy(copies);

		return PatternRuleLp.tryBuild(
				unfoldedHead, copiedPatternSubstitution,
				unfoldedBodyAtom, copiedPatternSubstitution,
				iteration);
	}

	/**
	 * Unfolds the atom at index <code>bodyIndex</code> in the body of
	 * the source rule using the provided pattern rule.
	 *
	 * @param sourceRule the rule whose body atom is unfolded
	 * @param bodyIndex the index of the current atom to consider in
	 * the body of <code>sourceRule</code>
	 * @param unfoldingRule the rule that we have to use to unfold
	 * @param rule the rule in progress computed so far during the unfolding
	 * @param currentBodyAtom the current body atom with the rule-in-progress
	 * pattern substitution applied
	 * @param rulesInProgress the collection to which rules still in
	 * progress must be added
	 * @param iteration the current iteration of the unfolding
	 * operator
	 * @return a collection of unfolded rules
	 */
	private static Collection<PatternRuleLp> unfoldAtIndex(
			RuleLp sourceRule,
			int bodyIndex,
			PatternRuleLp unfoldingRule,
			PatternRuleLpInProgress rule,
			PatternTerm currentBodyAtom,
			LinkedList<PatternRuleLpInProgress> rulesInProgress,
			int iteration) {

		// The thread running this unfolding.
		Thread currentThread = Thread.currentThread();

		// The collection to return at the end.
		LinkedList<PatternRuleLp> result = new LinkedList<>();

		int latestSourceIteration =
				Math.max(rule.getIteration(), unfoldingRule.getIteration());
		UnfoldingStep unfoldingStep = new UnfoldingStep(
				sourceRule,
				bodyIndex,
				iteration,
				latestSourceIteration,
				latestSourceIteration == iteration - 1);

		PatternSubstitution rulePatternSubstitution =
				rule.getPatternSubstitution();

		// We unify the current atom in the body of this rule with the
		// left-hand side of the rule used to unfold. The returned
		// unifiers are the MGUs computed for the current atom.
		Collection<? extends PatternSubstitution> unifiers =
				currentBodyAtom.unifyWith(unfoldingRule);

		for (PatternSubstitution unifier : unifiers) {
			if (currentThread.isInterrupted()) break;

			PatternSubstitution composedUnifier =
					rulePatternSubstitution.composeWith(unifier);
			result.addAll(unfoldWithUnifier(
					unfoldingStep,
					unfoldingRule,
					composedUnifier,
					rulesInProgress));
		}

		return result;
	}

	/**
	 * Applies one composed unifier to the selected unfolding step.
	 *
	 * @param unfoldingStep the source rule, selected body index, and iteration
	 * information for this unfolding step
	 * @param unfoldingRule the pattern rule used for unfolding
	 * @param composedUnifier the current rule substitution composed with one MGU
	 * @param rulesInProgress the collection receiving fact unfoldings that must
	 * continue at the next body index
	 * @return the completed pattern rules produced by this unifier
	 */
	private static Collection<PatternRuleLp> unfoldWithUnifier(
			UnfoldingStep unfoldingStep,
			PatternRuleLp unfoldingRule,
			PatternSubstitution composedUnifier,
			LinkedList<PatternRuleLpInProgress> rulesInProgress) {
		LinkedList<PatternRuleLp> result = new LinkedList<>();

		if (unfoldingRule.isFact()) {
			if (!unfoldingStep.isLastBodyAtom()) {
				// The current atom is not the last one: unfolding with a
				// fact produces a rule that still has to be processed.
				rulesInProgress.addLast(new PatternRuleLpInProgress(
						composedUnifier,
						unfoldingStep.latestSourceIteration()));
			}
			else if (unfoldingStep.reachesCurrentIteration()) {
				result.add(unfoldLastAtomWithFact(
						unfoldingStep.sourceRule(),
						composedUnifier,
						unfoldingStep.iteration()));
			}
		}
		else if (unfoldingStep.reachesCurrentIteration()) {
			result.addAll(unfoldWithNonFactRule(
					unfoldingStep.sourceRule(),
					unfoldingRule,
					composedUnifier,
					unfoldingStep.iteration()));
		}

		return result;
	}

	/**
	 * Unfolds the last body atom of the source rule with a fact.
	 *
	 * @param sourceRule the rule whose last body atom is unfolded
	 * @param composedUnifier the unifier computed for this unfolding step
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting pattern fact
	 */
	private static PatternRuleLp unfoldLastAtomWithFact(
			RuleLp sourceRule,
			PatternSubstitution composedUnifier,
			int iteration) {

		HashMap<Term,Term> copies = new HashMap<>();

		return PatternRuleLp.tryBuildFact(
				(Function) sourceRule.getHead().deepCopy(copies),
				composedUnifier.deepCopy(copies),
				iteration);
	}

	/**
	 * Unfolds the current body atom with a non-fact pattern rule.
	 *
	 * @param sourceRule the rule whose body atom is unfolded
	 * @param unfoldingRule the non-fact pattern rule used for unfolding
	 * @param composedUnifier the unifier computed for this unfolding step
	 * @param iteration the current iteration of the unfolding operator
	 * @return the resulting unfolded rules
	 */
	private static Collection<PatternRuleLp> unfoldWithNonFactRule(
			RuleLp sourceRule,
			PatternRuleLp unfoldingRule,
			PatternSubstitution composedUnifier,
			int iteration) {

		LinkedList<PatternRuleLp> result = new LinkedList<>();
		PatternTerm right = unfoldingRule.getRight();
		PatternSubstitution rightPatternSubstitution =
				right.getPatternSubstitution().composeWith(composedUnifier);

		if (rightPatternSubstitution != null) {
			HashMap<Term, Term> copies = new HashMap<>();
			result.add(PatternRuleLp.tryBuild(
					(Function) sourceRule.getHead().deepCopy(copies),
					composedUnifier.deepCopy(copies),
					(Function) right.getBaseTerm().deepCopy(copies),
					rightPatternSubstitution.deepCopy(copies),
					iteration));
		}

		return result;
	}

	/**
	 * Disables construction.
	 */
	private RuleLpPatternUnfolder() {
	}

	/** Selects the unfolding candidates for a body atom. */
	@FunctionalInterface
	interface CandidateSelector {

		/**
		 * Returns the rules that may unfold the given body atom.
		 *
		 * @param bodyAtom the body atom to unfold
		 * @return its unfolding candidates
		 */
		Collection<PatternRuleLp> candidatesFor(Function bodyAtom);
	}

	/** The stable source and iteration information for one unfolding step. */
	private record UnfoldingStep(
			RuleLp sourceRule,
			int bodyIndex,
			int iteration,
			int latestSourceIteration,
			boolean reachesCurrentIteration) {

		private boolean isLastBodyAtom() {
			return bodyIndex == sourceRule.getBodyLength() - 1;
		}
	}
}
