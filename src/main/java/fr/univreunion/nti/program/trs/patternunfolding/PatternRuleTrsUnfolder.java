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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.patternunfolding;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.argument.ArgumentIclp25;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Orchestrates one unfolding iteration for a TRS pattern rule.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleTrsUnfolder {

	/**
	 * Unfolds the source rule once with the provided pattern rules.
	 *
	 * @param source the pattern rule to unfold
	 * @param patternRules the rules used for unfolding
	 * @param iteration the current unfolding iteration
	 * @param proof the proof to update when a witness is found
	 * @return the unfolded rules in generation order
	 */
	static Collection<PatternRuleTrs> unfold(
			PatternRuleTrs source,
			Collection<PatternRuleTrs> patternRules,
			int iteration,
			Proof proof) {

		List<PatternRuleTrs> result = new ArrayList<>();
		UnfoldingState state = new UnfoldingState(
				source, iteration, proof, result);
		Thread currentThread = Thread.currentThread();

		// For the moment, we only unfold forwards.
		SimplePatternTerm right = source.getRight();
		for (Position position : right) {
			if (currentThread.isInterrupted()) break;

			SimplePatternTerm rightAtPosition = right.get(position);
			if (!rightAtPosition.isVariable() && unfoldAtPosition(
					state, patternRules, position, rightAtPosition))
				return result;
		}

		return result;
	}

	/**
	 * Unfolds one non-variable position with the available pattern rules.
	 *
	 * @param state the stable inputs and accumulated output of the unfolding
	 * iteration
	 * @param patternRules the pattern rules available for unfolding
	 * @param position the selected non-variable position in the source right-hand
	 * side
	 * @param rightAtPosition the source right-hand-side subterm at
	 * {@code position}
	 * @return <code>true</code> if a nontermination witness was found
	 */
	private static boolean unfoldAtPosition(
			UnfoldingState state,
			Collection<PatternRuleTrs> patternRules,
			Position position,
			SimplePatternTerm rightAtPosition) {
		Thread currentThread = Thread.currentThread();

		for (PatternRuleTrs unfoldingRule : patternRules) {
			if (currentThread.isInterrupted()) break;

			if (unfoldWithRule(
					state, unfoldingRule, position, rightAtPosition))
				return true;
		}

		return false;
	}

	/**
	 * Unfolds one position with one pattern rule and its weakenings.
	 *
	 * @param state the stable inputs and accumulated output of the unfolding
	 * iteration
	 * @param unfoldingRule the pattern rule selected for unfolding
	 * @param position the selected position in the source right-hand side
	 * @param rightAtPosition the source right-hand-side subterm at
	 * {@code position}
	 * @return <code>true</code> if a nontermination witness was found
	 */
	private static boolean unfoldWithRule(
			UnfoldingState state,
			PatternRuleTrs unfoldingRule,
			Position position,
			SimplePatternTerm rightAtPosition) {
		Thread currentThread = Thread.currentThread();

		for (PatternRuleTrs weakenedSource : state.source().weaken(
				rightAtPosition, unfoldingRule.getLeft())) {
			if (currentThread.isInterrupted()) break;

			if (unfoldWeakenedSource(
					state,
					unfoldingRule,
					weakenedSource,
					position,
					rightAtPosition))
				return true;
		}

		return false;
	}

	/**
	 * Unfolds one weakened source with the compatible rule weakenings.
	 *
	 * @param state the stable inputs and accumulated output of the unfolding
	 * iteration
	 * @param unfoldingRule the original pattern rule selected for unfolding
	 * @param weakenedSource one weakened version of the source rule
	 * @param position the selected position in the source right-hand side
	 * @param sourceRightAtPosition the already constructed subterm of the
	 * original source at {@code position}
	 * @return <code>true</code> if a nontermination witness was found
	 */
	private static boolean unfoldWeakenedSource(
			UnfoldingState state,
			PatternRuleTrs unfoldingRule,
			PatternRuleTrs weakenedSource,
			Position position,
			SimplePatternTerm sourceRightAtPosition) {
		SimplePatternTerm weakenedRightAtPosition =
				weakenedSource == state.source()
						? sourceRightAtPosition
						: weakenedSource.getRight().get(position);
		Thread currentThread = Thread.currentThread();

		for (PatternRuleTrs weakenedRule : unfoldingRule.weaken(
				unfoldingRule.getLeft(), weakenedRightAtPosition)) {
			if (currentThread.isInterrupted()) break;

			PatternRuleTrs unfoldedRule = weakenedSource.unfoldForwardsWith(
					weakenedRule,
					position,
					weakenedRightAtPosition,
					state.iteration());
			if (unfoldedRule != null && state.add(unfoldedRule))
				return true;
		}

		return false;
	}

	/** Prevents instantiation of this utility class. */
	private PatternRuleTrsUnfolder() {
	}

	/** Stable inputs and accumulated output of one unfolding iteration. */
	private record UnfoldingState(
			PatternRuleTrs source,
			int iteration,
			Proof proof,
			Collection<PatternRuleTrs> result) {

		/**
		 * Adds a rule and reports whether it is the first requested witness.
		 *
		 * @param unfoldedRule the unfolded rule to add to the accumulated result
		 * @return <code>true</code> if the rule is a nontermination witness and a
		 * proof was provided
		 */
		private boolean add(PatternRuleTrs unfoldedRule) {
			this.result.add(unfoldedRule);

			if (this.proof != null &&
					unfoldedRule.getNonTerminatingTerm() != null) {
				this.proof.setArgument(new ArgumentIclp25(unfoldedRule));
				return true;
			}

			return false;
		}
	}
}
