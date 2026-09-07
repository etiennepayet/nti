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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import fr.univreunion.nti.Printer;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.patternunfolding.patternproducer.CorrectPatternRuleTrsProducer;

/**
 * Prints the iterations of the TRS pattern unfolding operator.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class TrsPatternUnfolder {

	/**
	 * Applies the pattern unfolding operator
	 * <code>n</code> times to the provided TRS
	 * and displays the result.
	 *
	 * @param trs the TRS to unfold
	 * @param n the number of iterations
	 * of the pattern unfolding operator
	 * @param printer the printer used
	 * to display the result
	 */
	public static void printUnfoldings(Trs trs, int n, Printer printer) {

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		Collection<PatternRuleTrs> correct = CorrectPatternRuleTrsCollector.collectFrom(trs);

		// Some data structures used for unfolding.
		List<PatternRuleTrs> rulesToUnfold = new ArrayList<>();
		List<PatternRuleTrs> unfolded = new ArrayList<>();

		// We track the number of generated unfolded rules.
		int generatedRuleTotal = 0;

		printer.println("== Pattern unfoldings ==");

		for (int i = 0; i <= n; i++) {
			if (currentThread.isInterrupted()) break;

			printer.println("** Iteration " + i + ":");

			int generatedRuleCount;

			if (i == 0) {
				// At the first iteration, we have to initialize the
				// set of unfolded rules: we initialize it to the
				// pattern rules occurring in the provided problem.
				// We also check whether a pattern rule is a
				// nontermination witness.
				initializeUnfoldedRules(trs, unfolded, currentThread);
				generatedRuleCount = trs.size();
			}
			else {
				generatedRuleCount = unfoldNextIteration(
						rulesToUnfold,
						unfolded,
						correct,
						i,
						currentThread);
			}
			generatedRuleTotal += generatedRuleCount;

			printIterationResult(unfolded, generatedRuleCount, printer);
		}

		printer.println("================");
		printer.println("Total number of generated unfolded rules = " + generatedRuleTotal);
	}

	/**
	 * Initializes the unfolded rules with the trivial pattern rules
	 * associated with the provided TRS.
	 *
	 * @param trs the TRS whose rules are lifted to trivial pattern rules
	 * @param unfolded the collection receiving the initialized rules
	 * @param currentThread the thread running the unfolding
	 */
	private static void initializeUnfoldedRules(
			Trs trs,
			Collection<PatternRuleTrs> unfolded,
			Thread currentThread) {

		for (RuleTrs rule : trs) {
			if (currentThread.isInterrupted()) break;
			unfolded.add(
					CorrectPatternRuleTrsProducer.buildTrivialPatternRule(rule));
		}
	}

	/**
	 * Computes one positive iteration of the pattern unfolding operator.
	 *
	 * @param rulesToUnfold the workspace receiving the rules from the
	 * preceding iteration
	 * @param unfolded the collection receiving the rules generated during
	 * this iteration
	 * @param correct the correct pattern rules used by the unfolding operator
	 * @param iteration the positive iteration number
	 * @param currentThread the thread running the unfolding
	 * @return the number of rules generated during the iteration
	 */
	private static int unfoldNextIteration(
			List<PatternRuleTrs> rulesToUnfold,
			List<PatternRuleTrs> unfolded,
			Collection<PatternRuleTrs> correct,
			int iteration,
			Thread currentThread) {

		rulesToUnfold.clear();
		rulesToUnfold.addAll(unfolded);
		unfolded.clear();

		int generatedRuleCount = 0;
		for (PatternRuleTrs rule : rulesToUnfold) {
			if (currentThread.isInterrupted()) break;

			// We unfold 'rule' and check whether nontermination
			// can be proved from the new unfolded rules.
			Collection<PatternRuleTrs> generatedRules =
					rule.unfold(correct, iteration, null);
			generatedRuleCount += generatedRules.size();
			unfolded.addAll(generatedRules);
		}

		return generatedRuleCount;
	}

	/**
	 * Prints the pattern rules generated during one iteration and their count.
	 *
	 * @param unfolded the rules generated during the iteration
	 * @param generatedRuleCount the number of generated rules
	 * @param printer the printer used to display the result
	 */
	private static void printIterationResult(
			Iterable<PatternRuleTrs> unfolded,
			int generatedRuleCount,
			Printer printer) {

		for (PatternRuleTrs rule : unfolded)
			printer.println(rule);
		printer.println(
				"** " + generatedRuleCount + " unfolded rules generated");
	}

	/** Prevents instantiation. */
	private TrsPatternUnfolder() {}
}
