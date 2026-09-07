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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.patternproducer.CorrectPatternRuleTrsProducer;

/**
 * Collects correct pattern rules for a TRS.
 * <p>
 * The collected pattern rules are meant to be used as the set
 * <code>R</code> in the unfolding operator of Definition 13 of E. Payet,
 * <a href="https://www.imn.htwk-leipzig.de/~waldmann/WST2025/proceedings/WST2025_paper_2.pdf"><i>Non-Termination
 * of Term Rewrite Systems Using Pattern Unfolding</i></a>, Proceedings of the
 * 20th International Workshop on Termination (WST 2025), 2025. This is the
 * TRS adaptation of
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.
 * <p>
 * This class orchestrates the global traversal of the rules of a
 * TRS. The construction of each local pattern rule is delegated to
 * {@link CorrectPatternRuleTrsProducer}.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class CorrectPatternRuleTrsCollector {

	/**
	 * Collects the correct pattern rules generated from the
	 * provided TRS rules.
	 *
	 * @param rules the rules of the TRS
	 * @return a collection of pattern rules that are correct
	 * w.r.t. the provided rules
	 */
	public static Collection<PatternRuleTrs> collectFrom(Iterable<RuleTrs> rules) {
		LinkedList<RuleTrs> ruleList = copyOf(rules);

		// The collection to be returned at the end.
		LinkedList<PatternRuleTrs> result = new LinkedList<>();

		// A set that contains the rules that have been
		// successfully used to build a non-trivial pattern rule.
		Set<RuleTrs> used = new HashSet<>();

		// We first try to construct non-trivial
		// pattern rules from pairs of rules.
		for (RuleTrs r1 : ruleList)
			for (RuleTrs r2 : ruleList)
				if (r1 != r2) {
					addPatternRulesFromPair(r1, r2, result, used);
					addTwoContextShiftPatternRules(
							r1, r2, ruleList, result, used);
				}

		// Finally, we add trivial pattern rules
		// for rules that were not used above.
		for (RuleTrs r : ruleList)
			if (!used.contains(r))
				// If r = (left -> right) then we add
				// (left^* -> right^*) to the result.
				result.add(CorrectPatternRuleTrsProducer.buildTrivialPatternRule(r));

		return result;
	}

	/**
	 * Adds the pattern rules produced from an ordered pair of distinct
	 * TRS rules.
	 * <p>
	 * Proposition 9 of the Payet (WST 2025) paper cited in the class
	 * documentation is tried first. The additional
	 * context-shift schema is tried only when Proposition 9 produces no rule.
	 *
	 * @param r1 the first rule of the ordered pair
	 * @param r2 the second rule of the ordered pair
	 * @param result the collection receiving the produced pattern rules
	 * @param used the set receiving the rules used by a successful production
	 */
	private static void addPatternRulesFromPair(
			RuleTrs r1,
			RuleTrs r2,
			Collection<PatternRuleTrs> result,
			Set<RuleTrs> used) {

		// Proposition 9 of [Payet, WST'25].
		Collection<PatternRuleTrs> correctRules =
				CorrectPatternRuleTrsProducer.collectPatternRulesWithProp9Wst25(r1, r2);
		if (correctRules.isEmpty())
			// Additional context-shift schema.
			correctRules = CorrectPatternRuleTrsProducer.collectPatternRulesFromContextShift(r1, r2);

		if (!correctRules.isEmpty()) {
			used.add(r1); // r1 has been used
			used.add(r2); // r2 has been used
			result.addAll(correctRules);
		}
	}

	/**
	 * Adds the pattern rules produced by the two-context-shift schema
	 * from an ordered pair and each possible distinct third rule.
	 *
	 * @param r1 the first rule of the ordered triple
	 * @param r2 the second rule of the ordered triple
	 * @param rules the rules supplying the third rule
	 * @param result the collection receiving the produced pattern rules
	 * @param used the set receiving the rules used by a successful production
	 */
	private static void addTwoContextShiftPatternRules(
			RuleTrs r1,
			RuleTrs r2,
			Iterable<RuleTrs> rules,
			Collection<PatternRuleTrs> result,
			Set<RuleTrs> used) {

		for (RuleTrs r3 : rules)
			if (r3 != r1 && r3 != r2) {
				// Additional schema with two context shifts.
				PatternRuleTrs patternRule =
						CorrectPatternRuleTrsProducer
								.tryBuildPatternRuleFromTwoContextShifts(
										r1, r2, r3);
				if (patternRule != null) {
					used.add(r1); // r1 has been used
					used.add(r2); // r2 has been used
					used.add(r3); // r3 has been used
					result.add(patternRule);
				}
			}
	}

	/**
	 * Copies the provided rules into a list so that they
	 * can be traversed several times.
	 *
	 * @param rules the rules to copy
	 * @return a list containing the provided rules
	 */
	private static LinkedList<RuleTrs> copyOf(Iterable<RuleTrs> rules) {
		LinkedList<RuleTrs> result = new LinkedList<>();

		for (RuleTrs r : rules)
			result.add(r);

		return result;
	}

	/** Prevents instantiation. */
	private CorrectPatternRuleTrsCollector() {}
}
