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
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.patternunfolding.patternproducer.CorrectPatternRuleLpProducer;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Collects correct pattern rules for a logic program.
 * <p>
 * The collected pattern rules are meant to be used as the set
 * <code>B</code> in the unfolding operator of Definition 10 of E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.
 * <p>
 * This class orchestrates the global traversal of the rules of a
 * logic program. The construction of each local pattern rule is
 * delegated to {@link CorrectPatternRuleLpProducer}.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class CorrectPatternRuleLpCollector {

	/**
	 * Collects the correct pattern rules generated from the
	 * provided logic program rules.
	 *
	 * @param rules the rules of the logic program
	 * @return a collection of pattern rules that are correct
	 * w.r.t. the provided rules
	 */
	public static Collection<PatternRuleLp> collectFrom(Iterable<RuleLp> rules) {
		LinkedList<RuleLp> ruleList = copyOf(rules);

		// The collection to be returned at the end.
		LinkedList<PatternRuleLp> result = new LinkedList<>();

		// A set that contains the rules that have been
		// successfully used to build a non-trivial pattern rule.
		Set<RuleLp> used = new HashSet<>();

		// We first try to construct non-trivial
		// pattern facts from facts and binary rules.
		for (RuleLp r1 : ruleList)
			if (r1.isFact())
				for (RuleLp r2 : ruleList)
					if (r2.isBinary()) {
						addPatternFactFromPair(r1, r2, result, used);
						addTwoContextShiftPatternFacts(
								r1, r2, ruleList, result, used);
					}

		addPatternRulesFromUnusedRules(ruleList, used, result);

		return result;
	}

	/**
	 * Adds the pattern fact produced from a fact and a binary rule.
	 * <p>
	 * Proposition 2 of the Payet (2025) article cited in the class
	 * documentation is tried first. The additional
	 * context-shift schema is tried only when Proposition 2 produces no fact.
	 *
	 * @param r1 the fact of the ordered pair
	 * @param r2 the binary rule of the ordered pair
	 * @param result the collection receiving the produced pattern fact
	 * @param used the set receiving the rules used by a successful production
	 */
	private static void addPatternFactFromPair(
			RuleLp r1,
			RuleLp r2,
			Collection<PatternRuleLp> result,
			Set<RuleLp> used) {

		// Proposition 2 of [Payet, ICLP'25].
		PatternRuleLp patternFact =
				CorrectPatternRuleLpProducer
						.tryBuildPatternFactWithProp2Iclp25(r1, r2);
		if (patternFact == null)
			// Additional context-shift schema.
			patternFact = CorrectPatternRuleLpProducer
					.tryBuildPatternFactFromContextShift(r1, r2);

		if (patternFact != null) {
			used.add(r1); // r1 has been used
			used.add(r2); // r2 has been used
			result.add(patternFact);
		}
	}

	/**
	 * Adds pattern rules for the logic-program rules that were not used
	 * to produce a non-trivial pattern rule.
	 *
	 * @param rules the rules to inspect
	 * @param used the rules already used by a successful production
	 * @param result the collection receiving the produced pattern rules
	 */
	private static void addPatternRulesFromUnusedRules(
			Iterable<RuleLp> rules,
			Set<RuleLp> used,
			Collection<PatternRuleLp> result) {

		for (RuleLp rule : rules) {
			if (!used.contains(rule)) {
				if (rule.isFact()) {
					// We add h^* to the result, where h is the head of rule.
					SimplePatternTerm head =
							SimplePatternTerm.of(rule.getHead());
					result.add(PatternRuleLp.tryBuildFact(head, 0));
				}

				else if (rule.isBinary()) {
					PatternRuleLp patternRule = CorrectPatternRuleLpProducer
							.tryBuildPatternRuleWithProp2Iclp25(rule);
					if (patternRule != null) result.add(patternRule);
				}
			}
		}
	}

	/**
	 * Adds the pattern facts produced by the two-context-shift schema
	 * from a fact, a binary rule, and each possible distinct binary rule.
	 *
	 * @param r1 the fact of the ordered triple
	 * @param r2 the first binary rule of the ordered triple
	 * @param rules the rules supplying the second binary rule
	 * @param result the collection receiving the produced pattern facts
	 * @param used the set receiving the rules used by a successful production
	 */
	private static void addTwoContextShiftPatternFacts(
			RuleLp r1,
			RuleLp r2,
			Iterable<RuleLp> rules,
			Collection<PatternRuleLp> result,
			Set<RuleLp> used) {

		for (RuleLp r3 : rules)
			if (r3 != r2 && r3.isBinary()) {
				// Additional schema with two context shifts.
				PatternRuleLp patternFact = CorrectPatternRuleLpProducer
						.tryBuildPatternFactFromTwoContextShifts(
								r1, r2, r3);
				if (patternFact != null) {
					used.add(r1); // r1 has been used
					used.add(r2); // r2 has been used
					used.add(r3); // r3 has been used
					result.add(patternFact);
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
	private static LinkedList<RuleLp> copyOf(Iterable<RuleLp> rules) {
		LinkedList<RuleLp> result = new LinkedList<>();

		for (RuleLp r : rules)
			result.add(r);

		return result;
	}

	/** Prevents instantiation. */
	private CorrectPatternRuleLpCollector() {}
}
