/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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

package fr.univreunion.nti.program.trs.prooftech;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argument.ArgumentRootVariantCycle;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Searches for one or two root rewrite steps that return to a variant of the
 * starting term.
 *
 * @author <A HREF="mailto:etiennepayet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechRootVariantCycle implements ProofTechnique {

	/** Message emitted when the bounded search remains inconclusive. */
	private static final String NOT_FOUND_MESSAGE =
			"No root variant cycle found!";

	/** Maximum number of rules indexed by this bounded technique. */
	private static final int MAX_RULE_COUNT = 10_000;

	/** Maximum total length of the structural keys retained by the index. */
	private static final int MAX_INDEX_CHARACTER_COUNT = 32_000_000;

	/** Maximum number of candidate pairs validated structurally. */
	private static final int MAX_CANDIDATE_PAIR_COUNT = 100_000;

	/**
	 * Runs this technique on the specified TRS.
	 *
	 * @param trs the TRS to analyze
	 * @param context the context of the analysis
	 * @return the proof built by this technique
	 */
	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose("## Searching for a root variant cycle...");
		RootVariantIndex index = buildIndex(trs);
		if (index == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		int candidatePairCount = 0;
		for (RuleTrs first : index.rules()) {
			List<RuleTrs> candidates = index.rulesByLeft().get(
					canonical(first.getRight()));
			if (candidates != null)
				for (RuleTrs second : candidates) {
					if (++candidatePairCount > MAX_CANDIDATE_PAIR_COUNT) {
						proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
						return proof;
					}
					if (formsCycle(first, second)) {
						proof.printlnIfVerbose("Found a root variant cycle!");
						proof.setResult(Proof.ProofResult.NO);
						proof.setArgument(new ArgumentRootVariantCycle(first, second));
						return proof;
					}
				}
		}
		proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
		return proof;
	}

	/** Builds an insertion-ordered index of left-hand-side variants. */
	private static RootVariantIndex buildIndex(Trs trs) {
		List<RuleTrs> rules = new ArrayList<>();
		Map<String, List<RuleTrs>> rulesByLeft = new LinkedHashMap<>();
		int characterCount = 0;
		for (RuleTrs rule : trs) {
			if (rules.size() >= MAX_RULE_COUNT)
				return null;
			String key = canonical(rule.getLeft());
			if (MAX_INDEX_CHARACTER_COUNT - characterCount < key.length())
				return null;
			characterCount += key.length();
			rules.add(rule);
			rulesByLeft.computeIfAbsent(key, ignored -> new ArrayList<>()).add(rule);
		}
		return new RootVariantIndex(rules, rulesByLeft);
	}

	/** Returns whether the two rules form a root cycle modulo renaming. */
	private static boolean formsCycle(RuleTrs first, RuleTrs second) {
		return !first.isGeneralized() && !second.isGeneralized() &&
				first.getRight().isVariantOf(second.getLeft()) &&
				second.getRight().isVariantOf(first.getLeft());
	}

	/** Builds a compact key invariant under variable renaming. */
	private static String canonical(Term term) {
		Map<Variable, String> variables = new HashMap<>();
		return term.toString(variables, false);
	}

	/** The bounded index used during one search. */
	private record RootVariantIndex(
			List<RuleTrs> rules,
			Map<String, List<RuleTrs>> rulesByLeft) {}
}
