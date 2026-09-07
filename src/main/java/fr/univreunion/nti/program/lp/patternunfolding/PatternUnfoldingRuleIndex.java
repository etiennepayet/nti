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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * Indexes pattern-unfolding candidates by their left-hand predicate.
 * Candidate lists preserve the insertion order of the pattern rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternUnfoldingRuleIndex
		implements RuleLpPatternUnfolder.CandidateSelector {

	/** The pattern rules grouped by left-hand predicate. */
	private final Map<FunctionSymbol, List<PatternRuleLp>> rulesByLeft =
			new HashMap<>();

	/**
	 * Adds the provided rules to this index in iteration order.
	 *
	 * @param rules the newly generated pattern rules
	 */
	void addAll(Iterable<PatternRuleLp> rules) {
		for (PatternRuleLp rule : rules)
			this.rulesByLeft.computeIfAbsent(
					rule.getLeft().getRootSymbol(),
					ignored -> new ArrayList<>()).add(rule);
	}

	/**
	 * Returns the candidates whose left-hand predicate is that of the atom.
	 *
	 * @param bodyAtom the body atom to unfold
	 * @return its unfolding candidates, in their original insertion order
	 */
	@Override
	public List<PatternRuleLp> candidatesFor(Function bodyAtom) {
		List<PatternRuleLp> candidates =
				this.rulesByLeft.get(bodyAtom.getRootSymbol());

		return candidates == null ? List.of() : candidates;
	}
}
