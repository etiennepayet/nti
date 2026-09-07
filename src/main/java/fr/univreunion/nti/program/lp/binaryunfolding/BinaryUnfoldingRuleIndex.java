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

package fr.univreunion.nti.program.lp.binaryunfolding;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.lp.UnfoldedRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * Indexes binary-unfolding candidates by their head predicate.
 * Candidate lists preserve the insertion order of the unfolded rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class BinaryUnfoldingRuleIndex
		implements RuleLpBinaryUnfolder.CandidateSelector {

	/** The unfolded rules grouped by head predicate. */
	private final Map<FunctionSymbol, List<UnfoldedRuleLp>> rulesByHead =
			new HashMap<>();

	/**
	 * Adds the provided rules to this index in iteration order.
	 *
	 * @param rules the newly generated unfolded rules
	 */
	void addAll(Iterable<? extends UnfoldedRuleLp> rules) {
		for (UnfoldedRuleLp rule : rules)
			this.rulesByHead.computeIfAbsent(
					rule.getHead().getRootSymbol(),
					ignored -> new ArrayList<>()).add(rule);
	}

	/**
	 * Returns the candidates whose head predicate is that of the given atom.
	 *
	 * @param bodyAtom the body atom to unfold
	 * @return its unfolding candidates, in their original insertion order
	 */
	@Override
	public List<UnfoldedRuleLp> candidatesFor(Function bodyAtom) {
		List<UnfoldedRuleLp> candidates =
				this.rulesByHead.get(bodyAtom.getRootSymbol());

		return candidates == null ? List.of() : candidates;
	}
}
