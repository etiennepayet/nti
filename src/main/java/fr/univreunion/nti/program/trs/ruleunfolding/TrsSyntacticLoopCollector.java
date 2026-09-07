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

package fr.univreunion.nti.program.trs.ruleunfolding;

import java.util.Collection;
import java.util.Deque;
import java.util.LinkedList;

import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.trans.UnfoldedRuleTrsTrans;

/**
 * Collects the initial unfolded rules used by the TRS rule-unfolding
 * nontermination technique.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class TrsSyntacticLoopCollector {

	/**
	 * Returns the syntactic loops that occur in the specified set of
	 * dependency pairs.
	 *
	 * @param dependencyPairs the dependency pairs where syntactic loops have to
	 * be searched for
	 * @return a collection of syntactic loops
	 */
	public Collection<UnfoldedRuleTrs> collectFrom(DependencyPairs dependencyPairs) {
		// The collection that will be returned.
		Collection<UnfoldedRuleTrs> loops = new LinkedList<>();

		Deque<RuleTrs> sCopy = dependencyPairs.toDeque();
		int n = sCopy.size();
		for (int i = 0; i < n; i++) {
			RuleTrs rule = sCopy.removeFirst();
			Collection<RuleTrs> simpleCycle = new LinkedList<>();
			simpleCycle.add(rule);
			loops.addAll(UnfoldedRuleTrsTrans.getUnfoldedInstances(
					rule.getLeft(), rule.getRight(), 0, null, sCopy, simpleCycle));
			sCopy.addLast(rule);
		}

		return loops;
	}

	/**
	 * Returns the syntactic loops that occur in the specified sets of
	 * dependency pairs.
	 *
	 * @param sccs the sets of dependency pair where syntactic loops
	 * have to be searched for
	 * @return a collection of syntactic loops
	 */
	public Collection<UnfoldedRuleTrs> collectFrom(Collection<DependencyPairs> sccs) {
		// The collection that will be returned.
		Collection<UnfoldedRuleTrs> loops = new LinkedList<>();

		for (DependencyPairs dependencyPairs : sccs)
			loops.addAll(this.collectFrom(dependencyPairs));

		return loops;
	}

	/**
	 * Returns the syntactic loops that occur in the SCCs of the estimated
	 * dependency graph of the specified TRS.
	 *
	 * @param trs the TRS whose SCCs have to be inspected
	 * @return a collection of syntactic loops
	 */
	public Collection<UnfoldedRuleTrs> collectFrom(Trs trs) {
		return this.collectFrom(trs.getDependencyGraph().getSCCs());
	}
}
