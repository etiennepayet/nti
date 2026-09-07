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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import java.util.Deque;

import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.Trs;

/**
 * Collects the initial dependency pair problems associated with a TRS.
 * <p>
 * Each problem pairs the TRS under analysis with one SCC of its
 * estimated dependency graph.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class InitialDependencyPairProblemCollector {

	/**
	 * Collects the initial dependency pair problems associated with
	 * the specified TRS.
	 *
	 * @param trs the TRS under analysis
	 * @return the collection of initial dependency pair problems
	 * associated with <code>trs</code>
	 */
	DependencyPairProblemCollection collectFrom(Trs trs) {
		// The collection to return at the end.
		DependencyPairProblemCollection problems = new DependencyPairProblemCollection();

		// We compute the SCCs of the estimated dependency graph of the TRS.
		Deque<DependencyPairs> sccs = trs.getDependencyGraph().getSCCs();

		// We build one initial problem for each SCC of the estimated
		// dependency graph.
		for (DependencyPairs scc : sccs)
			problems.add(new DependencyPairProblem(trs, scc));

		return problems;
	}
}
