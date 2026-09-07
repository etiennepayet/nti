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

package fr.univreunion.nti.program.trs.dependencypair;

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;

/**
 * Collects the dependency pairs associated with a TRS.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DependencyPairCollector {

	/**
	 * Collects the dependency pairs associated with the specified TRS.
	 *
	 * @param trs the TRS whose dependency pairs have to be collected
	 * @return the dependency pairs associated with <code>trs</code>
	 */
	public DependencyPairs collectFrom(Trs trs) {
		List<RuleTrs> dependencyPairs = new ArrayList<>();

		for (RuleTrs rule : trs) {
			Term right = rule.getRight();
			right.forEachSubterm(subterm -> {
				if (trs.isRootDefined(subterm))
					dependencyPairs.add(new RuleTrs(
							(Function) rule.getLeft().toTuple(),
							subterm.toTuple()));
			});
		}

		return new DependencyPairs(dependencyPairs);
	}
}
