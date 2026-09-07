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

import java.util.Deque;
import java.util.LinkedList;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;

/**
 * Stores the simple cycles discovered during a TRS rule-unfolding proof.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class SimpleCycleRegistry {

	/**
	 * The simple cycles discovered so far.
	 */
	private final Deque<Set<RuleTrs>> simpleCycles = new LinkedList<>();

	/**
	 * Adds the specified simple cycle to this registry.
	 *
	 * @param simpleCycle a simple cycle to add
	 * @return <code>true</code> iff this registry changed as a result
	 * of the call
	 */
	public boolean add(Set<RuleTrs> simpleCycle) {
		return this.simpleCycles.add(simpleCycle);
	}

	/**
	 * Returns <code>true</code> iff this registry contains the specified
	 * simple cycle.
	 *
	 * @param simpleCycle a simple cycle whose presence has to be tested
	 * @return <code>true</code> iff this registry contains the specified
	 * simple cycle
	 */
	public boolean contains(Set<RuleTrs> simpleCycle) {
		return this.simpleCycles.contains(simpleCycle);
	}

	/**
	 * Removes all simple cycles from this registry.
	 */
	public void clear() {
		this.simpleCycles.clear();
	}
}
