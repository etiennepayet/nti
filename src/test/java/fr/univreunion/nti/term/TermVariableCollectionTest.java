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

package fr.univreunion.nti.term;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.pattern.HatFunctionSymbol;

class TermVariableCollectionTest {

	@Test
	@DisplayName("collect variables once through a shared composite subterm")
	void collectVariablesThroughSharedCompositeSubterm() {
		Variable variable = new Variable();
		Function shared = function("shared", variable);
		Function outer = function("outer", shared, shared);

		assertEquals(Set.of(variable), outer.getVariables());
		assertEquals(Set.of(variable), outer.getVariables());

		Variable existingVariable = new Variable();
		Set<Variable> accumulator = new HashSet<>(Set.of(existingVariable));
		outer.collectVariablesInto(accumulator);
		assertEquals(Set.of(existingVariable, variable), accumulator);
	}

	@Test
	@DisplayName("collect reachable variables through every cyclic term kind")
	void collectVariablesThroughCyclicTerms() {
		Variable functionCycle = new Variable();
		Variable functionVariable = new Variable();
		assertCollectsAcrossCycle(
				function("cycle-function", functionCycle, functionVariable),
				functionCycle,
				functionVariable);

		Variable listCycle = new Variable();
		Variable listVariable = new Variable();
		assertCollectsAcrossCycle(
				new PrologList(List.of(listCycle, listVariable)),
				listCycle,
				listVariable);

		Variable tupleCycle = new Variable();
		Variable tupleVariable = new Variable();
		assertCollectsAcrossCycle(
				new PrologTuple(List.of(tupleCycle, tupleVariable)),
				tupleCycle,
				tupleVariable);

		Variable hatCycle = new Variable();
		Variable hatVariable = new Variable();
		HatFunction hat = new HatFunction(
				hatSymbol("cycle-hat"),
				function("cycle-hat-argument", hatCycle, hatVariable),
				List.of(1, 0));
		assertCollectsAcrossCycle(hat, hatCycle, hatVariable);
	}

	private static void assertCollectsAcrossCycle(
			Term cyclicTerm,
			Variable cycleLink,
			Variable expectedVariable) {
		cycleLink.union(cyclicTerm);

		assertEquals(Set.of(expectedVariable), cyclicTerm.getVariables());
		assertEquals(Set.of(expectedVariable), cycleLink.getVariables());

		Set<Variable> accumulator = new HashSet<>();
		cyclicTerm.collectVariablesInto(accumulator);
		assertEquals(Set.of(expectedVariable), accumulator);
	}

	private static Function function(String prefix, Term... arguments) {
		return new Function(
				FunctionSymbol.intern(
						prefix + "-" + UUID.randomUUID(),
						arguments.length),
				List.of(arguments));
	}

	private static HatFunctionSymbol hatSymbol(String prefix) {
		Variable hole = new Variable();
		return HatFunctionSymbol.intern(
				function(prefix + "-context", hole),
				hole);
	}
}
