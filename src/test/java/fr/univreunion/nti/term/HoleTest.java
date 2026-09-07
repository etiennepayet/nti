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

package fr.univreunion.nti.term;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.trs.Trs;

class HoleTest {

	@Test
	@DisplayName("render a hole independently of variable names")
	void renderHoleIndependentlyOfVariableNames() {
		Hole hole = new Hole("□'");
		Map<Variable, String> names = new HashMap<>();
		names.put(hole, "ignored");

		assertEquals("□'", hole.toString());
		assertEquals("□'", hole.toString(names, false));
		assertEquals("□'", hole.toString(names, true));
		assertSame(Variable.VARIABLE_ROOT_SYMBOL, hole.getRootSymbol());
		assertTrue(hole.isVariable());
		assertTrue(hole.sameAs(hole));
		assertFalse(hole.sameAs(new Hole("□'")));
	}

	@Test
	@DisplayName("preserve hole type representation and copy-map reuse")
	void preserveHoleTypeRepresentationAndCopyMapReuse() {
		Hole hole = new Hole("□");
		Map<Term, Term> copies = new HashMap<>();

		assertSame(hole, hole.shallowCopy());

		Term firstCopy = hole.deepCopy(copies);
		Term repeatedCopy = hole.deepCopy(copies);

		assertTrue(firstCopy instanceof Hole);
		assertNotSame(hole, firstCopy);
		assertSame(firstCopy, repeatedCopy);
		assertSame(firstCopy, copies.get(hole));
		assertEquals("□", firstCopy.toString());
		assertSame(hole, hole.deepCopy(List.of()));
		assertTrue(hole.deepCopy(List.of(hole)) instanceof Hole);
	}

	@Test
	@DisplayName("resolve hole schemas deeply but retain shallow rendering")
	void resolveHoleSchemasDeeplyButRetainShallowRendering() {
		Hole hole = new Hole("□");
		Variable nestedVariable = new Variable();
		Function schema = new Function(
				symbol("hole-schema", 1), List.of(nestedVariable));
		Map<Variable, String> names = new HashMap<>();
		names.put(nestedVariable, "X");

		hole.union(schema);

		assertSame(schema, hole.findSchema());
		assertEquals(schema.toString(names, false),
				hole.toString(names, false));
		assertEquals("□", hole.toString(names, true));
		assertTrue(hole.deepCopy() instanceof Function);
		assertTrue(hole.shallowCopy() instanceof Function);

		Hole freshHole = new Hole("□");
		Term renamedCap = freshHole.rencap(
				new Trs("hole-rencap", List.of(), "FULL"), false);
		assertTrue(renamedCap instanceof Hole);
		assertNotSame(freshHole, renamedCap);
		assertEquals("□", renamedCap.toString());
	}

	private static FunctionSymbol symbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}
}
