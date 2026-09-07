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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.term;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

class PositionTest {

	@Test
	@DisplayName("represent the root and singleton positions")
	void representRootAndSingletonPositions() {
		Position root = new Position();
		Position singleton = new Position(-1);

		assertTrue(root.isEmpty());
		assertEquals("𝜀", root.toString());
		assertThrows(NoSuchElementException.class, root::getFirst);
		assertFalse(singleton.isEmpty());
		assertEquals(-1, singleton.getFirst());
		assertEquals("[-1]", singleton.toString());
	}

	@Test
	@DisplayName("derive independent positions by adding at either end")
	void deriveIndependentPositionsByAddingAtEitherEnd() {
		Position original = new Position(1);
		Position prefixed = original.addFirst(0);
		Position suffixed = original.addLast(2);

		assertEquals(List.of(1), elementsOf(original));
		assertEquals(List.of(0, 1), elementsOf(prefixed));
		assertEquals(List.of(1, 2), elementsOf(suffixed));

		Position extendedPrefix = prefixed.addLast(3);
		assertEquals(List.of(0, 1), elementsOf(prefixed));
		assertEquals(List.of(0, 1, 3), elementsOf(extendedPrefix));
	}

	@Test
	@DisplayName("append positions without modifying either operand")
	void appendPositionsWithoutModifyingEitherOperand() {
		Position left = new Position(0).addLast(1);
		Position right = new Position(2).addLast(3);
		Position appended = left.append(right);

		assertEquals(List.of(0, 1, 2, 3), elementsOf(appended));
		assertEquals(List.of(0, 1), elementsOf(left));
		assertEquals(List.of(2, 3), elementsOf(right));
		assertEquals(List.of(0, 1), elementsOf(left.append(new Position())));
		assertEquals(List.of(2, 3), elementsOf(new Position().append(right)));
		assertThrows(NullPointerException.class, () -> left.append(null));
	}

	@Test
	@DisplayName("remove successive final elements into proper prefixes")
	void removeSuccessiveFinalElementsIntoProperPrefixes() {
		Position position = new Position(0).addLast(1).addLast(2);
		Position firstPrefix = position.properPrefix();
		Position secondPrefix = firstPrefix.properPrefix();
		Position root = secondPrefix.properPrefix();

		assertEquals(List.of(0, 1, 2), elementsOf(position));
		assertEquals(List.of(0, 1), elementsOf(firstPrefix));
		assertEquals(List.of(0), elementsOf(secondPrefix));
		assertTrue(root.isEmpty());
		assertNull(root.properPrefix());
	}

	@Test
	@DisplayName("iterate in order and expose iterator removal on the position")
	void iterateInOrderAndExposeIteratorRemovalOnThePosition() {
		Position position = new Position(4).addLast(5);
		Iterator<Integer> iterator = position.iterator();

		assertTrue(iterator.hasNext());
		assertEquals(4, iterator.next());
		assertTrue(iterator.hasNext());
		assertEquals(5, iterator.next());
		assertFalse(iterator.hasNext());
		assertThrows(NoSuchElementException.class, iterator::next);
		assertThrows(NoSuchElementException.class, iterator::next);
		iterator.remove();
		assertEquals(List.of(4), elementsOf(position));
		assertThrows(IllegalStateException.class, iterator::remove);
	}

	private static List<Integer> elementsOf(Position position) {
		List<Integer> elements = new ArrayList<>();
		position.forEach(elements::add);
		return elements;
	}
}
