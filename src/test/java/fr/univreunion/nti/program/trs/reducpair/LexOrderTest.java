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

package fr.univreunion.nti.program.trs.reducpair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.UUID;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.FunctionSymbol;

class LexOrderTest {

	@Test
	void commitNestedSpeculativeViewsAndPreserveTransitiveClosure() {
		FunctionSymbol[] symbols = symbols(4);
		LexOrder order = new LexOrder();
		LexOrder outer = LexOrder.speculativeViewOf(order);

		assertTrue(outer.add(symbols[0], symbols[1]));
		LexOrder inner = LexOrder.speculativeViewOf(outer);
		assertTrue(inner.add(symbols[1], symbols[2]));
		inner.commitTo(outer);
		assertTrue(outer.add(symbols[2], symbols[3]));
		outer.commitTo(order);

		assertTrue(contains(order, symbols[0], symbols[1]));
		assertTrue(contains(order, symbols[0], symbols[2]));
		assertTrue(contains(order, symbols[0], symbols[3]));
		assertTrue(contains(order, symbols[1], symbols[3]));
		assertFalse(order.add(symbols[3], symbols[0]));
	}

	@Test
	void discardInnerViewAndKeepOuterChanges() {
		FunctionSymbol[] symbols = symbols(4);
		LexOrder order = new LexOrder();
		assertTrue(order.add(symbols[0], symbols[1]));

		LexOrder outer = LexOrder.speculativeViewOf(order);
		assertTrue(outer.add(symbols[1], symbols[2]));
		String outerState = outer.toString();
		LexOrder inner = LexOrder.speculativeViewOf(outer);
		assertTrue(inner.add(symbols[2], symbols[3]));

		assertEquals(outerState, outer.toString());
		assertTrue(contains(outer, symbols[0], symbols[2]));
		assertFalse(contains(outer, symbols[0], symbols[3]));
		outer.commitTo(order);
		assertEquals(outerState, order.toString());
	}

	@Test
	void discardOuterViewAfterNestedCommit() {
		FunctionSymbol[] symbols = symbols(4);
		LexOrder order = new LexOrder();
		assertTrue(order.add(symbols[0], symbols[1]));
		String initialState = order.toString();

		LexOrder outer = LexOrder.speculativeViewOf(order);
		assertTrue(outer.add(symbols[1], symbols[2]));
		LexOrder inner = LexOrder.speculativeViewOf(outer);
		assertTrue(inner.add(symbols[2], symbols[3]));
		inner.commitTo(outer);

		assertEquals(initialState, order.toString());
		assertTrue(contains(order, symbols[0], symbols[1]));
		assertFalse(contains(order, symbols[0], symbols[2]));
		assertFalse(contains(order, symbols[2], symbols[3]));
	}

	@Test
	void preserveSourceRenderingAfterSpeculativeTableGrowth() {
		FunctionSymbol[] symbols = symbols(96);
		LexOrder order = new LexOrder();
		for (int i = 1; i < 40; i += 2)
			assertTrue(order.add(symbols[i], symbols[0]));
		String initialState = order.toString();

		LexOrder speculative = LexOrder.speculativeViewOf(order);
		for (int i = 41; i < symbols.length; i += 2)
			assertTrue(speculative.add(symbols[i], symbols[i - 1]));

		assertEquals(initialState, order.toString());
	}

	@Test
	void keepCopyConstructorIndependentAndSkipUnmaterializedCommit() {
		FunctionSymbol[] symbols = symbols(3);
		LexOrder source = new LexOrder();
		assertTrue(source.add(symbols[0], symbols[1]));
		LexOrder copy = new LexOrder(source);

		assertTrue(copy.add(symbols[1], symbols[2]));
		assertFalse(contains(source, symbols[0], symbols[2]));
		assertTrue(contains(copy, symbols[0], symbols[2]));

		String sourceState = source.toString();
		LexOrder speculative = LexOrder.speculativeViewOf(source);
		speculative.commitTo(source);
		assertEquals(sourceState, source.toString());
	}

	@Test
	void preserveRenderingAcrossEagerCopyAndClearWithoutAffectingSource() {
		FunctionSymbol[] symbols = symbols(6);
		LexOrder source = new LexOrder();
		assertTrue(source.add(symbols[4], symbols[1]));
		assertTrue(source.add(symbols[2], symbols[0]));
		assertTrue(source.add(symbols[4], symbols[2]));
		String sourceState = source.toString();

		LexOrder copy = new LexOrder(source);
		assertEquals(sourceState, copy.toString());

		copy.clear();
		assertEquals("{}", copy.toString());
		assertEquals(sourceState, source.toString());

		LexOrder speculative = LexOrder.speculativeViewOf(source);
		assertTrue(speculative.add(symbols[1], symbols[0]));
		speculative.clear();
		speculative.commitTo(source);
		assertEquals(sourceState, source.toString());
	}

	@Test
	void closeOnePredecessorOverOneSuccessorInOneAddition() {
		FunctionSymbol[] symbols = symbols(4);
		LexOrder order = new LexOrder();
		assertTrue(order.add(symbols[1], symbols[0]));
		assertTrue(order.add(symbols[3], symbols[2]));

		assertTrue(order.add(symbols[2], symbols[1]));

		assertTrue(contains(order, symbols[2], symbols[1]));
		assertTrue(contains(order, symbols[2], symbols[0]));
		assertTrue(contains(order, symbols[3], symbols[1]));
		assertTrue(contains(order, symbols[3], symbols[0]));
	}

	@Test
	void letUnmaterializedNestedViewFollowLaterSourceMaterializations() {
		FunctionSymbol[] symbols = symbols(3);
		LexOrder root = new LexOrder();
		LexOrder outer = LexOrder.speculativeViewOf(root);
		LexOrder inner = LexOrder.speculativeViewOf(outer);

		assertTrue(root.add(symbols[0], symbols[1]));
		assertTrue(contains(inner, symbols[0], symbols[1]));

		assertTrue(outer.add(symbols[1], symbols[2]));
		assertTrue(contains(inner, symbols[1], symbols[2]));
		assertTrue(contains(inner, symbols[0], symbols[2]));
	}

	@Test
	void keepMaterializedNestedViewIndependentOfLaterSourceChanges() {
		FunctionSymbol[] symbols = symbols(5);
		LexOrder root = new LexOrder();
		assertTrue(root.add(symbols[0], symbols[1]));
		LexOrder outer = LexOrder.speculativeViewOf(root);
		LexOrder inner = LexOrder.speculativeViewOf(outer);

		assertTrue(inner.add(symbols[1], symbols[2]));
		assertTrue(outer.add(symbols[2], symbols[3]));
		assertTrue(root.add(symbols[3], symbols[4]));

		assertTrue(contains(inner, symbols[0], symbols[2]));
		assertFalse(contains(inner, symbols[2], symbols[3]));
		assertFalse(contains(inner, symbols[3], symbols[4]));
	}

	private static FunctionSymbol[] symbols(int count) {
		String prefix = "lex-order-test-" + UUID.randomUUID() + "-";
		FunctionSymbol[] symbols = new FunctionSymbol[count];
		for (int i = 0; i < count; i++)
			symbols[i] = FunctionSymbol.intern(prefix + i, 0);
		return symbols;
	}

	private static boolean contains(
			LexOrder order,
			FunctionSymbol source,
			FunctionSymbol target) {
		return !new LexOrder(order).add(target, source);
	}
}
