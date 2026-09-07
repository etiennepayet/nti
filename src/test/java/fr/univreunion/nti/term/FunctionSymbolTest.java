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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

class FunctionSymbolTest {

	@Test
	@DisplayName("intern canonical symbols and look them up without creation")
	void internAndLookUpCanonicalSymbols() {
		String name = "canonical-" + UUID.randomUUID();

		assertNull(FunctionSymbol.get(name, 2));
		assertNull(FunctionSymbol.get(name, 2));

		FunctionSymbol symbol = FunctionSymbol.intern(name, 2);

		assertSame(symbol, FunctionSymbol.intern(name, 2));
		assertSame(symbol, FunctionSymbol.get(name, 2));
		assertNotSame(symbol, FunctionSymbol.intern(name, 3));
		assertNotSame(symbol, FunctionSymbol.intern(name + "-other", 2));
		assertNull(FunctionSymbol.get(name, 1));
	}

	@Test
	@DisplayName("convert canonically between function and tuple symbols")
	void convertCanonicallyBetweenFunctionAndTupleSymbols() {
		String name = "conversion-" + UUID.randomUUID();
		FunctionSymbol functionSymbol = FunctionSymbol.intern(name, 3);

		FunctionSymbol tupleSymbol = functionSymbol.toTupleSymbol();

		assertNotSame(functionSymbol, tupleSymbol);
		assertSame(tupleSymbol, functionSymbol.toTupleSymbol());
		assertSame(tupleSymbol, tupleSymbol.toTupleSymbol());
		assertSame(functionSymbol, tupleSymbol.toFunctionSymbol());
		assertSame(functionSymbol, functionSymbol.toFunctionSymbol());
		assertEquals(name, tupleSymbol.getName());
		assertEquals(3, tupleSymbol.getArity());
		assertFalse(functionSymbol.isTupleSymbol());
		assertTrue(tupleSymbol.isTupleSymbol());
	}

	@Test
	@DisplayName("order function and tuple symbols by global insertion order")
	void orderSymbolsByGlobalInsertionOrder() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol first = FunctionSymbol.intern("first-" + suffix, 1);
		FunctionSymbol tuple = first.toTupleSymbol();
		FunctionSymbol last = FunctionSymbol.intern("last-" + suffix, 1);

		assertTrue(first.lt(tuple));
		assertTrue(tuple.lt(last));
		assertTrue(first.lt(last));
		assertFalse(tuple.lt(first));
		assertFalse(first.lt(first));
	}

	@Test
	@DisplayName("validate construction and render function and tuple symbols")
	void validateConstructionAndRenderSymbols() {
		FunctionSymbol functionSymbol =
				new FunctionSymbol("zero", 0, false, 0);
		FunctionSymbol tupleSymbol =
				new FunctionSymbol("zero", 0, true, 1);

		assertEquals("zero", functionSymbol.toString());
		assertEquals("zero^#", tupleSymbol.toString());
		assertFalse(functionSymbol.isHatSymbol());
		assertThrows(IllegalArgumentException.class,
				() -> new FunctionSymbol(null, 0, false, 0));
		assertThrows(IllegalArgumentException.class,
				() -> new FunctionSymbol("negative", -1, false, 0));
	}

	@Test
	@DisplayName("format ordinary symbol arities and exclude internal and tuple symbols")
	void formatOrdinarySymbolStatistics() {
		SymbolStatistics before = parse(FunctionSymbol.toStringStat());
		int aritySumBefore = Math.round(before.averageArity() * before.count());
		String suffix = UUID.randomUUID().toString();

		FunctionSymbol.intern("ordinary-zero-" + suffix, 0);
		FunctionSymbol tupleSource =
				FunctionSymbol.intern("ordinary-four-" + suffix, 4);
		FunctionSymbol.intern(" internal-" + suffix, 100);
		tupleSource.toTupleSymbol();

		String result = FunctionSymbol.toStringStat();

		int expectedCount = before.count() + 2;
		int expectedMinimumArity = 0;
		int expectedMaximumArity = Math.max(before.maximumArity(), 4);
		float expectedAverageArity =
				((float) (aritySumBefore + 4)) / expectedCount;
		assertEquals(
				expectedCount + " function symbol(s) -- arity: min=" +
				expectedMinimumArity + " max=" + expectedMaximumArity +
				" avg=" + expectedAverageArity,
				result);
	}

	private static SymbolStatistics parse(String statistics) {
		String[] parts = statistics.split(" ");
		int count = Integer.parseInt(parts[0]);
		if (count == 0)
			return new SymbolStatistics(0, -1, -1, 0.0f);
		return new SymbolStatistics(
				count,
				Integer.parseInt(parts[5].substring("min=".length())),
				Integer.parseInt(parts[6].substring("max=".length())),
				Float.parseFloat(parts[7].substring("avg=".length())));
	}

	private record SymbolStatistics(
			int count,
			int minimumArity,
			int maximumArity,
			float averageArity) {}
}
