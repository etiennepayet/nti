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

package fr.univreunion.nti.term.pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Hole;
import fr.univreunion.nti.term.Variable;

class HatFunctionSymbolTest {

	@Test
	@DisplayName("intern variant contexts as one canonical hat symbol")
	void internVariantContextsAsOneCanonicalHatSymbol() {
		FunctionSymbol contextRoot = uniqueUnarySymbol("hat-symbol-variant");
		Variable firstHole = new Variable();
		Variable secondHole = new Variable();
		Function firstContext = new Function(contextRoot, List.of(firstHole));
		Function variantContext = new Function(contextRoot, List.of(secondHole));

		HatFunctionSymbol first =
				HatFunctionSymbol.intern(firstContext, firstHole);
		HatFunctionSymbol variant =
				HatFunctionSymbol.intern(variantContext, secondHole);

		assertSame(first, variant);
		assertEquals("hat", first.getName());
		assertEquals(1, first.getArity());
		assertTrue(first.isHatSymbol());
		assertFalse(first.isTupleSymbol());
	}

	@Test
	@DisplayName("keep non-variant contexts as distinct hat symbols")
	void keepNonVariantContextsAsDistinctHatSymbols() {
		Variable firstHole = new Variable();
		Variable secondHole = new Variable();
		Function firstContext = new Function(
				uniqueUnarySymbol("hat-symbol-first-context"),
				List.of(firstHole));
		Function secondContext = new Function(
				uniqueUnarySymbol("hat-symbol-second-context"),
				List.of(secondHole));

		HatFunctionSymbol first =
				HatFunctionSymbol.intern(firstContext, firstHole);
		HatFunctionSymbol second =
				HatFunctionSymbol.intern(secondContext, secondHole);

		assertNotSame(first, second);
	}

	@Test
	@DisplayName("copy context metadata and render the canonical hole")
	void copyContextMetadataAndRenderTheCanonicalHole() {
		Variable contextHole = new Variable();
		Function context = new Function(
				uniqueUnarySymbol("hat-symbol-metadata"),
				List.of(contextHole));

		HatFunctionSymbol symbol =
				HatFunctionSymbol.intern(context, contextHole);
		Function storedContext =
				assertInstanceOf(Function.class, symbol.getSimpleContext());
		Hole storedHole = assertInstanceOf(Hole.class, symbol.getVariable());

		assertNotSame(context, storedContext);
		assertSame(context.getRootSymbol(), storedContext.getRootSymbol());
		assertSame(storedHole, storedContext.getChild(0));
		assertNotSame(contextHole, storedHole);
		assertSame(contextHole, context.getChild(0));
		assertEquals("hat[" + storedContext + "]", symbol.toString());
		assertTrue(HatFunctionSymbol.toStringSymbolTable().contains(
				": " + storedContext + "\n"));
	}

	@Test
	@DisplayName("reject an empty simple context")
	void rejectAnEmptySimpleContext() {
		Variable hole = new Variable();

		assertThrows(IllegalArgumentException.class,
				() -> HatFunctionSymbol.intern(hole, hole));
	}

	private static FunctionSymbol uniqueUnarySymbol(String prefix) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), 1);
	}
}
