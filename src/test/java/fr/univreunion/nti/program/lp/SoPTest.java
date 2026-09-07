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

package fr.univreunion.nti.program.lp;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class SoPTest {

	@Test
	void incrementalConstructionMatchesCompleteConstruction() {
		Variable sharedHeadVariable = new Variable();
		BinaryRuleLp prependedRule = rule(
				function(
						"incremental-head",
						sharedHeadVariable,
						sharedHeadVariable),
				function("incremental-link", sharedHeadVariable));

		Variable tailVariable = new Variable();
		BinaryRuleLp previousRule = rule(
				function("incremental-link", tailVariable),
				function("incremental-tail", tailVariable));
		List<BinaryRuleLp> previousSequence = List.of(previousRule);

		SoP completeTau = new SoP(List.of(prependedRule, previousRule));
		SoP incrementalTau = new SoP(
				prependedRule,
				previousSequence,
				new SoP(previousSequence));

		assertEquivalentMappings(
				completeTau,
				incrementalTau,
				prependedRule.getHeadPredicateSymbol());
		assertEquivalentMappings(
				completeTau,
				incrementalTau,
				prependedRule.getBodyPredicateSymbol());
		assertEquivalentMappings(
				completeTau,
				incrementalTau,
				previousRule.getBodyPredicateSymbol());
	}

	@Test
	void returnsNoMappingForValidPositionsOfUnknownPredicates() {
		SoP tau = new SoP(List.of());
		FunctionSymbol predicateSymbol =
				FunctionSymbol.intern("unknown-predicate", 2);

		assertFalse(tau.isInDomain(predicateSymbol, 0));
		assertFalse(tau.isInDomain(predicateSymbol, 1));
		assertNull(tau.getMappedTerm(predicateSymbol, 0));
		assertNull(tau.getMappedTerm(predicateSymbol, 1));
	}

	@Test
	void rejectsInvalidPositionsEvenWhenPredicateIsUnknown() {
		SoP tau = new SoP(List.of());
		FunctionSymbol predicateSymbol =
				FunctionSymbol.intern("unknown-indexed-predicate", 2);

		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.isInDomain(predicateSymbol, -1));
		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.isInDomain(predicateSymbol, 2));
		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.getMappedTerm(predicateSymbol, -1));
		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.getMappedTerm(predicateSymbol, 2));
	}

	@Test
	void rejectsInvalidPositionsOfMappedPredicates() {
		Variable variable = new Variable();
		BinaryRuleLp mappedRule = rule(
				function("mapped-indexed-predicate", variable),
				function("mapped-indexed-body", variable));
		SoP tau = new SoP(List.of(mappedRule));
		FunctionSymbol predicateSymbol = mappedRule.getHeadPredicateSymbol();

		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.isInDomain(predicateSymbol, -1));
		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.isInDomain(predicateSymbol, 1));
		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.getMappedTerm(predicateSymbol, -1));
		assertThrows(
				IndexOutOfBoundsException.class,
				() -> tau.getMappedTerm(predicateSymbol, 1));
	}

	private static void assertEquivalentMappings(
			SoP expected,
			SoP actual,
			FunctionSymbol predicateSymbol) {
		for (int argumentIndex = 0;
				argumentIndex < predicateSymbol.getArity();
				argumentIndex++) {
			assertEquals(
					expected.isInDomain(predicateSymbol, argumentIndex),
					actual.isInDomain(predicateSymbol, argumentIndex));

			Term expectedTerm =
					expected.getMappedTerm(predicateSymbol, argumentIndex);
			Term actualTerm = actual.getMappedTerm(predicateSymbol, argumentIndex);
			if (expectedTerm == null)
				assertNull(actualTerm);
			else {
				assertNotNull(actualTerm);
				assertTrue(expectedTerm.isVariantOf(actualTerm));
			}
		}
	}

	private static BinaryRuleLp rule(Function head, Function body) {
		return new BinaryRuleLp(head, body, 0);
	}

	private static Function function(String name, Term... arguments) {
		return new Function(
				FunctionSymbol.intern(name, arguments.length),
				List.of(arguments));
	}
}
