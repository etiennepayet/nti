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
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class PatternSubstitutionTest {

	@Test
	@DisplayName("build the default pumping and closing identities")
	void buildTheDefaultPumpingAndClosingIdentities() {
		TestPatternSubstitution patternSubstitution =
				new TestPatternSubstitution();

		assertEquals(1, patternSubstitution.getArity());
		assertTrue(patternSubstitution.getPumping().isEmpty());
		assertTrue(patternSubstitution.getClosing().isEmpty());
		assertNotSame(patternSubstitution.getPumping(),
				patternSubstitution.getClosing());
		assertEquals("{}^n1{}", patternSubstitution.toString());
	}

	@Test
	@DisplayName("validate list construction and share its substitutions shallowly")
	void validateListConstructionAndShareItsSubstitutionsShallowly() {
		assertThrows(IllegalArgumentException.class,
				() -> new TestPatternSubstitution(null));
		assertThrows(IllegalArgumentException.class,
				() -> new TestPatternSubstitution(List.of()));
		assertThrows(IllegalArgumentException.class,
				() -> new TestPatternSubstitution(List.of(new Substitution())));

		Substitution pumping = new Substitution();
		Substitution closing = new Substitution();
		List<Substitution> source = new ArrayList<>(List.of(pumping, closing));
		TestPatternSubstitution patternSubstitution =
				new TestPatternSubstitution(source);
		source.clear();

		assertEquals(1, patternSubstitution.getArity());
		assertSame(pumping, patternSubstitution.getPumping());
		assertSame(closing, patternSubstitution.getClosing());
	}

	@Test
	@DisplayName("preserve a long provided tuple independently and in order")
	void preserveALongProvidedTupleIndependentlyAndInOrder() {
		List<Substitution> source = new ArrayList<>();
		for (int index = 0; index < 12; index++)
			source.add(new Substitution());
		List<Substitution> expected = List.copyOf(source);

		TestPatternSubstitution patternSubstitution =
				new TestPatternSubstitution(source);
		source.clear();

		assertEquals(11, patternSubstitution.getArity());
		assertEquals(expected, collect(patternSubstitution.iterator()));
		assertSame(expected.get(0), patternSubstitution.getPumping());
		assertSame(expected.get(11), patternSubstitution.getClosing());
	}

	@Test
	@DisplayName("find variables only in pumping domains")
	void findVariablesOnlyInPumpingDomains() {
		Variable pumpedVariable = new Variable();
		Variable selfMappedVariable = new Variable();
		Variable closingVariable = new Variable();
		Substitution firstPumping = new Substitution();
		firstPumping.add(selfMappedVariable, selfMappedVariable);
		Substitution secondPumping = new Substitution();
		secondPumping.add(pumpedVariable, constant("pattern-pumped"));
		Substitution closing = new Substitution();
		closing.add(closingVariable, constant("pattern-closing"));
		TestPatternSubstitution patternSubstitution =
				new TestPatternSubstitution(
						List.of(firstPumping, secondPumping, closing));

		assertTrue(patternSubstitution.inPumpingDomain(pumpedVariable));
		assertFalse(patternSubstitution.inPumpingDomain(selfMappedVariable));
		assertFalse(patternSubstitution.inPumpingDomain(closingVariable));
		assertFalse(patternSubstitution.inPumpingDomain(new Variable()));
		Map<Variable, String> names = new HashMap<>();
		names.put(pumpedVariable, "Pumped");
		names.put(selfMappedVariable, "SelfMapped");
		names.put(closingVariable, "Closing");
		assertEquals(firstPumping.toString(names) + "^n1"
				+ secondPumping.toString(names) + "^n2"
				+ closing.toString(names),
				patternSubstitution.toString(names));
	}

	@Test
	@DisplayName("iterate and mutate substitutions in tuple order")
	void iterateAndMutateSubstitutionsInTupleOrder() {
		Substitution firstPumping = new Substitution();
		Substitution secondPumping = new Substitution();
		Substitution closing = new Substitution();
		TestPatternSubstitution patternSubstitution =
				new TestPatternSubstitution(
						List.of(firstPumping, secondPumping, closing));
		ListIterator<Substitution> iterator = patternSubstitution.iterator();

		assertSame(firstPumping, iterator.next());
		Substitution replacement = new Substitution();
		iterator.set(replacement);
		assertSame(secondPumping, iterator.next());
		iterator.remove();

		assertEquals(1, patternSubstitution.getArity());
		assertSame(replacement, patternSubstitution.getPumping());
		assertSame(closing, patternSubstitution.getClosing());
		assertEquals(List.of(replacement, closing),
				collect(patternSubstitution.iterator()));
	}

	private static List<Substitution> collect(
			ListIterator<Substitution> iterator) {
		List<Substitution> substitutions = new ArrayList<>();
		iterator.forEachRemaining(substitutions::add);
		return substitutions;
	}

	private static Function constant(String prefix) {
		return new Function(FunctionSymbol.intern(
				prefix + "-" + UUID.randomUUID(), 0), List.of());
	}

	private static final class TestPatternSubstitution
			extends PatternSubstitution {

		private TestPatternSubstitution() {}

		private TestPatternSubstitution(List<Substitution> substitutions) {
			super(substitutions);
		}

		@Override
		public PatternSubstitution composeWith(
				PatternSubstitution otherPatternSubstitution) {
			return null;
		}

		@Override
		public PatternSubstitution deepCopy() {
			return null;
		}

		@Override
		public PatternSubstitution deepCopy(Map<Term, Term> copies) {
			return null;
		}
	}
}
