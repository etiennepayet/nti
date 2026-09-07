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
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

class SubstitutionTest {

	@Test
	@DisplayName("build and clear an empty substitution")
	void buildAndClearAnEmptySubstitution() {
		Substitution substitution = new Substitution();
		Variable variable = new Variable();
		Function defaultTerm = constant("substitution-default");

		assertTrue(substitution.isEmpty());
		assertNull(substitution.get(variable));
		assertSame(defaultTerm,
				substitution.getOrDefault(variable, defaultTerm));
		assertTrue(substitution.getDomain().isEmpty());
		assertEquals("{}", substitution.toString());

		substitution.add(variable, defaultTerm);
		substitution.clear();
		assertTrue(substitution.isEmpty());
		assertNull(substitution.get(variable));
	}

	@Test
	@DisplayName("accept equivalent mappings and reject incompatible additions")
	void acceptEquivalentMappingsAndRejectIncompatibleAdditions() {
		Variable variable = new Variable();
		Variable argument = new Variable();
		FunctionSymbol symbol = FunctionSymbol.intern(
				"substitution-compatible-" + UUID.randomUUID(), 1);
		Function first = new Function(symbol, List.of(argument));
		Function equivalent = new Function(symbol, List.of(argument));
		Function incompatible = constant("substitution-incompatible");
		Substitution substitution = new Substitution();

		assertThrows(IllegalArgumentException.class,
				() -> substitution.add(null, first));
		assertThrows(IllegalArgumentException.class,
				() -> substitution.add(variable, null));
		assertTrue(substitution.add(variable, first));
		assertTrue(substitution.add(variable, equivalent));
		assertSame(first, substitution.get(variable));
		assertFalse(substitution.add(variable, incompatible));
		assertSame(first, substitution.get(variable));
		Variable selfMapped = new Variable();
		assertTrue(substitution.add(selfMapped, selfMapped));
		assertSame(selfMapped, substitution.get(selfMapped));
	}

	@Test
	@DisplayName("replace and remove mappings by deep equality")
	void replaceAndRemoveMappingsByDeepEquality() {
		Variable variable = new Variable();
		Function first = constant("substitution-replaced-first");
		Function replacement = constant("substitution-replaced-second");
		Substitution substitution = new Substitution();

		assertThrows(IllegalArgumentException.class,
				() -> substitution.addReplace(null, first));
		assertThrows(IllegalArgumentException.class,
				() -> substitution.addReplace(variable, null));
		substitution.addReplace(variable, first);
		substitution.addReplace(variable, replacement);
		assertSame(replacement, substitution.get(variable));
		assertFalse(substitution.remove(variable, first));
		assertTrue(substitution.remove(variable,
				new Function(replacement.getRootSymbol(), List.of())));
		assertTrue(substitution.isEmpty());
		assertFalse(substitution.remove(variable, replacement));
	}

	@Test
	@DisplayName("copy the mapping table while sharing variables and terms")
	void copyTheMappingTableWhileSharingVariablesAndTerms() {
		Variable variable = new Variable();
		Function term = constant("substitution-copy");
		Substitution original = new Substitution();
		original.add(variable, term);
		Substitution copy = new Substitution(original);

		assertSame(term, copy.get(variable));
		copy.clear();
		assertTrue(copy.isEmpty());
		assertSame(term, original.get(variable));

		Set<Variable> domain = original.getDomain();
		domain.clear();
		assertEquals(Set.of(variable), original.getDomain());
	}

	@Test
	@DisplayName("expose mutable mappings through substitution iteration")
	void exposeMutableMappingsThroughSubstitutionIteration() {
		Variable variable = new Variable();
		Function first = constant("substitution-iteration-first");
		Function replacement = constant("substitution-iteration-replacement");
		Substitution substitution = new Substitution();
		substitution.add(variable, first);
		Iterator<Map.Entry<Variable, Term>> iterator = substitution.iterator();

		Map.Entry<Variable, Term> mapping = iterator.next();
		assertSame(variable, mapping.getKey());
		assertSame(first, mapping.setValue(replacement));
		assertSame(replacement, substitution.get(variable));
		iterator.remove();
		assertTrue(substitution.isEmpty());
		assertThrows(IllegalStateException.class, iterator::remove);
	}

	@Test
	@DisplayName("retain mappings and mutable iteration after singleton promotion")
	void retainMappingsAndMutableIterationAfterSingletonPromotion() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		Function firstTerm = constant("substitution-promoted-first");
		Function secondTerm = constant("substitution-promoted-second");
		Function replacement = constant("substitution-promoted-replacement");
		Substitution substitution = new Substitution();
		substitution.add(firstVariable, firstTerm);
		substitution.add(secondVariable, secondTerm);

		Iterator<Map.Entry<Variable, Term>> iterator = substitution.iterator();
		while (iterator.hasNext()) {
			Map.Entry<Variable, Term> mapping = iterator.next();
			if (mapping.getKey() == firstVariable)
				assertSame(firstTerm, mapping.setValue(replacement));
			else
				iterator.remove();
		}

		assertSame(replacement, substitution.get(firstVariable));
		assertNull(substitution.get(secondVariable));
		assertEquals(Set.of(firstVariable), substitution.getDomain());

		substitution.clear();
		substitution.add(secondVariable, secondTerm);
		assertSame(secondTerm, substitution.iterator().next().getValue());
	}

	@Test
	@DisplayName("render named mappings without relying on hash iteration order")
	void renderNamedMappingsWithoutRelyingOnHashIterationOrder() {
		Variable variable = new Variable();
		Variable argument = new Variable();
		Function term = new Function(
				FunctionSymbol.intern(
						"substitution-rendering-" + UUID.randomUUID(), 1),
				List.of(argument));
		Substitution substitution = new Substitution();
		substitution.add(variable, term);
		Map<Variable, String> names = new HashMap<>();
		names.put(variable, "Domain");
		names.put(argument, "Argument");

		assertEquals("{Domain->" + term.getRootSymbol() + "(Argument)}",
				substitution.toString(names));
	}

	@Test
	@DisplayName("compose mappings while preserving first-domain priority")
	void composeMappingsWhilePreservingFirstDomainPriority() {
		Variable firstDomain = new Variable();
		Variable intermediate = new Variable();
		Variable identityDomain = new Variable();
		Variable secondOnlyDomain = new Variable();
		FunctionSymbol wrapperSymbol = FunctionSymbol.intern(
				"substitution-composition-wrapper-" + UUID.randomUUID(), 1);
		Function wrappedIntermediate = new Function(
				wrapperSymbol, List.of(intermediate));
		Function intermediateTarget = constant("substitution-composition-target");
		Function collidingTarget = constant("substitution-composition-collision");
		Function secondOnlyTarget = constant("substitution-composition-second-only");
		Substitution first = new Substitution();
		first.add(firstDomain, wrappedIntermediate);
		first.add(identityDomain, identityDomain);
		Substitution second = new Substitution();
		second.add(intermediate, intermediateTarget);
		second.add(firstDomain, collidingTarget);
		second.add(secondOnlyDomain, secondOnlyTarget);

		Substitution composition = first.composeWith(second);
		Function composedFirst = (Function) composition.get(firstDomain);

		assertSame(wrapperSymbol, composedFirst.getRootSymbol());
		assertNotSame(intermediateTarget, composedFirst.getChild(0));
		assertTrue(intermediateTarget.deepEquals(composedFirst.getChild(0)));
		assertNull(composition.get(identityDomain));
		assertSame(intermediateTarget, composition.get(intermediate));
		assertSame(secondOnlyTarget, composition.get(secondOnlyDomain));
		assertSame(wrappedIntermediate, first.get(firstDomain));
		assertSame(collidingTarget, second.get(firstDomain));
	}

	@Test
	@DisplayName("find variables in substitution domains and nested ranges")
	void findVariablesInSubstitutionDomainsAndNestedRanges() {
		Variable domainVariable = new Variable();
		Variable rangeVariable = new Variable();
		Variable nestedVariable = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern(
						"substitution-containment-" + UUID.randomUUID(), 1),
				List.of(nestedVariable));
		Function range = new Function(
				FunctionSymbol.intern(
						"substitution-range-" + UUID.randomUUID(), 2),
				List.of(rangeVariable, nested));
		Substitution substitution = new Substitution();
		substitution.add(domainVariable, range);

		assertTrue(substitution.contains(domainVariable));
		assertTrue(substitution.contains(rangeVariable));
		assertTrue(substitution.contains(nestedVariable));
		assertFalse(substitution.contains(new Variable()));
		assertFalse(new Substitution().contains(domainVariable));
	}

	@Test
	@DisplayName("deep copy domains and ranges with one canonical copy map")
	void deepCopyDomainsAndRangesWithOneCanonicalCopyMap() {
		Variable domainVariable = new Variable();
		Variable sharedRangeVariable = new Variable();
		FunctionSymbol rangeSymbol = FunctionSymbol.intern(
				"substitution-deep-copy-" + UUID.randomUUID(), 2);
		Function range = new Function(
				rangeSymbol, List.of(domainVariable, sharedRangeVariable));
		Substitution source = new Substitution();
		source.add(domainVariable, range);
		Variable prebuiltRangeCopy = new Variable();
		Map<Term, Term> copies = new HashMap<>();
		copies.put(sharedRangeVariable, prebuiltRangeCopy);

		Substitution copy = source.deepCopy(copies);
		Variable copiedDomain = copy.getDomain().iterator().next();
		Function copiedRange = (Function) copy.get(copiedDomain);

		assertNotSame(domainVariable, copiedDomain);
		assertNotSame(range, copiedRange);
		assertSame(rangeSymbol, copiedRange.getRootSymbol());
		assertSame(copiedDomain, copiedRange.getChild(0));
		assertSame(prebuiltRangeCopy, copiedRange.getChild(1));
		assertSame(copiedDomain, copies.get(domainVariable));
		assertNull(copies.get(range));
		assertSame(range, source.get(domainVariable));
	}

	@Test
	@DisplayName("rename domains and ranges while accepting compatible domain collisions")
	void renameDomainsAndRangesWhileAcceptingCompatibleDomainCollisions() {
		Variable renamedDomain = new Variable();
		Variable firstDomain = new Variable();
		Variable secondDomain = new Variable();
		Variable untouchedDomain = new Variable();
		Variable rangeVariable = new Variable();
		Variable renamedRangeVariable = new Variable();
		FunctionSymbol wrapperSymbol = FunctionSymbol.intern(
				"substitution-renaming-wrapper-" + UUID.randomUUID(), 1);
		Function firstRange = new Function(wrapperSymbol, List.of(rangeVariable));
		Function equivalentRange = new Function(wrapperSymbol, List.of(rangeVariable));
		Function untouchedRange = constant("substitution-renaming-untouched");
		Substitution source = new Substitution();
		source.add(firstDomain, firstRange);
		source.add(secondDomain, equivalentRange);
		source.add(untouchedDomain, untouchedRange);
		Substitution renaming = new Substitution();
		renaming.add(firstDomain, renamedDomain);
		renaming.add(secondDomain, renamedDomain);
		renaming.add(rangeVariable, renamedRangeVariable);

		Substitution renamed = source.renameWith(renaming);
		Function renamedRange = (Function) renamed.get(renamedDomain);

		assertEquals(Set.of(renamedDomain, untouchedDomain), renamed.getDomain());
		assertSame(wrapperSymbol, renamedRange.getRootSymbol());
		assertSame(renamedRangeVariable, renamedRange.getChild(0));
		assertNotSame(untouchedRange, renamed.get(untouchedDomain));
		assertTrue(untouchedRange.deepEquals(renamed.get(untouchedDomain)));
		assertSame(firstRange, source.get(firstDomain));
		assertSame(equivalentRange, source.get(secondDomain));

		Substitution invalidRenaming = new Substitution(renaming);
		invalidRenaming.addReplace(firstDomain,
				constant("substitution-renaming-non-variable"));
		assertNull(source.renameWith(invalidRenaming));
		assertSame(firstRange, source.get(firstDomain));
	}

	@Test
	@DisplayName("restrict mappings shallowly without changing the source")
	void restrictMappingsShallowlyWithoutChangingTheSource() {
		Variable retainedDomain = new Variable();
		Variable omittedDomain = new Variable();
		Variable absentDomain = new Variable();
		Function retainedRange = constant("substitution-restriction-retained");
		Function omittedRange = constant("substitution-restriction-omitted");
		Substitution source = new Substitution();
		source.add(retainedDomain, retainedRange);
		source.add(omittedDomain, omittedRange);

		Substitution restricted = source.restrictTo(
				List.of(retainedDomain, absentDomain));

		assertEquals(Set.of(retainedDomain), restricted.getDomain());
		assertSame(retainedRange, restricted.get(retainedDomain));
		assertNull(restricted.get(omittedDomain));
		restricted.clear();
		assertEquals(Set.of(retainedDomain, omittedDomain), source.getDomain());
		assertTrue(source.restrictTo(List.of()).isEmpty());
	}

	@Test
	@DisplayName("union compatible mappings and discard partial incompatible results")
	void unionCompatibleMappingsAndDiscardPartialIncompatibleResults() {
		Variable sharedDomain = new Variable();
		Variable firstOnlyDomain = new Variable();
		Variable secondOnlyDomain = new Variable();
		Function sharedRange = constant("substitution-union-shared");
		Function equivalentSharedRange = new Function(
				sharedRange.getRootSymbol(), List.of());
		Function firstOnlyRange = constant("substitution-union-first-only");
		Function secondOnlyRange = constant("substitution-union-second-only");
		Substitution first = new Substitution();
		first.add(sharedDomain, sharedRange);
		first.add(firstOnlyDomain, firstOnlyRange);
		Substitution compatible = new Substitution();
		compatible.add(sharedDomain, equivalentSharedRange);
		compatible.add(secondOnlyDomain, secondOnlyRange);

		Substitution union = first.unionWith(compatible);

		assertSame(sharedRange, union.get(sharedDomain));
		assertSame(firstOnlyRange, union.get(firstOnlyDomain));
		assertSame(secondOnlyRange, union.get(secondOnlyDomain));
		assertEquals(Set.of(sharedDomain, firstOnlyDomain), first.getDomain());
		assertEquals(Set.of(sharedDomain, secondOnlyDomain), compatible.getDomain());

		Substitution incompatible = new Substitution();
		incompatible.add(secondOnlyDomain, secondOnlyRange);
		incompatible.add(sharedDomain,
				constant("substitution-union-incompatible"));
		assertNull(first.unionWith(incompatible));
		assertEquals(Set.of(sharedDomain, firstOnlyDomain), first.getDomain());
		assertEquals(Set.of(sharedDomain, secondOnlyDomain), incompatible.getDomain());
		assertSame(sharedRange, first.get(sharedDomain));
	}

	private static Function constant(String prefix) {
		return new Function(
				FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), 0),
				List.of());
	}
}
