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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.pattern.HatFunctionSymbol;

class TermRobinsonUnificationTest {

	@Test
	@DisplayName("complete an initial substitution without modifying terms")
	void completeInitialSubstitutionWithoutModifyingTerms() {
		FunctionSymbol pair = symbol("robinson-initial", 2);
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		Variable preservedVariable = new Variable();
		Function firstConstant = constant("robinson-initial-first");
		Function secondConstant = constant("robinson-initial-second");
		Function preservedConstant = constant("robinson-initial-preserved");
		Function source = new Function(
				pair, List.of(firstVariable, secondVariable));
		Function target = new Function(
				pair, List.of(firstConstant, secondConstant));
		Substitution unifier = new Substitution();
		unifier.addReplace(firstVariable, firstConstant);
		unifier.addReplace(preservedVariable, preservedConstant);

		assertTrue(source.isUnifiableWith(target, unifier));
		assertTrue(unifier.get(firstVariable).deepEquals(firstConstant));
		assertTrue(unifier.get(secondVariable).deepEquals(secondConstant));
		assertTrue(unifier.get(preservedVariable).deepEquals(preservedConstant));
		assertSame(firstVariable, source.getChild(0));
		assertSame(secondVariable, source.getChild(1));
		assertSame(firstConstant, target.getChild(0));
		assertSame(secondConstant, target.getChild(1));
	}

	@Test
	@DisplayName("compose leftmost disagreement bindings in order")
	void composeLeftmostDisagreementBindingsInOrder() {
		FunctionSymbol pair = symbol("robinson-order", 2);
		Variable repeatedSource = new Variable();
		Variable targetVariable = new Variable();
		Function constant = constant("robinson-order-constant");
		Function source = new Function(
				pair, List.of(repeatedSource, repeatedSource));
		Function target = new Function(
				pair, List.of(targetVariable, constant));
		Substitution unifier = new Substitution();

		assertTrue(source.isUnifiableWith(target, unifier));
		assertTrue(unifier.get(repeatedSource).deepEquals(constant));
		assertTrue(unifier.get(targetVariable).deepEquals(constant));
	}

	@Test
	@DisplayName("preserve shared input terms with an empty substitution")
	void preserveSharedInputTermsWithEmptySubstitution() {
		FunctionSymbol pair = symbol("robinson-shared-pair", 2);
		FunctionSymbol wrapper = symbol("robinson-shared-wrapper", 1);
		Variable sharedVariable = new Variable();
		Function sharedTerm = new Function(
				wrapper, List.of(sharedVariable));
		Function constant = constant("robinson-shared-constant");
		Function source = new Function(
				pair, List.of(sharedTerm, sharedVariable));
		Function target = new Function(
				pair, List.of(sharedTerm, constant));
		Substitution unifier = new Substitution();

		assertTrue(source.isUnifiableWith(target, unifier));
		assertNotSame(constant, unifier.get(sharedVariable));
		assertTrue(constant.deepEquals(unifier.get(sharedVariable)));
		assertSame(sharedTerm, source.getChild(0));
		assertSame(sharedTerm, target.getChild(0));
		assertSame(sharedVariable, sharedTerm.getChild(0));
	}

	@Test
	@DisplayName("keep Robinson unification unsupported for a shared tuple")
	void keepRobinsonUnificationUnsupportedForSharedTuple() {
		PrologTuple tuple = new PrologTuple(List.of(new Variable()));

		assertThrows(
				UnsupportedOperationException.class,
				() -> tuple.isUnifiableWith(tuple, new Substitution()));
	}

	@Test
	@DisplayName("roll back the substitution after a later root conflict")
	void rollBackSubstitutionAfterLaterRootConflict() {
		FunctionSymbol pair = symbol("robinson-conflict", 2);
		Variable sourceVariable = new Variable();
		Variable preservedVariable = new Variable();
		Function firstTarget = constant("robinson-conflict-binding");
		Function sourceConflict = constant("robinson-conflict-source");
		Function targetConflict = constant("robinson-conflict-target");
		Function preservedTerm = constant("robinson-conflict-preserved");
		Function source = new Function(
				pair, List.of(sourceVariable, sourceConflict));
		Function target = new Function(
				pair, List.of(firstTarget, targetConflict));
		Substitution unifier = new Substitution();
		unifier.addReplace(preservedVariable, preservedTerm);

		assertFalse(source.isUnifiableWith(target, unifier));
		assertNull(unifier.get(sourceVariable));
		assertSame(preservedTerm, unifier.get(preservedVariable));
		assertSame(sourceVariable, source.getChild(0));
		assertSame(firstTarget, target.getChild(0));
	}

	@Test
	@DisplayName("reject an occurs-check without changing the substitution")
	void rejectOccursCheckWithoutChangingSubstitution() {
		Variable variable = new Variable();
		Function containingFunction = new Function(
				symbol("robinson-occurs", 1), List.of(variable));
		Variable preservedVariable = new Variable();
		Function preservedTerm = constant("robinson-occurs-preserved");
		Substitution unifier = new Substitution();
		unifier.addReplace(preservedVariable, preservedTerm);

		assertFalse(variable.isUnifiableWith(containingFunction, unifier));
		assertSame(preservedTerm, unifier.get(preservedVariable));
		assertNull(unifier.get(variable));
		assertSame(variable, containingFunction.getChild(0));
	}

	@Test
	@DisplayName("subtract a context tower from a left hat function")
	void subtractContextTowerFromLeftHatFunction() {
		HatFixture fixture = hatFixture("robinson-left-hat");
		Variable hatArgument = new Variable();
		Variable towerArgument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), hatArgument, List.of(2, 3));
		Function tower = new Function(
				fixture.contextSymbol(), List.of(towerArgument));
		Substitution unifier = new Substitution();

		assertTrue(hat.isUnifiableWith(tower, unifier));
		assertHatMapping(
				unifier.get(towerArgument), fixture.hatSymbol(), hatArgument, 2, 2);
		assertSame(hatArgument, hat.getArgument());
		assertSame(towerArgument, tower.getChild(0));
	}

	@Test
	@DisplayName("preserve disagreement orientation for a right hat function")
	void preserveDisagreementOrientationForRightHatFunction() {
		HatFixture fixture = hatFixture("robinson-right-hat");
		Variable towerArgument = new Variable();
		Variable hatArgument = new Variable();
		Function tower = new Function(
				fixture.contextSymbol(), List.of(towerArgument));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), hatArgument, List.of(2, 3));
		Substitution unifier = new Substitution();

		assertTrue(tower.isUnifiableWith(hat, unifier));
		assertHatMapping(
				unifier.get(towerArgument), fixture.hatSymbol(), hatArgument, 2, 2);
	}

	@Test
	@DisplayName("fall back to subtracting the smaller left hat from the right")
	void fallBackToSubtractingLeftHatFromRightHat() {
		HatFixture fixture = hatFixture("robinson-two-hats");
		Variable smallerArgument = new Variable();
		Variable largerArgument = new Variable();
		HatFunction smaller = new HatFunction(
				fixture.hatSymbol(), smallerArgument, List.of(1, 1));
		HatFunction larger = new HatFunction(
				fixture.hatSymbol(), largerArgument, List.of(3, 4));
		Substitution unifier = new Substitution();

		assertTrue(smaller.isUnifiableWith(larger, unifier));
		assertHatMapping(
				unifier.get(smallerArgument),
				fixture.hatSymbol(), largerArgument, 2, 3);
	}

	@Test
	@DisplayName("reject incompatible hat contexts without changing substitution")
	void rejectIncompatibleHatContextsWithoutChangingSubstitution() {
		HatFixture firstFixture = hatFixture("robinson-first-context");
		HatFixture secondFixture = hatFixture("robinson-second-context");
		HatFunction first = new HatFunction(
				firstFixture.hatSymbol(), constant("robinson-first-argument"), 1, 1);
		HatFunction second = new HatFunction(
				secondFixture.hatSymbol(), constant("robinson-second-argument"), 1, 1);
		Variable preservedVariable = new Variable();
		Function preservedTerm = constant("robinson-hat-preserved");
		Substitution unifier = new Substitution();
		unifier.addReplace(preservedVariable, preservedTerm);

		assertFalse(first.isUnifiableWith(second, unifier));
		assertSame(preservedTerm, unifier.get(preservedVariable));
	}

	private static void assertHatMapping(
			Term mappedTerm,
			HatFunctionSymbol expectedSymbol,
			Term expectedArgument,
			int firstExponent,
			int secondExponent) {

		assertTrue(mappedTerm instanceof HatFunction);
		HatFunction mappedHat = (HatFunction) mappedTerm;
		assertSame(expectedSymbol, mappedHat.getRootSymbol());
		assertSame(expectedArgument, mappedHat.getArgument());
		assertTrue(mappedHat.equalExponents(new HatFunction(
				expectedSymbol,
				expectedArgument,
				List.of(firstExponent, secondExponent))));
	}

	private static HatFixture hatFixture(String prefix) {
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol = symbol(prefix, 1);
		Function context = new Function(
				contextSymbol, List.of(contextVariable));
		return new HatFixture(
				contextSymbol,
				HatFunctionSymbol.intern(context, contextVariable));
	}

	private record HatFixture(
			FunctionSymbol contextSymbol,
			HatFunctionSymbol hatSymbol) {}

	private static Function constant(String prefix) {
		return new Function(symbol(prefix, 0), List.of());
	}

	private static FunctionSymbol symbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}
}
