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
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

class TermUnificationTest {

	@Test
	@DisplayName("unify terms destructively and extract their MGU")
	void unifyDestructivelyAndExtractMgu() {
		FunctionSymbol pair = symbol("unification-success", 2);
		Variable leftVariable = new Variable();
		Variable rightVariable = new Variable();
		Function leftConstant = constant("unification-left-constant");
		Function rightConstant = constant("unification-right-constant");
		Function left = new Function(
				pair, List.of(leftVariable, leftConstant));
		Function right = new Function(
				pair, List.of(rightConstant, rightVariable));
		Substitution mgu = new Substitution();

		assertTrue(left.unifyWith(right, mgu));
		assertTrue(mgu.get(leftVariable).deepEquals(rightConstant));
		assertTrue(mgu.get(rightVariable).deepEquals(leftConstant));
		assertTrue(leftVariable.deepEquals(rightConstant));
		assertTrue(rightVariable.deepEquals(leftConstant));
		assertTrue(left.deepEquals(right));
	}

	@Test
	@DisplayName("unify without extracting an MGU")
	void unifyWithoutExtractingMgu() {
		Variable variable = new Variable();
		Function constant = constant("unification-without-mgu");

		assertTrue(variable.unifyWith(constant));
		assertTrue(variable.deepEquals(constant));
	}

	@Test
	@DisplayName("retain earlier destructive bindings after a later root conflict")
	void retainEarlierBindingsAfterLaterRootConflict() {
		FunctionSymbol pair = symbol("unification-late-conflict", 2);
		Variable variable = new Variable();
		Function boundConstant = constant("unification-bound-before-conflict");
		Function firstRoot = constant("unification-conflicting-first-root");
		Function secondRoot = constant("unification-conflicting-second-root");
		Function left = new Function(pair, List.of(variable, firstRoot));
		Function right = new Function(pair, List.of(boundConstant, secondRoot));
		Substitution mgu = new Substitution();

		assertFalse(left.unifyWith(right, mgu));
		assertTrue(variable.deepEquals(boundConstant));
		assertTrue(mgu.isEmpty());
	}

	@Test
	@DisplayName("reject cycles without changing a provided substitution")
	void rejectCyclesWithoutChangingProvidedSubstitution() {
		Variable cyclicVariable = new Variable();
		Function containingFunction = new Function(
				symbol("unification-cycle", 1), List.of(cyclicVariable));
		Variable preservedDomain = new Variable();
		Variable preservedImage = new Variable();
		Substitution mgu = new Substitution();
		mgu.addReplace(preservedDomain, preservedImage);

		assertFalse(cyclicVariable.unifyWith(containingFunction, mgu));
		assertSame(preservedImage, mgu.get(preservedDomain));
	}

	private static Function constant(String prefix) {
		return new Function(symbol(prefix, 0), List.of());
	}

	private static FunctionSymbol symbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}
}
