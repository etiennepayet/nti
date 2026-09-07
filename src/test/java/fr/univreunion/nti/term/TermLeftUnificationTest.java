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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.leftunif.LuEquation;

class TermLeftUnificationTest {

	@AfterEach
	void resetEquationTime() {
		LuEquation.resetTime();
	}

	@Test
	@DisplayName("left-unify identical terms without extracting mappings")
	void leftUnifyIdenticalTermsWithoutMappings() {
		Function constant = constant("lu-identical");
		Substitution sigma = new Substitution();
		Substitution rho = new Substitution();

		assertTrue(constant.leftUnifyWith(constant, sigma, rho));
		assertTrue(sigma.isEmpty());
		assertTrue(rho.isEmpty());
	}

	@Test
	@DisplayName("reject root conflicts and occurs-check failures")
	void rejectRootConflictsAndOccursCheckFailures() {
		Substitution sigma = new Substitution();
		Substitution rho = new Substitution();
		Variable preservedDomain = new Variable();
		Variable preservedImage = new Variable();
		sigma.addReplace(preservedDomain, preservedImage);

		assertFalse(constant("lu-conflict-left").leftUnifyWith(
				constant("lu-conflict-right"), sigma, rho));
		assertSame(preservedImage, sigma.get(preservedDomain));
		assertTrue(rho.isEmpty());

		Variable variable = new Variable();
		Function containingTerm = new Function(
				FunctionSymbol.intern(uniqueName("lu-occurs"), 1),
				List.of(variable));
		assertFalse(containingTerm.leftUnifyWith(variable, sigma, rho));
		assertSame(preservedImage, sigma.get(preservedDomain));
		assertTrue(rho.isEmpty());
	}

	@Test
	@DisplayName("extract sigma and rho from repeated source variables")
	void extractSigmaAndRhoFromRepeatedSourceVariables() {
		FunctionSymbol pair =
				FunctionSymbol.intern(uniqueName("lu-extraction"), 2);
		Variable sourceVariable = new Variable();
		Variable targetVariable = new Variable();
		Function constant = constant("lu-extracted-constant");
		Function source = new Function(
				pair, List.of(sourceVariable, sourceVariable));
		Function target = new Function(
				pair, List.of(targetVariable, constant));
		Substitution sigma = new Substitution();
		Substitution rho = new Substitution();

		assertTrue(source.leftUnifyWith(target, sigma, rho));
		assertTrue(sigma.get(targetVariable).deepEquals(constant));
		assertTrue(rho.get(sourceVariable).deepEquals(constant));
		assertNull(sigma.get(sourceVariable));
		assertNull(rho.get(targetVariable));
	}

	@Test
	@DisplayName("preserve decomposition order and equation-time behavior")
	void preserveDecompositionOrderAndEquationTimeBehavior() {
		LuEquation.resetTime();
		FunctionSymbol pair =
				FunctionSymbol.intern(uniqueName("lu-time"), 2);
		Variable firstSource = new Variable();
		Variable secondSource = new Variable();
		Variable firstTarget = new Variable();
		Variable secondTarget = new Variable();
		Function source = new Function(
				pair, List.of(firstSource, secondSource));
		Function target = new Function(
				pair, List.of(firstTarget, secondTarget));

		assertTrue(source.leftUnifyWith(target, null, null));
		assertEquals(5, LuEquation.getCurrentTime());
	}

	private static Function constant(String prefix) {
		return new Function(
				FunctionSymbol.intern(uniqueName(prefix), 0), List.of());
	}

	private static String uniqueName(String prefix) {
		return prefix + "-" + UUID.randomUUID();
	}
}
