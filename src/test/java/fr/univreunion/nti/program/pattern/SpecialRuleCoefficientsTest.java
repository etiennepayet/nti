/*
 * Copyright 2025 Etienne Payet <etienne.payet at univ-reunion.fr>
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

package fr.univreunion.nti.program.pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

import org.junit.jupiter.api.Test;

class SpecialRuleCoefficientsTest {

	@Test
	void computesZeroAlpha() {
		SpecialRuleCoefficients coefficients =
				new SpecialRuleCoefficients(1, 1, -1, -1, 0, 0, 0);

		assertEquals(0, coefficients.computeAlpha());
	}

	@Test
	void computesPositiveAlpha() {
		SpecialRuleCoefficients coefficients =
				new SpecialRuleCoefficients(1, 2, 0, 1, 1, 1, 1);

		assertEquals(1, coefficients.computeAlpha());
	}

	@Test
	void roundsPositiveAlphaUp() {
		SpecialRuleCoefficients coefficients =
				new SpecialRuleCoefficients(2, 5, 0, 1, 0, 0, 2);

		assertEquals(2, coefficients.computeAlpha());
	}
}
