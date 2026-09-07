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

package fr.univreunion.nti.program.trs.polynomial;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

class CoefficientInstantiatorTest {

	@Test
	@DisplayName("enumerate bounded coefficients by identifier and reset")
	void enumerateBoundedCoefficientsByIdentifierAndReset() {
		PolynomialConst first = new PolynomialConst();
		PolynomialConst second = new PolynomialConst();
		PolynomialConst third = new PolynomialConst();
		Intervals intervals = new Intervals();
		intervals.putMin(first, 1);
		intervals.putMax(first, 2);
		intervals.putMin(second, 0);
		intervals.putMax(second, 1);
		intervals.putMin(third, 2);
		intervals.putMax(third, 2);
		CoefficientInstantiator instantiator = new CoefficientInstantiator(
				List.of(third, first, second), intervals, 3);
		List<List<Integer>> instantiations = new ArrayList<>();

		while (instantiator.hasNext()) {
			instantiator.next();
			instantiations.add(values(first, second, third));
		}

		assertEquals(List.of(
				List.of(1, 0, 2),
				List.of(1, 1, 2),
				List.of(2, 0, 2),
				List.of(2, 1, 2)), instantiations);
		assertThrows(NoSuchElementException.class, instantiator::next);
		instantiator.reset();
		assertTrue(instantiator.hasNext());
		assertEquals(List.of(2, 1, 2), values(first, second, third));
		instantiator.next();
		assertEquals(List.of(1, 0, 2), values(first, second, third));
	}

	@Test
	@DisplayName("deliver one empty instantiation and support reset")
	void deliverOneEmptyInstantiationAndSupportReset() {
		CoefficientInstantiator instantiator = new CoefficientInstantiator(
				List.of(), new Intervals(), 2);

		assertTrue(instantiator.hasNext());
		instantiator.next();
		assertFalse(instantiator.hasNext());
		assertThrows(NoSuchElementException.class, instantiator::next);
		instantiator.reset();
		assertTrue(instantiator.hasNext());
		instantiator.next();
		assertFalse(instantiator.hasNext());
	}

	private static List<Integer> values(PolynomialConst... coefficients) {
		List<Integer> values = new ArrayList<>(coefficients.length);
		for (PolynomialConst coefficient : coefficients)
			values.add(coefficient.getValue());
		return values;
	}
}
