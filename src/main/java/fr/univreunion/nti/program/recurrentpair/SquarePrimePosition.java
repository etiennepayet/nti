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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.recurrentpair;

import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Data identified at the square' position of <code>c1</code>.
 *
 * @param s the ground term found at the square' position of <code>u2</code>
 * @param u1AtSquarePrimeIndex the term at the square' position of
 * <code>u1</code>
 * @param v1AtSquarePrimeIndex the term at the square' position of
 * <code>v1</code>
 * @param y1 the only variable occurring in the square' components of
 * <code>u1</code> and <code>v1</code>
 */
record SquarePrimePosition(
		Term s,
		Term u1AtSquarePrimeIndex,
		Term v1AtSquarePrimeIndex,
		Variable y1) {
}
