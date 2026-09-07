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

/**
 * Input data used to compute the parameters of the second finite chain.
 *
 * @param initialS the initial ground term c2^m2[s]
 * @param c2 the context <code>c2</code>
 * @param x2 the variable at the square position in <code>u2</code>
 * @param v2AtSquareIndex the term at the square position in <code>v2</code>
 * @param n2 the integer <code>n2</code>
 * @param n4 the integer <code>n4</code>
 * @param delta the difference <code>m1 - n2</code>
 */
record SecondChainInput(
		Term initialS,
		Term c2,
		Term x2,
		Term v2AtSquareIndex,
		int n2,
		int n4,
		int delta) {
}
