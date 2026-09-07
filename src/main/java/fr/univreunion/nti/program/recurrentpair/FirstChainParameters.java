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
 * Parameters computed from the first finite chain.
 *
 * @param c2 the context <code>c2</code>
 * @param m1 the power <code>m1</code> in the first chain
 * @param n1 the power <code>n1</code> in the first chain
 * @param n2 the power <code>n2</code> in the first chain
 * @param n4 the power <code>n4</code> needed by the second chain
 * @param delta the difference <code>m1 - n2</code>
 */
record FirstChainParameters(
		Term c2,
		int m1,
		int n1,
		int n2,
		int n4,
		int delta) {
}
