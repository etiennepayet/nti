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
 * Input data used to build the associated nonterminating term.
 *
 * @param chains the finite chains of the built recurrent pair
 * @param root the leading function symbol of c1 and its arity
 * @param s the ground term s of the built recurrent pair
 * @param c2PowerM2OfS the ground term c2^m2[s] of the built recurrent pair
 */
record NonTerminatingTermInput(
		FiniteChains chains,
		RootSymbol root,
		Term s,
		Term c2PowerM2OfS) {
}
