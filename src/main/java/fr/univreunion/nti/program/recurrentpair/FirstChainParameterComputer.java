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

import fr.univreunion.nti.term.Hole;
import fr.univreunion.nti.term.Term;

/**
 * Computes the parameters related to the first finite chain.
 */
final class FirstChainParameterComputer {

	/**
	 * This class cannot be instantiated.
	 */
	private FirstChainParameterComputer() {}

	/**
	 * Tries to compute the parameters related to the first finite chain.
	 *
	 * @param input the input data for computing the parameters
	 * @return the computed parameters, or <code>null</code>
	 */
	static synchronized FirstChainParameters tryCompute(
			FirstChainInput input) {

		// 0x25A1 is the UTF-16 encoding of
		// the white square character.
		ContextTower.GroundContext groundContext = ContextTower.groundContextFrom(
				input.squarePrimePosition().u1AtSquarePrimeIndex(),
				input.squarePrimePosition().y1(),
				new Hole("" + '□'));
		if (groundContext == null) return null;

		Term c2 = groundContext.context();
		int m1 = groundContext.power();

		// By definition, c2 contains at least
		// one occurrence of square. Indeed, it
		// is built from u1AtSquarePrimeIndex,
		// which contains y1.

		int n2 = ContextTower.powerOf(
				input.squarePrimePosition().v1AtSquarePrimeIndex(),
				c2,
				input.squarePrimePosition().y1());
		if (n2 < 0 || m1 <= n2) return null;

		int delta = m1 - n2;

		int n1 = ContextTower.powerOf(
				input.chains().v1().getChild(input.holePositions().squareIndex()),
				c2,
				input.holePositions().x1());
		int n4 = ContextTower.powerOf(
				input.chains().v2().getChild(input.holePositions().squarePrimeIndex()),
				c2,
				input.holePositions().x2());
		if (n1 < 0 ||
				(0 < n1 % delta) ||
				n4 < 0 ||
				n4 < n2)
			return null;

		return new FirstChainParameters(c2, m1, n1, n2, n4, delta);
	}
}
