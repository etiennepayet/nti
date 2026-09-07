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

/**
 * The coefficients recognized for a special pattern rule.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

record SpecialRuleCoefficients(
		int leftA,
		int rightA,
		int leftB,
		int rightB,
		int leftD,
		int rightD,
		int k) {

	/**
	 * Computes the <code>alpha</code> threshold represented by these coefficients.
	 *
	 * @return the <code>alpha</code> threshold
	 */
	int computeAlpha() {
		int alpha = 0;

		if (this.leftA < this.rightA) {
			int numerator = this.leftA * this.k - (this.rightD - this.leftD);
			if (0 < numerator) {
				int denominator = this.rightA - this.leftA;
				int i = (numerator % denominator == 0 ? 0 : 1);
				alpha = numerator / denominator + i;
			}
		}

		return alpha;
	}
}
