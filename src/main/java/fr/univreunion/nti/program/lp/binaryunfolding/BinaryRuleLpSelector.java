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

package fr.univreunion.nti.program.lp.binaryunfolding;

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.UnfoldedRuleLp;

/**
 * Selects binary rules from unfolded logic-program rules.
 */
final class BinaryRuleLpSelector {

	/**
	 * This class cannot be instantiated.
	 */
	private BinaryRuleLpSelector() {}

	/**
	 * Returns the binary rules contained in the provided unfolded rules.
	 *
	 * @param unfolded the unfolded rules to inspect
	 * @return the binary rules contained in the provided unfolded rules
	 */
	static List<BinaryRuleLp> selectFrom(
			Iterable<UnfoldedRuleLp> unfolded) {
		List<BinaryRuleLp> binaryRules = new ArrayList<>();
		for (UnfoldedRuleLp unfoldedRule : unfolded)
			if (unfoldedRule instanceof BinaryRuleLp binaryRule)
				binaryRules.add(binaryRule);
		return binaryRules;
	}
}
