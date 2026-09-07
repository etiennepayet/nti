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

package fr.univreunion.nti.program.lp.binaryunfolding;

import java.util.HashMap;

import fr.univreunion.nti.program.lp.UnfoldedRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;

/**
 * Builds the identity-unfolded rule for one selected body atom.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class IdentityBinaryUnfolder {

	/**
	 * Unfolds the selected body atom with identity.
	 *
	 * @param rule the rule computed so far during the unfolding
	 * @param bodyIndex the selected body atom index
	 * @param iteration the current iteration of the unfolding operator
	 * @return the rule produced by identity unfolding
	 */
	static UnfoldedRuleLp unfold(
			UnfoldedRuleLp rule,
			int bodyIndex,
			int iteration) {

		HashMap<Term,Term> copies = new HashMap<>();
		Function unfoldedHead = (Function) rule.getHead().deepCopy(copies);
		Function[] unfoldedBody = {
				(Function) rule.getBody(bodyIndex).deepCopy(copies)
		};

		return UnfoldedRuleLp.of(unfoldedHead, unfoldedBody, iteration);
	}

	/**
	 * Disables construction.
	 */
	private IdentityBinaryUnfolder() {
	}
}
