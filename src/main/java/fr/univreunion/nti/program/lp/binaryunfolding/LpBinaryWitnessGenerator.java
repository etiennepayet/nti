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

import java.util.List;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.program.lp.UnfoldedRuleLp;

/**
 * Generates nontermination witnesses from binary unfolded rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class LpBinaryWitnessGenerator {

	/**
	 * This class cannot be instantiated.
	 */
	private LpBinaryWitnessGenerator() {}

	/**
	 * Generates the nontermination witnesses for one unfolding step
	 * and updates the provided loop dictionary.
	 * <p>
	 * Unit witnesses are added to the dictionary before extended
	 * witnesses are generated, preserving the historical generation
	 * order.
	 *
	 * @param unfolded a list of rules resulting from unfolding a logic
	 * program
	 * @param loopDictionary the loop dictionary to update
	 * @return the witnesses generated during the step
	 */
	static LpBinaryWitnessGeneration generateFrom(
			Iterable<UnfoldedRuleLp> unfolded,
			List<NonTerminationWitness> loopDictionary) {
		List<BinaryRuleLp> binaryRules =
				BinaryRuleLpSelector.selectFrom(unfolded);

		List<NonTerminationWitness> unitWitnesses =
				UnitWitnessBuilder.buildFrom(binaryRules);
		loopDictionary.addAll(unitWitnesses);

		List<NonTerminationWitness> extendedWitnesses =
				WitnessExtender.extend(binaryRules, loopDictionary);
		loopDictionary.addAll(extendedWitnesses);

		return LpBinaryWitnessGeneration.from(
				unitWitnesses, extendedWitnesses);
	}
}
