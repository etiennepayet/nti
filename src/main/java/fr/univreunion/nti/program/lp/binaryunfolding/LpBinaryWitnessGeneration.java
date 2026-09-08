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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import fr.univreunion.nti.program.lp.NonTerminationWitness;

/**
 * The nontermination witnesses generated during one binary-unfolding step.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class LpBinaryWitnessGeneration {

	/**
	 * The generated witnesses.
	 */
	private final List<NonTerminationWitness> generatedWitnesses;

	/**
	 * Builds a witness generation from unit and extended witnesses.
	 *
	 * @param unitWitnesses the unit witnesses generated during the step
	 * @param extendedWitnesses the extended witnesses generated during the step
	 * @return the witness generation for the step
	 */
	static LpBinaryWitnessGeneration from(
			Collection<NonTerminationWitness> unitWitnesses,
			Collection<NonTerminationWitness> extendedWitnesses) {
		List<NonTerminationWitness> generatedWitnesses =
				new ArrayList<>(unitWitnesses);
		generatedWitnesses.addAll(extendedWitnesses);
		return new LpBinaryWitnessGeneration(generatedWitnesses);
	}

	/**
	 * Builds a witness generation from the provided generated witnesses.
	 *
	 * @param generatedWitnesses the generated witnesses
	 */
	private LpBinaryWitnessGeneration(
			Collection<NonTerminationWitness> generatedWitnesses) {
		this.generatedWitnesses = new ArrayList<>(generatedWitnesses);
	}

	/**
	 * Returns all witnesses generated during the step, preserving
	 * the historical order: unit witnesses first, then extended ones.
	 * The returned list is a defensive copy.
	 *
	 * @return all witnesses generated during the step
	 */
	List<NonTerminationWitness> newWitnesses() {
		return new ArrayList<>(this.generatedWitnesses);
	}
}
