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

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.lp.NonTerminationWitness;

/**
 * The stable state used while running the binary-unfolding proof.
 *
 * @param context the context of the analysis
 * @param proof the proof being built
 * @param unfolder the binary unfolder
 * @param loopDictionary the loop dictionary constructed during the proof
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

record LpBinaryProofState(
		AnalysisContext context,
		Proof proof,
		LpBinaryUnfolder unfolder,
		List<NonTerminationWitness> loopDictionary) {}
