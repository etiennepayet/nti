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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;

/**
 * Runs the dependency pair phase of the TRS termination prover.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

@FunctionalInterface
interface DependencyPairAnalysisRunner {

	/**
	 * Runs the dependency pair analysis.
	 *
	 * @param context the context of the analysis
	 * @param diagnosticProof the proof receiving analysis failures
	 * @return the selected dependency pair proof, or {@code null}
	 */
	Proof run(AnalysisContext context, Proof diagnosticProof);
}
