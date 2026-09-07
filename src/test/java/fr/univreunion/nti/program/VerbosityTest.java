/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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

package fr.univreunion.nti.program;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

class VerbosityTest {

	@Test
	@DisplayName("preserve boolean context compatibility")
	void preserveBooleanContextCompatibility() {
		AnalysisContext quiet = new AnalysisContext(false, null);
		AnalysisContext verbose = new AnalysisContext(true, null);

		assertFalse(quiet.isInVerboseMode());
		assertFalse(quiet.createProof().isInVeryVerboseMode());
		assertTrue(verbose.isInVerboseMode());
		assertFalse(verbose.createProof().isInVeryVerboseMode());
	}

	@Test
	@DisplayName("very verbose proofs retain ordinary details and all-attempt mode")
	void veryVerboseProofsRetainOrdinaryDetailsAndAllAttemptMode() {
		AnalysisContext context = new AnalysisContext(
				Verbosity.VERY_VERBOSE, null);
		Proof proof = context.createProof();

		proof.printlnIfVerbose("ordinary detail");

		assertTrue(context.isInVerboseMode());
		assertTrue(proof.isInVeryVerboseMode());
		assertTrue(proof.hasDescription());
		assertTrue(proof.toString().contains("ordinary detail"));
	}
}
