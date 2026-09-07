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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.List;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.ProgramFactory;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.LpoDependencyPairProcessor;

class UsableRulesLpoTargetsTest {

	private static final List<String> TARGETS = List.of(
			"usable-rules-lpo/sk90-4.44.ari",
			"usable-rules-lpo/ex15-luc98-z.ari",
			"usable-rules-lpo/ex1-zan97-igm.ari",
			"usable-rules-lpo/ex2-luc03b-z.ari");

	@Test
	@DisplayName("prove the four isolated survey targets with usable rules and LPO")
	void proveIsolatedSurveyTargets() throws Exception {
		for (String target : TARGETS) {
			Trs trs = (Trs) ProgramFactory.parse(resourcePath(target).toString());
			Proof proof = new DependencyPairFramework(
					List.of(new LpoDependencyPairProcessor(false)), List.of())
					.run(trs, new AnalysisContext(true, null));

			assertEquals(Proof.ProofResult.YES, proof.getResult(), target);
			assertTrue(proof.toString().contains("Using usable rules:"), target);
		}
	}

	private static Path resourcePath(String resource) throws URISyntaxException {
		return Path.of(UsableRulesLpoTargetsTest.class.getClassLoader()
				.getResource(resource).toURI());
	}
}
