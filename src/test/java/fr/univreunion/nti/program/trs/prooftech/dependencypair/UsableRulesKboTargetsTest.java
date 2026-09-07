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
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.HomeomorphicEmbeddingDependencyPairProcessor;

class UsableRulesKboTargetsTest {

	private static final List<String> TARGETS = List.of(
			"usable-rules-kbo/rta1.ari",
			"usable-rules-kbo/der95-12.ari",
			"usable-rules-kbo/hm-t005.ari");

	@Test
	@DisplayName("prove the three isolated survey targets with usable rules and KBO")
	void proveIsolatedSurveyTargets() throws Exception {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();
		for (String target : TARGETS) {
			Trs trs = (Trs) ProgramFactory.parse(resourcePath(target).toString());
			Proof proof = new DependencyPairFramework(
					config.buildUnfilteredFinitenessProcessors(
							new HomeomorphicEmbeddingDependencyPairProcessor()),
					List.of())
					.run(trs, new AnalysisContext(true, null));

			assertEquals(Proof.ProofResult.YES, proof.getResult(),
					target + System.lineSeparator() + proof);
			assertTrue(proof.toString().contains("Using usable rules:"), target);
		}
	}

	private static Path resourcePath(String resource) throws URISyntaxException {
		return Path.of(UsableRulesKboTargetsTest.class.getClassLoader()
				.getResource(resource).toURI());
	}
}
