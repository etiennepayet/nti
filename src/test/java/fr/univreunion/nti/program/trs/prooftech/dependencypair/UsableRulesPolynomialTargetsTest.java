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
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.HomeomorphicEmbeddingDependencyPairProcessor;

class UsableRulesPolynomialTargetsTest {

	private static final List<String> UNFILTERED_TARGETS = List.of(
			"usable-rules-polynomial/list-sum-prod-bin-assoc-distr-app.ari",
			"usable-rules-polynomial/log2.ari",
			"usable-rules-polynomial/ternary-hard.ari",
			"usable-rules-polynomial/tree.ari");

	private static final List<String> FILTERED_TARGETS = List.of(
			"usable-rules-polynomial/quick.ari",
			"usable-rules-polynomial/ex1-luc02b-fr.ari",
			"usable-rules-polynomial/ex49-gm04-z.ari",
			"usable-rules-polynomial/ex6-luc98-c.ari",
			"usable-rules-polynomial/ex7-blr02-fr.ari",
			"usable-rules-polynomial/palindrome-nosorts-c.ari",
			"usable-rules-polynomial/peano-nosorts-c.ari");

	@Test
	@DisplayName("prove the eleven usable-rule polynomial survey targets")
	void proveUsableRulePolynomialSurveyTargets() throws Exception {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();
		proveAll(UNFILTERED_TARGETS,
				config.buildUnfilteredFinitenessProcessors(
						new HomeomorphicEmbeddingDependencyPairProcessor()));
		proveAll(FILTERED_TARGETS,
				config.buildFilteredFinitenessProcessors(
						new HomeomorphicEmbeddingDependencyPairProcessor()));
	}

	private static void proveAll(
			List<String> targets, List<DependencyPairProcessor> processors)
			throws Exception {

		for (String target : targets) {
			Trs trs = (Trs) ProgramFactory.parse(resourcePath(target).toString());
			Proof proof = new DependencyPairFramework(processors, List.of())
					.run(trs, new AnalysisContext(true, null));

			assertEquals(Proof.ProofResult.YES, proof.getResult(), target);
			String description = proof.toString();
			assertTrue(description.contains("Using usable rules:"), target);
			assertTrue(description.contains(
					"Polynomial order induced by the interpretation:"), target);
		}
	}

	private static Path resourcePath(String resource) throws URISyntaxException {
		return Path.of(UsableRulesPolynomialTargetsTest.class.getClassLoader()
				.getResource(resource).toURI());
	}
}
