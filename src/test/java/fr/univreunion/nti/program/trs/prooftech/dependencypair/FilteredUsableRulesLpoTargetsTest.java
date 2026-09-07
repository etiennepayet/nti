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

class FilteredUsableRulesLpoTargetsTest {

	private static final List<String> TARGETS = List.of(
			"filtered-usable-rules-lpo/ag01-3.49.ari",
			"filtered-usable-rules-lpo/ag01-3.56.ari",
			"filtered-usable-rules-lpo/sk90-4.30.ari",
			"filtered-usable-rules-lpo/strategy-ag01-4.33.ari",
			"filtered-usable-rules-lpo/strategy-ag01-4.37.ari",
			"filtered-usable-rules-lpo/strategy-ag01-4.37a.ari",
			"filtered-usable-rules-lpo/ex4-7-37-bor03-z.ari",
			"filtered-usable-rules-lpo/peano-nosorts-noand-fr.ari");

	@Test
	@DisplayName("prove the eight filtered usable-rule survey targets")
	void proveFilteredUsableRuleSurveyTargets() throws Exception {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();
		for (String target : TARGETS) {
			Trs trs = (Trs) ProgramFactory.parse(resourcePath(target).toString());
			Proof proof = new DependencyPairFramework(
					config.buildFilteredFinitenessProcessors(
							new HomeomorphicEmbeddingDependencyPairProcessor()),
					List.of()).run(trs, new AnalysisContext(true, null));

			assertEquals(Proof.ProofResult.YES, proof.getResult(), target);
		}
	}

	private static Path resourcePath(String resource) throws URISyntaxException {
		return Path.of(FilteredUsableRulesLpoTargetsTest.class.getClassLoader()
				.getResource(resource).toURI());
	}
}
