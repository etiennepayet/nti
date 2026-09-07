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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.net.URISyntaxException;
import java.nio.file.Path;
import java.util.List;
import java.util.Objects;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.ProgramFactory;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.HomeomorphicEmbeddingDependencyPairProcessor;

class ForwardInstantiationTargetsTest {

	private static final List<String> TARGETS = List.of(
			"forward-instantiation/forward-instantiation.ari",
			"forward-instantiation/forward-instantiation2.ari",
			"forward-instantiation/cade04t.ari",
			"forward-instantiation/mixed-2.ari",
			"forward-instantiation/lindau.ari",
			"forward-instantiation/sk90-4.41.ari",
			"forward-instantiation/sk90-4.50.ari",
			"forward-instantiation/sk90-4.55.ari",
			"forward-instantiation/strategy-4.20.ari",
			"forward-instantiation/strategy-4.20a.ari",
			"forward-instantiation/strategy-4.25.ari",
			"forward-instantiation/test830.ari",
			"forward-instantiation/ex4-7-15-bor03-l.ari",
			"forward-instantiation/various-02.ari",
			"forward-instantiation/various-03.ari",
			"forward-instantiation/various-04.ari",
			"forward-instantiation/various-05.ari",
			"forward-instantiation/various-08.ari",
			"forward-instantiation/various-22.ari",
			"forward-instantiation/various-25.ari");

	@Test
	@DisplayName("prove the twenty isolated survey targets")
	void proveIsolatedSurveyTargets() throws Exception {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();
		for (String target : TARGETS) {
			Trs trs = (Trs) ProgramFactory.parse(resourcePath(target).toString());
			Proof proof = new DependencyPairFramework(
					config.buildUnfilteredFinitenessProcessors(
							new HomeomorphicEmbeddingDependencyPairProcessor()),
					List.of()).run(trs, new AnalysisContext(true, null));

			assertEquals(Proof.ProofResult.YES, proof.getResult(),
					target + System.lineSeparator() + proof);
		}
	}

	private static Path resourcePath(String resource) throws URISyntaxException {
		return Path.of(Objects.requireNonNull(
				ForwardInstantiationTargetsTest.class.getClassLoader()
						.getResource(resource)).toURI());
	}
}
