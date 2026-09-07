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

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.ForwardInstantiationDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.HomeomorphicEmbeddingDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.Iclp25PatternUnfoldingDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.KboDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.LpoDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.PayetRuleUnfoldingDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.PolynomialInterpretationDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.SubtermCriterionDependencyPairProcessor;

class DefaultDependencyPairProcessorConfigTest {

	@Test
	@DisplayName("build unfiltered finiteness processors in their configured order")
	void buildUnfilteredFinitenessProcessorsInOrder() {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();
		HomeomorphicEmbeddingDependencyPairProcessor embedding =
				new HomeomorphicEmbeddingDependencyPairProcessor();

		List<DependencyPairProcessor> processors =
				config.buildUnfilteredFinitenessProcessors(embedding);

		assertFinitenessProcessorTypes(processors, embedding, true);
		for (DependencyPairProcessor processor : processors)
			assertFalse(processor.usesFiltering());
	}

	@Test
	@DisplayName("build filtered finiteness processors in their configured order")
	void buildFilteredFinitenessProcessorsInOrder() {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();
		HomeomorphicEmbeddingDependencyPairProcessor embedding =
				new HomeomorphicEmbeddingDependencyPairProcessor();

		List<DependencyPairProcessor> processors =
				config.buildFilteredFinitenessProcessors(embedding);

		assertFinitenessProcessorTypes(processors, embedding, false);
		assertFalse(processors.get(0).usesFiltering());
		assertFalse(processors.get(1).usesFiltering());
		for (int i = 2; i < processors.size(); i++)
			assertTrue(processors.get(i).usesFiltering());
	}

	@Test
	@DisplayName("build infiniteness processors in their configured order")
	void buildInfinitenessProcessorsInOrder() {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();

		List<DependencyPairProcessor> processors =
				config.buildInfinitenessProcessors();

		assertEquals(4, processors.size());
		assertInstanceOf(PayetRuleUnfoldingDependencyPairProcessor.class,
				processors.get(0));
		assertInstanceOf(PayetRuleUnfoldingDependencyPairProcessor.class,
				processors.get(1));
		assertInstanceOf(PayetRuleUnfoldingDependencyPairProcessor.class,
				processors.get(2));
		assertInstanceOf(Iclp25PatternUnfoldingDependencyPairProcessor.class,
				processors.get(3));
		assertTrue(processors.get(0).toString().contains("max=20"));
		assertTrue(processors.get(1).toString().contains("max=-1"));
		assertTrue(processors.get(2).toString().contains("max=-1"));
		for (DependencyPairProcessor processor : processors)
			assertFalse(processor.usesFiltering());
	}

	@Test
	@DisplayName("build fresh processor collections and instances")
	void buildFreshProcessorCollectionsAndInstances() {
		DefaultDependencyPairProcessorConfig config =
				new DefaultDependencyPairProcessorConfig();
		HomeomorphicEmbeddingDependencyPairProcessor embedding =
				new HomeomorphicEmbeddingDependencyPairProcessor();

		List<DependencyPairProcessor> firstFiniteness =
				config.buildUnfilteredFinitenessProcessors(embedding);
		List<DependencyPairProcessor> secondFiniteness =
				config.buildUnfilteredFinitenessProcessors(embedding);
		List<DependencyPairProcessor> firstInfiniteness =
				config.buildInfinitenessProcessors();
		List<DependencyPairProcessor> secondInfiniteness =
				config.buildInfinitenessProcessors();

		assertNotSame(firstFiniteness, secondFiniteness);
		assertSame(embedding, firstFiniteness.getFirst());
		assertSame(embedding, secondFiniteness.getFirst());
		for (int i = 1; i < firstFiniteness.size(); i++)
			assertNotSame(firstFiniteness.get(i), secondFiniteness.get(i));

		assertNotSame(firstInfiniteness, secondInfiniteness);
		for (int i = 0; i < firstInfiniteness.size(); i++)
			assertNotSame(firstInfiniteness.get(i), secondInfiniteness.get(i));
	}

	private static void assertFinitenessProcessorTypes(
			List<DependencyPairProcessor> processors,
			HomeomorphicEmbeddingDependencyPairProcessor embedding,
			boolean includesForwardInstantiation) {

		assertEquals(includesForwardInstantiation ? 6 : 5, processors.size());
		assertSame(embedding, processors.get(0));
		assertInstanceOf(SubtermCriterionDependencyPairProcessor.class,
				processors.get(1));
		assertInstanceOf(LpoDependencyPairProcessor.class, processors.get(2));
		assertInstanceOf(PolynomialInterpretationDependencyPairProcessor.class,
				processors.get(3));
		assertInstanceOf(KboDependencyPairProcessor.class, processors.get(4));
		if (includesForwardInstantiation)
			assertInstanceOf(ForwardInstantiationDependencyPairProcessor.class,
					processors.get(5));
	}
}
