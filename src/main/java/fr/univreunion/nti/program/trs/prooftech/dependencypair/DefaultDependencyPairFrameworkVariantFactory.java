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

import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.HomeomorphicEmbeddingDependencyPairProcessor;

/**
 * Builds the unfiltered and filtered default framework variants.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class DefaultDependencyPairFrameworkVariantFactory
		implements DependencyPairFrameworkVariantFactory {

	/** The dependency pair processor configuration. */
	private final DefaultDependencyPairProcessorConfig processorConfig;

	/**
	 * Builds a variant factory using the provided processor configuration.
	 *
	 * @param processorConfig the processor configuration to use
	 */
	DefaultDependencyPairFrameworkVariantFactory(
			DefaultDependencyPairProcessorConfig processorConfig) {

		this.processorConfig = processorConfig;
	}

	/**
	 * Builds the framework variant tasks.
	 *
	 * @param trs the TRS to analyze
	 * @param context the context of the analysis
	 * @return the named framework attempts
	 */
	@Override
	public List<DependencyPairFrameworkAttempt> buildAttempts(
			Trs trs, AnalysisContext context) {
		HomeomorphicEmbeddingDependencyPairProcessor embeddingProcessor =
				new HomeomorphicEmbeddingDependencyPairProcessor();
		DependencyPairFramework unfilteredFramework = new DependencyPairFramework(
				this.processorConfig.buildUnfilteredFinitenessProcessors(
						embeddingProcessor),
				this.processorConfig.buildInfinitenessProcessors());
		DependencyPairFramework filteredFramework = new DependencyPairFramework(
				this.processorConfig.buildFilteredFinitenessProcessors(
						embeddingProcessor),
				List.of());

		return List.of(
				new DependencyPairFrameworkAttempt(
						"Unfiltered",
						() -> unfilteredFramework.run(trs, context),
						unfilteredFramework::infinitenessAttempts),
				new DependencyPairFrameworkAttempt(
						"Argument-filtered",
						() -> filteredFramework.run(trs.copy(null), context),
						filteredFramework::infinitenessAttempts));
	}
}
