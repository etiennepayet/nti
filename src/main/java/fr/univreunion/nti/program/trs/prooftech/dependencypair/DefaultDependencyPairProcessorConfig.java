/*
 * Copyright 2025 Etienne Payet <etienne.payet at univ-reunion.fr>
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

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.ForwardInstantiationDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.HomeomorphicEmbeddingDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.Iclp25PatternUnfoldingDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.KboDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.LpoDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.PayetRuleUnfoldingDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.PolynomialInterpretationDependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.SubtermCriterionDependencyPairProcessor;

/**
 * Builds the default dependency pair processors used by the TRS termination
 * prover.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

class DefaultDependencyPairProcessorConfig {

	/**
	 * The maximum number of polynomial coefficients allowed without argument
	 * filters.
	 */
	private static final int UNFILTERED_MAX_COEFFICIENT_COUNT = 14;

	/**
	 * The maximum depth allowed for a TRS rule without argument filters.
	 */
	private static final int UNFILTERED_MAX_DEPTH = 4;

	/**
	 * The maximum number of polynomial coefficients allowed with argument
	 * filters. 25 seems to be the best value to get the maximum number of
	 * successes in TermComp.
	 */
	private static final int FILTERED_MAX_COEFFICIENT_COUNT = 25;

	/**
	 * The maximum depth allowed for a TRS rule with argument filters.
	 */
	private static final int FILTERED_MAX_DEPTH = 5;

	/**
	 * The maximum depth used by the bounded-depth rule unfolding processor.
	 */
	private static final int RULE_UNFOLDING_BOUNDED_MAX_DEPTH = 20;

	/**
	 * Builds the finiteness processors used by the unfiltered DP framework
	 * variant.
	 *
	 * @param homeomorphicEmbeddingProcessor the shared homeomorphic
	 * embedding processor
	 * @return the finiteness processors
	 */
	List<DependencyPairProcessor> buildUnfilteredFinitenessProcessors(
			HomeomorphicEmbeddingDependencyPairProcessor homeomorphicEmbeddingProcessor) {

		List<DependencyPairProcessor> processors = new ArrayList<>();
		processors.add(homeomorphicEmbeddingProcessor);
		processors.add(new SubtermCriterionDependencyPairProcessor());
		processors.add(new LpoDependencyPairProcessor(false));
		processors.add(new PolynomialInterpretationDependencyPairProcessor(
				false, UNFILTERED_MAX_COEFFICIENT_COUNT,
				UNFILTERED_MAX_DEPTH));
		processors.add(new KboDependencyPairProcessor(
				false, UNFILTERED_MAX_COEFFICIENT_COUNT));
		processors.add(new ForwardInstantiationDependencyPairProcessor());

		return processors;
	}

	/**
	 * Builds the finiteness processors used by the filtered DP framework
	 * variant.
	 *
	 * @param homeomorphicEmbeddingProcessor the shared homeomorphic
	 * embedding processor
	 * @return the finiteness processors
	 */
	List<DependencyPairProcessor> buildFilteredFinitenessProcessors(
			HomeomorphicEmbeddingDependencyPairProcessor homeomorphicEmbeddingProcessor) {

		List<DependencyPairProcessor> processors = new ArrayList<>();
		processors.add(homeomorphicEmbeddingProcessor);
		processors.add(new SubtermCriterionDependencyPairProcessor());
		processors.add(new LpoDependencyPairProcessor(true));
		processors.add(new PolynomialInterpretationDependencyPairProcessor(
				true, FILTERED_MAX_COEFFICIENT_COUNT,
				FILTERED_MAX_DEPTH));
		processors.add(new KboDependencyPairProcessor(
				true, FILTERED_MAX_COEFFICIENT_COUNT));

		return processors;
	}

	/**
	 * Builds the infiniteness processors used by the unfiltered DP framework.
	 *
	 * @return the infiniteness processors
	 */
	List<DependencyPairProcessor> buildInfinitenessProcessors() {
		List<DependencyPairProcessor> processors = new ArrayList<>();
		processors.add(new PayetRuleUnfoldingDependencyPairProcessor(
				this.buildBoundedDepthRuleUnfoldingParameters()));
		processors.add(new PayetRuleUnfoldingDependencyPairProcessor(
				this.buildNoBackwardUnfoldingParameters()));
		processors.add(new PayetRuleUnfoldingDependencyPairProcessor(
				this.buildAllStrategiesParameters()));
		processors.add(new Iclp25PatternUnfoldingDependencyPairProcessor(new Parameters()));

		return processors;
	}

	/**
	 * Builds the parameters used by the bounded-depth rule unfolding processor.
	 *
	 * @return the parameters used by the bounded-depth rule unfolding processor
	 */
	private Parameters buildBoundedDepthRuleUnfoldingParameters() {
		Parameters parameters = new Parameters();
		parameters.setMaxDepth(RULE_UNFOLDING_BOUNDED_MAX_DEPTH);
		return parameters;
	}

	/**
	 * Builds the parameters used by the rule unfolding processor that disables
	 * backward unfolding.
	 *
	 * @return the parameters used by the rule unfolding processor that disables
	 * backward unfolding
	 */
	private Parameters buildNoBackwardUnfoldingParameters() {
		Parameters parameters = new Parameters();
		parameters.disableBackwardUnfolding();
		return parameters;
	}

	/**
	 * Builds the parameters used by the rule unfolding processor that enables
	 * all loop search strategies.
	 *
	 * @return the parameters used by the rule unfolding processor that enables
	 * all loop search strategies
	 */
	private Parameters buildAllStrategiesParameters() {
		Parameters parameters = new Parameters();
		parameters.setStrategy(StrategyLoop.ALL);
		return parameters;
	}
}
