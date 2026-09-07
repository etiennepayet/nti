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
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.FinitenessDependencyPairProcessor;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Variable;

class FinitenessDependencyPairProcessorTest {

	@Test
	@DisplayName("stop after solving the full unfiltered problem")
	void stopAfterSolvingFullProblem() throws IOException {
		RecordingProcessor processor = new RecordingProcessor(
				true, true, Outcome.FINITE);

		DependencyPairProcessorResult result = processor.run(
				problem(), filtering(), 0, context());

		assertTrue(result.isFinite());
		assertEquals(List.of("none"), processor.filterings());
	}

	@Test
	@DisplayName("do not enumerate filters when filtering is disabled")
	void doNotEnumerateFiltersWhenDisabled() throws IOException {
		RecordingProcessor processor = new RecordingProcessor(
				false, true, Outcome.FAILED);

		DependencyPairProcessorResult result = processor.run(
				problem(), filtering(), 0, context());

		assertTrue(result.isFailed());
		assertEquals(List.of("none"), processor.filterings());
	}

	@Test
	@DisplayName("enumerate filters in order until one proves finiteness")
	void enumerateFiltersInOrderUntilFinite() throws IOException {
		RecordingProcessor processor = new RecordingProcessor(
				true, true, Outcome.FAILED, Outcome.FAILED, Outcome.FINITE);

		DependencyPairProcessorResult result = processor.run(
				problem(), filtering(), 0, context());

		assertTrue(result.isFinite());
		assertEquals(List.of("none", "[0]", "[1]"), processor.filterings());
	}

	@Test
	@DisplayName("stop filter enumeration after decomposition")
	void stopFilterEnumerationAfterDecomposition() throws IOException {
		RecordingProcessor processor = new RecordingProcessor(
				true, true, Outcome.FAILED, Outcome.DECOMPOSED);

		DependencyPairProcessorResult result = processor.run(
				problem(), filtering(), 0, context());

		assertTrue(result.isDecomposed());
		assertEquals(List.of("none", "[0]"), processor.filterings());
	}

	@Test
	@DisplayName("return a fresh failure after exhausting all filters")
	void returnFreshFailureAfterExhaustingFilters() throws IOException {
		RecordingProcessor processor = new RecordingProcessor(
				true, true, Outcome.FAILED, Outcome.FAILED, Outcome.FAILED);

		DependencyPairProcessorResult result = processor.run(
				problem(), filtering(), 0, context());

		assertTrue(result.isFailed());
		assertEquals(List.of("none", "[0]", "[1]"), processor.filterings());
		assertFalse(result.getProof().toString().contains("attempt"));
	}

	@Test
	@DisplayName("report an unsuitable number of filter instantiations")
	void reportUnsuitableFilterCount() throws IOException {
		RecordingProcessor processor = new RecordingProcessor(
				true, false, Outcome.FAILED);

		DependencyPairProcessorResult result = processor.run(
				problem(), filtering(), 3, context());

		assertTrue(result.isFailed());
		assertEquals(List.of("none"), processor.filterings());
		assertTrue(result.getProof().toString().contains(
				"Too many argument filtering possibilities (2)"));
	}

	@Test
	@DisplayName("preserve interruption while enumerating filters")
	void preserveInterruptionWhileEnumeratingFilters() throws IOException {
		RecordingProcessor processor = new RecordingProcessor(
				true, true, Outcome.FAILED, Outcome.INTERRUPT_AND_FAIL);
		try {
			DependencyPairProcessorResult result = processor.run(
					problem(), filtering(), 0, context());

			assertTrue(result.isFailed());
			assertTrue(Thread.currentThread().isInterrupted());
			assertEquals(List.of("none", "[0]"), processor.filterings());
		}
		finally {
			Thread.interrupted();
		}
	}

	private static DependencyPairProblem problem() throws IOException {
		Trs trs = parseTrs("f(X,Y) -> f(X,Y)");
		return new DependencyPairProblem(trs, new DependencyPairs(List.of()));
	}

	private static ArgFiltering filtering() {
		ArgFiltering filtering = new ArgFiltering();
		filtering.add(FunctionSymbol.intern("f", 2));
		return filtering;
	}

	private static AnalysisContext context() {
		return new AnalysisContext(true, null);
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new ArrayList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return new Trs("", rules, "FULL");
	}

	private enum Outcome {
		FINITE,
		DECOMPOSED,
		FAILED,
		INTERRUPT_AND_FAIL
	}

	private static final class RecordingProcessor
			extends FinitenessDependencyPairProcessor {

		private final boolean suitable;
		private final List<Outcome> outcomes;
		private final List<String> filterings = new ArrayList<>();
		private int callIndex;

		private RecordingProcessor(
				boolean usesFiltering, boolean suitable, Outcome... outcomes) {

			super(usesFiltering);
			this.suitable = suitable;
			this.outcomes = List.of(outcomes);
		}

		@Override
		protected DependencyPairProcessorResult run(
				DependencyPairProblem problem,
				ArgFiltering filtering,
				Collection<PairOfTerms> trsPairs,
				Collection<PairOfTerms> dependencyPairs,
				int indentation,
				AnalysisContext context) {

			this.filterings.add(filtering == null
					? "none"
					: filtering.get(FunctionSymbol.intern("f", 2)).toString());
			Proof proof = context.createProof();
			proof.printlnIfVerbose("attempt " + this.callIndex);
			Outcome outcome = this.outcomes.get(this.callIndex++);
			return switch (outcome) {
				case FINITE -> DependencyPairProcessorResult.finite(proof);
				case DECOMPOSED -> DependencyPairProcessorResult.decomposed(proof);
				case FAILED -> DependencyPairProcessorResult.failed(proof);
				case INTERRUPT_AND_FAIL -> {
					Thread.currentThread().interrupt();
					yield DependencyPairProcessorResult.failed(proof);
				}
			};
		}

		@Override
		protected boolean isSuitable(FilterInstantiator instantiator) {
			return this.suitable;
		}

		private List<String> filterings() {
			return this.filterings;
		}
	}
}
