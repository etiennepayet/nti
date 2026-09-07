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
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.Iclp25PatternUnfoldingDependencyPairProcessor;
import fr.univreunion.nti.term.Variable;

class Iclp25PatternUnfoldingDependencyPairProcessorTest {

	@Test
	@DisplayName("prove infiniteness by pattern unfolding and count generated rules")
	void proveInfinitenessAndCountGeneratedRules() throws IOException {
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor().run(
				problemFor("f(X) -> f(X)"), null, 0, context);

		assertTrue(result.isInfinite());
		assertTrue(context.getGeneratedRules() > 0);
		assertTrue(result.getProof().toString().contains(
				"success, nontermination proved"));
	}

	@Test
	@DisplayName("fail when pattern unfolding is exhausted without a witness")
	void failWhenPatternUnfoldingIsExhausted() throws IOException {
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor().run(
				problemWithTrs("f(X) -> g(X)"), null, 0, context);

		assertTrue(result.isFailed());
		assertTrue(context.getGeneratedRules() > 0);
		assertTrue(result.getProof().toString().contains(
				"Could not prove nontermination!"));
	}

	@Test
	@DisplayName("bound exponentially growing pattern unfolding")
	void boundExponentiallyGrowingPatternUnfolding() throws IOException {
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor().run(
				problemFor(
						"h(X,c(Y,Z)) -> h(c(s(Y),X),Z)",
						"h(c(s(X),c(s(0),Y)),Z) -> h(Y,c(s(0),c(X,Z)))"),
				null, 0, context);

		assertTrue(result.isFailed());
		assertTrue(context.getGeneratedRules() >= 2_000,
				() -> "generated rules: " + context.getGeneratedRules());
		assertTrue(context.getGeneratedRules() < 2_100,
				() -> "generated rules: " + context.getGeneratedRules());
		assertTrue(result.getProof().toString().contains(
				"Too many unfolded rules ("));
	}

	@Test
	@DisplayName("bound linearly deepening pattern unfolding")
	void boundLinearlyDeepeningPatternUnfolding() throws IOException {
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor().run(
				problemFor(
						"f(f(X)) -> f(X)",
						"g(0) -> g(f(0))"),
				null, 0, context);

		assertTrue(result.isFailed());
		assertTrue(context.getGeneratedRules() > 100);
		assertTrue(context.getGeneratedRules() < 110);
		assertTrue(result.getProof().toString().contains(
				"Too many iterations of the unfolding operator"));
	}

	@Test
	@DisplayName("stop before unfolding when the current thread is interrupted")
	void stopBeforeUnfoldingWhenCurrentThreadIsInterrupted() throws IOException {
		AnalysisContext context = context();
		DependencyPairProblem problem = problemFor("f(X) -> f(X)");
		Thread.currentThread().interrupt();
		try {
			DependencyPairProcessorResult result = newProcessor().run(
					problem, null, 0, context);

			assertTrue(result.isFailed());
			assertEquals(0, context.getGeneratedRules());
			assertTrue(Thread.currentThread().isInterrupted());
		}
		finally {
			Thread.interrupted();
		}
	}

	@Test
	@DisplayName("ignore argument filtering during pattern unfolding")
	void ignoreArgumentFilteringDuringPatternUnfolding() throws IOException {
		Iclp25PatternUnfoldingDependencyPairProcessor processor = newProcessor();
		DependencyPairProcessorResult result = processor.run(
				problemFor("f(X) -> f(X)"), new ArgFiltering(), 0, context());

		assertFalse(processor.usesFiltering());
		assertTrue(result.isInfinite());
	}

	@Test
	@DisplayName("copy the processor parameters independently")
	void copyProcessorParametersIndependently() {
		Parameters parameters = new Parameters();
		Iclp25PatternUnfoldingDependencyPairProcessor processor =
				new Iclp25PatternUnfoldingDependencyPairProcessor(parameters);
		DependencyPairProcessor copy = processor.copy();
		String copiedDescription = copy.toString();

		parameters.setMaxDepth(0);

		assertNotSame(processor, copy);
		assertFalse(processor.toString().equals(copiedDescription));
		assertEquals(copiedDescription, copy.toString());
	}

	private static Iclp25PatternUnfoldingDependencyPairProcessor newProcessor() {
		return new Iclp25PatternUnfoldingDependencyPairProcessor(new Parameters());
	}

	private static DependencyPairProblem problemFor(String... ruleTexts) throws IOException {
		Trs trs = parseTrs(ruleTexts);
		return new InitialDependencyPairProblemCollector()
				.collectFrom(trs).iterator().next();
	}

	private static DependencyPairProblem problemWithTrs(String ruleText) throws IOException {
		return new DependencyPairProblem(
				parseTrs(ruleText), new DependencyPairs(List.of()));
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
}
