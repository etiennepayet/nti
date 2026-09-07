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
import fr.univreunion.nti.program.trs.StrategyLoop;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessor;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.PayetRuleUnfoldingDependencyPairProcessor;
import fr.univreunion.nti.term.Variable;

class PayetRuleUnfoldingDependencyPairProcessorTest {

	@Test
	@DisplayName("prove infiniteness from a syntactic loop")
	void proveInfinitenessFromSyntacticLoop() throws IOException {
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor(new Parameters()).run(
				problemFor("f(X) -> f(X)"), null, 0, context);

		assertTrue(result.isInfinite());
		assertTrue(context.getGeneratedRules() > 0);
		assertTrue(result.getProof().toString().contains("success, loop found"));
	}

	@Test
	@DisplayName("prioritize a root-closing composed triple")
	void prioritizeRootClosingComposedTriple() throws IOException {
		Parameters parameters = new Parameters();
		parameters.disableBackwardUnfolding();
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor(parameters).run(
				problemFor(
						"j(X,l(Y),Z) -> p(X,j(X,Y,Z),z)",
						"p(X,s(Y),Z) -> j(X,Y,Z)",
						"j(X,Y,Z) -> X"),
				null, 0, context);

		assertTrue(result.isInfinite());
		assertTrue(result.getProof().toString().contains("[iteration = 2]"));
		assertTrue(result.getProof().toString().contains(
				"j^#(s(_0),l(_1),_2) -> j^#(s(_0),_0,z)"));
		assertEquals(-1, parameters.getMaxDepth());
	}

	@Test
	@DisplayName("fail when rule unfolding is exhausted")
	void failWhenRuleUnfoldingIsExhausted() throws IOException {
		Parameters parameters = new Parameters();
		parameters.setMaxDepth(2);
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor(parameters).run(
				problemWithoutDependencyPairs("f(X) -> g(X)"), null, 0, context);

		assertTrue(result.isFailed());
		assertEquals(0, context.getGeneratedRules());
		assertTrue(result.getProof().toString().contains(
				"Could not prove infiniteness!"));
	}

	@Test
	@DisplayName("preserve interruption before rule unfolding")
	void preserveInterruptionBeforeRuleUnfolding() throws IOException {
		Parameters parameters = new Parameters();
		AnalysisContext context = context();
		DependencyPairProblem problem = problemFor("f(X) -> f(X)");
		Thread.currentThread().interrupt();
		try {
			DependencyPairProcessorResult result = newProcessor(parameters).run(
					problem, null, 0, context);

			assertTrue(result.isFailed());
			assertEquals(0, context.getGeneratedRules());
			assertTrue(Thread.currentThread().isInterrupted());
			assertEquals(-1, parameters.getMaxDepth());
		}
		finally {
			Thread.interrupted();
		}
	}

	@Test
	@DisplayName("ignore argument filtering during rule unfolding")
	void ignoreArgumentFilteringDuringRuleUnfolding() throws IOException {
		PayetRuleUnfoldingDependencyPairProcessor processor =
				newProcessor(new Parameters());
		DependencyPairProcessorResult result = processor.run(
				problemFor("f(X) -> f(X)"), new ArgFiltering(), 0, context());

		assertFalse(processor.usesFiltering());
		assertTrue(result.isInfinite());
	}

	@Test
	@DisplayName("restore unlimited maximum depth after analysis")
	void restoreUnlimitedMaximumDepthAfterAnalysis() throws IOException {
		Parameters parameters = new Parameters();

		DependencyPairProcessorResult result = newProcessor(parameters).run(
				problemFor("f(X) -> f(X)"), null, 0, context());

		assertTrue(result.isInfinite());
		assertEquals(-1, parameters.getMaxDepth());
	}

	@Test
	@DisplayName("restore disabled variable unfolding after fallback attempt")
	void restoreDisabledVariableUnfoldingAfterFallbackAttempt() throws IOException {
		Parameters parameters = new Parameters();
		parameters.setMaxDepth(2);

		DependencyPairProcessorResult result = newProcessor(parameters).run(
				problemWithoutDependencyPairs("f(X) -> g(X)"), null, 0, context());

		assertTrue(result.isFailed());
		assertFalse(parameters.isVariableUnfoldingEnabled());
		assertTrue(result.getProof().toString().contains(
				"unfold_variables=false"));
		assertTrue(result.getProof().toString().contains(
				"unfold_variables=true"));
	}

	@Test
	@DisplayName("share the unfolding-rule budget across maximum-depth attempts")
	void shareRuleBudgetAcrossMaximumDepthAttempts() throws IOException {
		Parameters parameters = new Parameters();
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor(parameters).run(
				problemFor("a(a(delta,X),Y) -> a(Y,a(X,Y))"),
				null, 0, context);

		assertTrue(result.isFailed());
		assertTrue(context.getGeneratedRules() >= 10_000,
				() -> "generated rules: " + context.getGeneratedRules());
		assertTrue(result.getProof().toString().contains(
				"Too many unfolded rules ("));
		assertEquals(-1, parameters.getMaxDepth());
	}

	@Test
	@DisplayName("retain the iteration-six loop for test77")
	void retainIterationSixLoopForTest77() throws IOException {
		Parameters parameters = new Parameters();
		parameters.setStrategy(StrategyLoop.ALL);
		AnalysisContext context = context();
		DependencyPairProcessorResult result = newProcessor(parameters).run(
				problemFor(
						"plus(X,zero) -> X",
						"plus(X,s(Y)) -> s(plus(X,Y))",
						"double(X) -> plus(X,X)",
						"f(zero,s(zero),X) -> f(X,double(X),X)",
						"g(X,Y) -> X",
						"g(X,Y) -> Y"),
				null, 0, context);

		assertTrue(result.isInfinite());
		assertTrue(result.getProof().toString().contains(
				"[iteration = 6] f^#(g(zero,_0)," +
						"plus(g(_1,s(zero)),g(zero,_2)),_3)"));
		assertEquals(13_743, context.getGeneratedRules());
		assertEquals(-1, parameters.getMaxDepth());
	}

	@Test
	@DisplayName("copy the processor parameters independently")
	void copyProcessorParametersIndependently() {
		Parameters parameters = new Parameters();
		PayetRuleUnfoldingDependencyPairProcessor processor =
				newProcessor(parameters);
		DependencyPairProcessor copy = processor.copy();
		String copiedDescription = copy.toString();

		parameters.setMaxDepth(0);

		assertNotSame(processor, copy);
		assertFalse(processor.toString().equals(copiedDescription));
		assertEquals(copiedDescription, copy.toString());
	}

	private static PayetRuleUnfoldingDependencyPairProcessor newProcessor(
			Parameters parameters) {

		return new PayetRuleUnfoldingDependencyPairProcessor(parameters);
	}

	private static DependencyPairProblem problemFor(String... ruleTexts)
			throws IOException {

		Trs trs = parseTrs(ruleTexts);
		return new InitialDependencyPairProblemCollector()
				.collectFrom(trs).iterator().next();
	}

	private static DependencyPairProblem problemWithoutDependencyPairs(
			String ruleText) throws IOException {

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
