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
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.ForwardInstantiationDependencyPairProcessor;
import fr.univreunion.nti.term.Variable;

class ForwardInstantiationDependencyPairProcessorTest {

	@Test
	@DisplayName("prove the canonical forward-instantiation example finite")
	void proveCanonicalExampleFinite() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(X,Y,Z) -> g(X,Y,Z)",
				"g(0,1,X) -> f(X,X,X)"));

		assertTrue(result.isFinite(), result.getProof().toString());
		assertTrue(result.getProof().toString().contains(
				"Forward-instantiated dependency pair"));
		assertTrue(result.getProof().toString().contains(
				"cyclic dependency pairs from 2 to 0"));
	}

	@Test
	@DisplayName("also handle an example with unrelated rewrite rules")
	void ignoreUnrelatedRules() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(X,Y,Z) -> g(X,Y,Z)",
				"g(0,1,X) -> f(X,X,X)",
				"a -> b",
				"a -> c"));

		assertTrue(result.isFinite(), result.getProof().toString());
	}

	@Test
	@DisplayName("decompose when another cyclic component remains")
	void decomposeAroundRemainingComponent() throws IOException {
		Trs trs = parseTrs(
				"f(X,Y,Z) -> g(X,Y,Z)",
				"g(0,1,X) -> f(X,X,X)",
				"q(X) -> q(X)");
		List<RuleTrs> pairs = new ArrayList<>();
		for (DependencyPairProblem initialProblem :
				new InitialDependencyPairProblemCollector().collectFrom(trs))
			for (RuleTrs pair : initialProblem.getDependencyPairs())
				pairs.add(pair);

		DependencyPairProcessorResult result = runProcessor(
				new DependencyPairProblem(trs, new DependencyPairs(pairs)));

		assertTrue(result.isDecomposed(), result.getProof().toString());
		assertEquals(1, result.getSubproblems().size());
		assertEquals(1,
				result.getSubproblems().iterator().next().nbDependencyPairs());
	}

	@Test
	@DisplayName("reject a forward instantiation that does not shrink cycles")
	void rejectNonShrinkingInstantiation() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(X) -> f(X)"));

		assertTrue(result.isFailed());
	}

	@Test
	@DisplayName("treat a collapsing TRS inverse cap as one fresh variable")
	void collapsingRulePreventsCanonicalSpecialization() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(X,Y,Z) -> g(X,Y,Z)",
				"g(0,1,X) -> f(X,X,X)",
				"h(X) -> X"));

		assertTrue(result.isFailed());
	}

	@Test
	@DisplayName("leave generalized TRSs unchanged")
	void rejectGeneralizedTrs() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(X,Y,Z) -> g(X,Y,Z)",
				"g(0,1,X) -> f(X,X,X)",
				"a -> h(X)"));

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains("generalized TRS"));
	}

	@Test
	@DisplayName("bound the number of dependency pairs")
	void boundNumberOfDependencyPairs() throws IOException {
		String[] rules = new String[65];
		for (int index = 0; index < rules.length; index++)
			rules[index] = "f" + index + "(X) -> f" +
					((index + 1) % rules.length) + "(X)";

		DependencyPairProcessorResult result = runProcessor(problemFor(rules));

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains("size bounds"));
	}

	@Test
	@DisplayName("honor an existing interruption")
	void honorInterruption() throws IOException {
		DependencyPairProblem problem = problemFor(
				"f(X,Y,Z) -> g(X,Y,Z)",
				"g(0,1,X) -> f(X,X,X)");
		Thread.currentThread().interrupt();
		try {
			DependencyPairProcessorResult result = runProcessor(problem);

			assertTrue(result.isFailed());
			assertTrue(Thread.currentThread().isInterrupted());
		}
		finally {
			assertTrue(Thread.interrupted());
		}
	}

	private static DependencyPairProcessorResult runProcessor(
			DependencyPairProblem problem) {

		return new ForwardInstantiationDependencyPairProcessor().run(
				problem, null, 0, new AnalysisContext(true, null));
	}

	private static DependencyPairProblem problemFor(String... ruleTexts)
			throws IOException {

		return new InitialDependencyPairProblemCollector()
				.collectFrom(parseTrs(ruleTexts)).iterator().next();
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
