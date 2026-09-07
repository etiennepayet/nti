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
import static org.junit.jupiter.api.Assertions.assertFalse;
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
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.SubtermCriterionDependencyPairProcessor;
import fr.univreunion.nti.term.Variable;

class SubtermCriterionDependencyPairProcessorTest {

	@Test
	@DisplayName("prove finiteness with a strict simple projection")
	void proveFinitenessWithStrictSimpleProjection() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(g(g(X)),Y) -> f(g(X),k(Y))"));

		assertTrue(result.isFinite());
		assertTrue(result.getProof().toString().contains(
				"Simple projection: {f^# -> 1}"));
	}

	@Test
	@DisplayName("find compatible projections for distinct dependency-pair roots")
	void findCompatibleProjectionsForDistinctRoots() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(s(X),Y) -> g(X,h(Y))",
				"g(s(X),Y) -> f(X,k(Y))"));

		assertTrue(result.isFinite());
		assertTrue(result.getProof().toString().contains("f^# -> 1"));
		assertTrue(result.getProof().toString().contains("g^# -> 1"));
	}

	@Test
	@DisplayName("decompose when only some projected pairs are strict")
	void decomposeWhenOnlySomeProjectedPairsAreStrict() throws IOException {
		Trs trs = parseTrs(
				"f(g(g(X)),Y) -> f(g(X),k(Y))",
				"q(X,Y) -> q(X,k(Y))");
		DependencyPairProcessorResult result = runProcessor(
				problemContainingAllDependencyPairs(trs));

		assertTrue(result.isDecomposed());
		assertEquals(1, result.getSubproblems().size());
		assertEquals(1,
				result.getSubproblems().iterator().next().nbDependencyPairs());
	}

	@Test
	@DisplayName("fail when every projection grows")
	void failWhenEveryProjectionGrows() throws IOException {
		DependencyPairProcessorResult result = runProcessor(problemFor(
				"f(X) -> f(s(X))"));

		assertTrue(result.isFailed());
	}

	@Test
	@DisplayName("bound the number of simple projections")
	void boundNumberOfSimpleProjections() throws IOException {
		String[] rules = new String[16];
		for (int index = 0; index < rules.length; index++)
			rules[index] = "f" + index + "(X,Y) -> f" +
					((index + 1) % rules.length) + "(X,Y)";

		DependencyPairProcessorResult result = runProcessor(problemFor(rules));

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains(
				"Too many simple projections"));
	}

	@Test
	@DisplayName("ignore argument filtering")
	void ignoreArgumentFiltering() throws IOException {
		SubtermCriterionDependencyPairProcessor processor =
				new SubtermCriterionDependencyPairProcessor();
		DependencyPairProcessorResult result = processor.run(
				problemFor("f(s(X),Y) -> f(X,h(Y))"),
				new ArgFiltering(), 0, context());

		assertFalse(processor.usesFiltering());
		assertTrue(result.isFinite());
	}

	private static DependencyPairProcessorResult runProcessor(
			DependencyPairProblem problem) {

		return new SubtermCriterionDependencyPairProcessor().run(
				problem, null, 0, context());
	}

	private static DependencyPairProblem problemFor(String... ruleTexts)
			throws IOException {

		return new InitialDependencyPairProblemCollector()
				.collectFrom(parseTrs(ruleTexts)).iterator().next();
	}

	private static DependencyPairProblem problemContainingAllDependencyPairs(
			Trs trs) {

		DependencyPairProblemCollection initialProblems =
				new InitialDependencyPairProblemCollector().collectFrom(trs);
		List<RuleTrs> dependencyPairs = new ArrayList<>();
		for (DependencyPairProblem problem : initialProblems)
			for (RuleTrs dependencyPair : problem.getDependencyPairs())
				dependencyPairs.add(dependencyPair);
		return new DependencyPairProblem(
				trs, new DependencyPairs(dependencyPairs));
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
