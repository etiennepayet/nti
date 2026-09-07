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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.LpoDependencyPairProcessor;
import fr.univreunion.nti.term.Variable;

class LpoDependencyPairProcessorTest {

	@Test
	@DisplayName("reject a dependency pair problem with too many symbols")
	void rejectProblemWithTooManySymbols() throws IOException {
		String term = "f(a0,a1,a2,a3,a4,a5,a6,a7,a8,a9," +
				"a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20)";
		DependencyPairProcessorResult result = runProcessor(
				parseTrs(term + " -> " + term));

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains(
				"symbols to deal with)! Aborting!"));
	}

	@Test
	@DisplayName("prove a decreasing recursive dependency pair finite")
	void proveDecreasingRecursiveProblemFinite() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				parseTrs("f(s(X)) -> f(X)"));

		assertTrue(result.isFinite());
		assertTrue(result.getProof().toString().contains(
				"Lexicographic path order induced by the precedence:"));
	}

	@Test
	@DisplayName("fail when no lexicographic path order orients the dependency pair strictly")
	void failWhenNoLexicographicPathOrderIsSuitable() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				parseTrs("f(X) -> f(X)"));

		assertTrue(result.isFailed());
	}

	@Test
	@DisplayName("decompose a problem when only some dependency pairs are strict")
	void decomposeProblemWhenOnlySomeDependencyPairsAreStrict() throws IOException {
		Trs trs = parseTrs(
				"f(s(X)) -> f(X)",
				"g(X) -> g(X)");
		DependencyPairProcessorResult result = runProcessor(
				problemContainingAllDependencyPairs(trs));

		assertTrue(result.isDecomposed());
		assertEquals(1, result.getSubproblems().size());
		assertEquals(1, result.getSubproblems().iterator().next().nbDependencyPairs());
		assertTrue(result.getProof().toString().contains(
				"Lexicographic path order induced by the precedence:"));
	}

	@Test
	@DisplayName("compute the transitive usable-rule closure in source order")
	void computeTransitiveUsableRuleClosureInSourceOrder() throws IOException {
		DependencyPairProcessorResult result = runProcessor(parseTrs(
				"f(s(X)) -> f(h(X))",
				"k(a) -> b",
				"u(a) -> c",
				"h(X) -> k(X)"));

		assertTrue(result.isFinite());
		String proof = result.getProof().toString();
		int firstUsableRule = proof.indexOf("k(a) -> b");
		int secondUsableRule = proof.indexOf("h(_0) -> k(_0)");
		assertTrue(0 <= firstUsableRule);
		assertTrue(firstUsableRule < secondUsableRule);
		assertFalse(proof.contains("u(a) -> c"));
	}

	@Test
	@DisplayName("apply argument filtering to usable rules")
	void applyArgumentFilteringToUsableRules() throws IOException {
		Trs trs = parseTrs(
				"f(s(X),Y) -> f(h(X),Y)",
				"h(X) -> k(X)",
				"k(a) -> b",
				"u(a) -> u(b)",
				"u(b) -> u(a)");
		DependencyPairProcessorResult result = runFilteredProcessor(trs);

		assertTrue(result.isFinite(), result.getProof().toString());
		String proof = result.getProof().toString();
		assertTrue(proof.contains("Using argument filtering"));
		assertTrue(proof.contains("Using usable rules:"));
		assertFalse(proof.contains("u(a) -> u(b)"));
		assertFalse(proof.contains("u(b) -> u(a)"));
	}

	@Test
	@DisplayName("reject usable rules for a generalized TRS")
	void rejectUsableRulesForGeneralizedTrs() throws IOException {
		DependencyPairProcessorResult result = runProcessor(parseTrs(
				"f(s(X)) -> f(X)",
				"g(a) -> Y"));

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains(
				"Usable rules are not applied to a generalized TRS."));
	}

	private static DependencyPairProcessorResult runProcessor(Trs trs) {
		DependencyPairProblem problem = new InitialDependencyPairProblemCollector()
				.collectFrom(trs).iterator().next();
		return runProcessor(problem);
	}

	private static DependencyPairProcessorResult runProcessor(DependencyPairProblem problem) {
		LpoDependencyPairProcessor processor = new LpoDependencyPairProcessor(false);
		return processor.run(problem, null, 0, context());
	}

	private static DependencyPairProcessorResult runFilteredProcessor(Trs trs) {
		DependencyPairProblem problem = problemForRoot(trs, "f");
		ArgFiltering filtering = buildFiltering(trs, problem);
		LpoDependencyPairProcessor processor = new LpoDependencyPairProcessor(true);
		return processor.run(problem, filtering, 0, context());
	}

	private static DependencyPairProblem problemForRoot(Trs trs, String root) {
		for (DependencyPairProblem problem :
				new InitialDependencyPairProblemCollector().collectFrom(trs))
			if (root.equals(problem.getDependencyPairs().iterator().next()
					.getLeft().getRootSymbol().getName()))
				return problem;
		throw new IllegalArgumentException("no dependency pair for " + root);
	}

	private static ArgFiltering buildFiltering(
			Trs trs, DependencyPairProblem problem) {
		ArgFiltering filtering = new ArgFiltering();
		for (RuleTrs rule : trs) {
			rule.getLeft().buildFilters(filtering);
			rule.getRight().buildFilters(filtering);
		}
		for (RuleTrs pair : problem.getDependencyPairs()) {
			pair.getLeft().buildFilters(filtering);
			pair.getRight().buildFilters(filtering);
		}
		return filtering;
	}

	private static DependencyPairProblem problemContainingAllDependencyPairs(Trs trs) {
		DependencyPairProblemCollection initialProblems =
				new InitialDependencyPairProblemCollector().collectFrom(trs);
		List<RuleTrs> dependencyPairs = new ArrayList<>();
		for (DependencyPairProblem problem : initialProblems)
			for (RuleTrs dependencyPair : problem.getDependencyPairs())
				dependencyPairs.add(dependencyPair);
		return new DependencyPairProblem(trs, new DependencyPairs(dependencyPairs));
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
