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
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.PolynomialInterpretationDependencyPairProcessor;
import fr.univreunion.nti.term.Variable;

class PolynomialInterpretationDependencyPairProcessorTest {

	@Test
	@DisplayName("reject a dependency pair problem whose rules are too deep")
	void rejectProblemWhoseRulesAreTooDeep() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				parseTrs("f(X) -> f(X)"), 100, 0);

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains(
				"This DP problem is too complex! Aborting!"));
	}

	@Test
	@DisplayName("reject a dependency pair problem whose symbols have excessive arity")
	void rejectProblemWhoseSymbolsHaveExcessiveArity() throws IOException {
		DependencyPairProcessorResult result = runProcessor(parseTrs(
				"f(X1,X2,X3,X4,X5,X6,X7) -> f(X1,X2,X3,X4,X5,X6,X7)"),
				100, 10);

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains(
				"This DP problem is too complex! Aborting!"));
	}

	@Test
	@DisplayName("reject a dependency pair problem with too many coefficients")
	void rejectProblemWithTooManyCoefficients() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				parseTrs("f(X) -> f(X)"), 0, 10);

		assertTrue(result.isFailed());
		assertTrue(result.getProof().toString().contains(
				"coefficients to instantiate)! Aborting!"));
	}

	@Test
	@DisplayName("prove a decreasing recursive dependency pair finite")
	void proveDecreasingRecursiveProblemFinite() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				parseTrs("f(s(X)) -> f(X)"), 100, 10);

		assertTrue(result.isFinite());
		assertTrue(result.getProof().toString().contains(
				"Polynomial order induced by the interpretation:"));
	}

	@Test
	@DisplayName("prove a decreasing recursive problem containing a constant finite")
	void proveDecreasingRecursiveProblemContainingConstantFinite() throws IOException {
		DependencyPairProcessorResult result = runProcessor(parseTrs(
				"f(s(X)) -> f(X)",
				"h(a) -> a"), 100, 10);

		assertTrue(result.isFinite());
		assertTrue(result.getProof().toString().contains(
				"Polynomial order induced by the interpretation:"));
	}

	@Test
	@DisplayName("fail when no polynomial interpretation orients the dependency pair strictly")
	void failWhenNoPolynomialInterpretationIsSuitable() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				parseTrs("f(X) -> f(X)"), 100, 10);

		assertTrue(result.isFailed());
	}

	@Test
	@DisplayName("decompose a problem when only some dependency pairs are strict")
	void decomposeProblemWhenOnlySomeDependencyPairsAreStrict() throws IOException {
		Trs trs = parseTrs(
				"f(s(X)) -> f(X)",
				"g(X) -> g(X)");
		DependencyPairProcessorResult result = runProcessor(
				problemContainingAllDependencyPairs(trs), 100, 10);

		assertTrue(result.isDecomposed());
		assertEquals(1, result.getSubproblems().size());
		assertEquals(1, result.getSubproblems().iterator().next().nbDependencyPairs());
		assertTrue(result.getProof().toString().contains(
				"Polynomial order induced by the interpretation:"));
	}

	@Test
	@DisplayName("restrict an unfiltered polynomial search to usable rules")
	void restrictUnfilteredSearchToUsableRules() throws IOException {
		DependencyPairProcessorResult result = runProcessor(parseTrs(
				"f(s(X)) -> f(X)",
				"u(a) -> b"), 2, 10);

		assertTrue(result.isFinite(), result.getProof().toString());
		String proof = result.getProof().toString();
		assertTrue(proof.contains("Using usable rules: []"));
		assertFalse(proof.contains("u(a) -> b"));
	}

	@Test
	@DisplayName("apply argument filtering to usable rules before polynomial search")
	void applyArgumentFilteringToUsableRules() throws IOException {
		Trs trs = parseTrs(
				"f(s(X),Y) -> f(X,Y)",
				"u(a) -> u(b)",
				"u(b) -> u(a)");
		DependencyPairProcessorResult result =
				runFilteredProcessor(trs, 2, 10);

		assertTrue(result.isFinite(), result.getProof().toString());
		String proof = result.getProof().toString();
		assertTrue(proof.contains("Using argument filtering:"));
		assertTrue(proof.contains("Using usable rules: []"));
		assertFalse(proof.contains("u(a) -> u(b)"));
		assertFalse(proof.contains("u(b) -> u(a)"));
	}

	private static DependencyPairProcessorResult runProcessor(
			Trs trs, int maxCoefficientCount, int maxDepth) {

		DependencyPairProblem problem = new InitialDependencyPairProblemCollector()
				.collectFrom(trs).iterator().next();
		return runProcessor(problem, maxCoefficientCount, maxDepth);
	}

	private static DependencyPairProcessorResult runProcessor(
			DependencyPairProblem problem, int maxCoefficientCount, int maxDepth) {

		PolynomialInterpretationDependencyPairProcessor processor =
				new PolynomialInterpretationDependencyPairProcessor(
						false, maxCoefficientCount, maxDepth);
		return processor.run(problem, null, 0, context());
	}

	private static DependencyPairProcessorResult runFilteredProcessor(
			Trs trs, int maxCoefficientCount, int maxDepth) {
		DependencyPairProblem problem = problemForRoot(trs, "f");
		ArgFiltering filtering = buildFiltering(trs, problem);
		PolynomialInterpretationDependencyPairProcessor processor =
				new PolynomialInterpretationDependencyPairProcessor(
						true, maxCoefficientCount, maxDepth);
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
