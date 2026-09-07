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
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.HomeomorphicEmbeddingDependencyPairProcessor;
import fr.univreunion.nti.term.Variable;

class HomeomorphicEmbeddingDependencyPairProcessorTest {

	@Test
	@DisplayName("prove finiteness when every left-hand side embeds its right-hand side")
	void proveFinitenessWhenEveryLeftHandSideEmbedsRightHandSide() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				problemFor("f(s(X)) -> f(X)"), null);

		assertTrue(result.isFinite());
	}

	@Test
	@DisplayName("fail when a dependency pair has deeply equal sides")
	void failWhenDependencyPairHasDeeplyEqualSides() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				problemFor("f(X) -> f(X)"), null);

		assertTrue(result.isFailed());
	}

	@Test
	@DisplayName("fail when a left-hand side does not embed its right-hand side")
	void failWhenLeftHandSideDoesNotEmbedRightHandSide() throws IOException {
		DependencyPairProcessorResult result = runProcessor(
				problemFor("f(X) -> f(s(X))"), null);

		assertTrue(result.isFailed());
	}

	@Test
	@DisplayName("ignore argument filtering when checking embeddings")
	void ignoreArgumentFilteringWhenCheckingEmbeddings() throws IOException {
		DependencyPairProblem problem = problemFor("f(s(X)) -> f(X)");
		HomeomorphicEmbeddingDependencyPairProcessor processor =
				new HomeomorphicEmbeddingDependencyPairProcessor();

		DependencyPairProcessorResult result = processor.run(
				problem, new ArgFiltering(), 0, context());

		assertFalse(processor.usesFiltering());
		assertTrue(result.isFinite());
	}

	private static DependencyPairProcessorResult runProcessor(
			DependencyPairProblem problem, ArgFiltering filtering) {

		return new HomeomorphicEmbeddingDependencyPairProcessor().run(
				problem, filtering, 0, context());
	}

	private static DependencyPairProblem problemFor(String ruleText) throws IOException {
		Trs trs = parseTrs(ruleText);
		return new InitialDependencyPairProblemCollector()
				.collectFrom(trs).iterator().next();
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
