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

package fr.univreunion.nti.program.lp.patternunfolding;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
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
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.ModeNonTerminationTracker;
import fr.univreunion.nti.program.lp.ResultLp;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.term.Variable;

class LpPatternUnfolderTest {

	@Test
	@DisplayName("accumulate pattern rules between iterations in generation order")
	void accumulatePatternRulesBetweenIterationsInGenerationOrder()
			throws IOException, InterruptedException {

		LpPatternUnfolder unfolder = new LpPatternUnfolder(chainRules());

		List<PatternRuleLp> firstIteration = unfolder.unfoldNext(1);
		List<PatternRuleLp> secondIteration = unfolder.unfoldNext(2);

		assertEquals(List.of(
				"p(_0) :- q(_0)",
				"q(_0) :- r(_0)",
				"q(a) :- e*"), representationsOf(firstIteration));
		assertEquals(List.of(
				"p(_0) :- r(_0)",
				"p(a) :- e*"), representationsOf(secondIteration));
	}

	@Test
	@DisplayName("preserve insertion order inside predicate buckets")
	void preserveInsertionOrderInsidePredicateBuckets() throws IOException {
		PatternRuleLp firstQRule = patternRule(
				"q(X){}{}", "a(X){}{}");
		PatternRuleLp rRule = patternRule(
				"r(X){}{}", "c(X){}{}");
		PatternRuleLp secondQRule = patternRule(
				"q(X){}{}", "b(X){}{}");
		PatternUnfoldingRuleIndex index = new PatternUnfoldingRuleIndex();
		index.addAll(List.of(firstQRule, rRule, secondQRule));

		RuleLp qSource = parseRule("p(X) :- q(X).");
		RuleLp sSource = parseRule("p(X) :- s(X).");

		assertEquals(
				List.of(firstQRule, secondQRule),
				index.candidatesFor(qSource.getBody(0)));
		assertTrue(index.candidatesFor(sSource.getBody(0)).isEmpty());
	}

	@Test
	@DisplayName("stop pattern unfolding when interrupted")
	void stopPatternUnfoldingWhenInterrupted() throws IOException {
		LpPatternUnfolder unfolder = new LpPatternUnfolder(chainRules());

		Thread.currentThread().interrupt();
		try {
			assertThrows(InterruptedException.class, () -> unfolder.unfoldNext(1));
		}
		finally {
			Thread.interrupted();
		}
	}

	@Test
	@DisplayName("stop the proof after the first empty iteration")
	void stopProofAfterFirstEmptyIteration() throws IOException {
		List<RuleLp> rules = chainRules();
		AnalysisContext context = new AnalysisContext(true, null);
		Mode mode = new Mode(rules.getFirst().getHead().getRootSymbol(), List.of(0));

		ResultLp result = new LpPatternNonTerminationProver(rules).prove(
				context, new ModeNonTerminationTracker(mode));

		assertTrue(result.isMAYBE());
		assertEquals(5, context.getGeneratedRules());
		assertTrue(result.getProof().toString().contains(
				"Iteration = 3: 0 new unfolded rule(s) generated\n, aborting!"));
	}

	@Test
	@DisplayName("complete a proof from a generated pattern witness")
	void completeProofFromGeneratedPatternWitness() throws IOException {
		ParserString parser = new ParserString();
		RuleLp rule = parser.parseLpRule(
				"p(X) :- p(s(X)).", new HashMap<>());
		AnalysisContext context = new AnalysisContext(true, null);
		Mode mode = new Mode(rule.getHead().getRootSymbol(), List.of());

		ResultLp result = new LpPatternNonTerminationProver(List.of(rule)).prove(
				context, new ModeNonTerminationTracker(mode));

		assertTrue(result.isNO());
		assertEquals(2, context.getGeneratedRules());
		assertEquals("Mode p(o): the query p(0) is non-terminating "
				+ "(extracted from a LP pattern rule [Payet, ICLP'25])",
				result.getProof().getArgument().toString());
	}

	@Test
	@DisplayName("process logic-program rules containing Prolog lists")
	void processLogicProgramRulesContainingPrologLists() throws IOException {
		List<RuleLp> rules = reverseRules();

		assertDoesNotThrow(() -> {
			LpPatternUnfolder unfolder = new LpPatternUnfolder(rules);
			unfolder.unfoldNext(1);
		});
	}

	private static List<RuleLp> chainRules() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleLp> rules = new ArrayList<>();
		rules.add(parser.parseLpRule("p(X) :- q(X).", variables));
		rules.add(parser.parseLpRule("q(X) :- r(X).", variables));
		rules.add(parser.parseLpRule("r(a).", variables));
		return rules;
	}

	private static List<RuleLp> reverseRules() throws IOException {
		ParserString parser = new ParserString();
		List<RuleLp> rules = new ArrayList<>();
		rules.add(parser.parseLpRule(
				"rev([],R,R).", new HashMap<>()));
		rules.add(parser.parseLpRule(
				"rev([X|Xs],R0,R) :- rev(Xs,[X|R0],R).",
				new HashMap<>()));
		rules.add(parser.parseLpRule(
				"reverse(L,R) :- rev(L,[],R).", new HashMap<>()));
		return rules;
	}

	private static RuleLp parseRule(String text) throws IOException {
		return new ParserString().parseLpRule(text, new HashMap<>());
	}

	private static PatternRuleLp patternRule(
			String left,
			String right) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		return PatternRuleLp.tryBuild(
				parser.parseSimplePatternTerm(left, variables),
				parser.parseSimplePatternTerm(right, variables),
				0);
	}

	private static List<String> representationsOf(List<PatternRuleLp> rules) {
		return rules.stream().map(Object::toString).toList();
	}
}
