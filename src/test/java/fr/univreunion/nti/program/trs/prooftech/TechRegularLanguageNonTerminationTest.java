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

package fr.univreunion.nti.program.trs.prooftech;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Variable;

class TechRegularLanguageNonTerminationTest {

	@Test
	@DisplayName("synthesize and independently verify the S-rule automaton")
	void proveSRule() throws IOException {
		Proof proof = new TechRegularLanguageNonTermination().run(parseTrs(
				"a(a(a(s,X),Y),Z) -> a(a(X,Z),a(Y,Z))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("regular tree language",
				proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains("States: 0..4"));
		assertTrue(proof.getArgument().toString().contains(
				"All three obligations were checked independently"));
		assertTrue(proof.toString().contains(
				"Found and independently verified"));
	}

	@Test
	@DisplayName("apply the generic automaton technique to the Owl rule")
	void proveOwlRuleGenerically() throws IOException {
		Proof proof = new TechRegularLanguageNonTermination().run(parseTrs(
				"a(a(delta,X),Y) -> a(Y,a(X,Y))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("regular tree language",
				proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains("States: 0..2"));
	}

	@Test
	@DisplayName("reject a terminating duplicating rule")
	void rejectTerminatingDuplicatingRule() throws IOException {
		Proof proof = new TechRegularLanguageNonTermination().run(parseTrs(
				"f(a,X) -> g(X,X)"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
		assertTrue(proof.toString().contains(
				"No regular-language nontermination certificate found!"));
	}

	@Test
	@DisplayName("reject a certificate whose accepted term is a normal form")
	void rejectAutomatonAcceptingNormalForm() throws IOException {
		Trs trs = parseTrs("f(a,X) -> g(X,X)");
		var a = fr.univreunion.nti.term.FunctionSymbol.get("a", 0);
		FiniteTreeAutomaton candidate = new FiniteTreeAutomaton(
				1, java.util.Set.of(0), List.of(
						new FiniteTreeAutomaton.Transition(a, List.of(), 0)));
		NormalFormAutomaton normalForms = NormalFormAutomaton.build(
				trs, List.of(
						fr.univreunion.nti.term.FunctionSymbol.get("a", 0),
						fr.univreunion.nti.term.FunctionSymbol.get("f", 2),
						fr.univreunion.nti.term.FunctionSymbol.get("g", 2)),
				64, 4_096);

		RegularLanguageCertificateVerifier.Verification verification =
				new RegularLanguageCertificateVerifier().verify(
						trs, candidate, normalForms);

		assertFalse(verification.valid());
		assertTrue(verification.failure().contains("normal form"));
	}

	@Test
	@DisplayName("stop before SAT when the thread is interrupted")
	void observeInterruption() throws IOException {
		Thread.currentThread().interrupt();
		try {
			Proof proof = new TechRegularLanguageNonTermination().run(parseTrs(
					"a(a(a(s,X),Y),Z) -> a(a(X,Z),a(Y,Z))"), context());
			assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
			assertFalse(proof.isSuccess());
		}
		finally {
			assertTrue(Thread.interrupted());
		}
	}

	@Test
	@DisplayName("do not pass an oversized encoding to the SAT solver")
	void rejectOversizedEncodingBeforeSat() throws IOException {
		Trs trs = parseTrs(
				"a(a(a(s,X),Y),Z) -> a(a(X,Z),a(Y,Z))");
		var a = fr.univreunion.nti.term.FunctionSymbol.get("a", 2);
		var s = fr.univreunion.nti.term.FunctionSymbol.get("s", 0);
		List<fr.univreunion.nti.term.FunctionSymbol> alphabet = List.of(a, s);
		NormalFormAutomaton normalForms = NormalFormAutomaton.build(
				trs, alphabet, 64, 4_096);
		AtomicInteger solverCalls = new AtomicInteger();
		SatSolver solver = (formula, timeout) -> {
			solverCalls.incrementAndGet();
			return SatSolver.SatResult.unsatisfiable();
		};

		RegularLanguageAutomatonSearch.SearchResult result =
				new RegularLanguageAutomatonSearch(
						solver, 5, 5, 20, 1_000)
						.search(trs, alphabet, normalForms);

		assertTrue(result.aborted());
		assertEquals(0, solverCalls.get());
	}

	@Test
	@DisplayName("prove the S-rule before dependency-pair analysis")
	void runBeforeDependencyPairs() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"a(a(a(s,X),Y),Z) -> a(a(X,Z),a(Y,Z))"), analysis)
				.prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("regular tree language",
				proof.getArgument().getWitnessKind());
	}

	private static AnalysisContext context() {
		return new AnalysisContext(true, null);
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new LinkedList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return new Trs("", rules, "FULL");
	}
}
