/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Variable;

class DependencyPairAnalysisTest {

	@Test
	@DisplayName("append the attempt summary after the selected proof")
	void appendAttemptSummaryAfterSelectedProof() {
		AnalysisContext context = context(true);
		Proof selectedProof = successfulProof(context, "decisive proof trace");
		DependencyPairFrameworkAttempt attempt =
				new DependencyPairFrameworkAttempt(
						"Selected variant", () -> selectedProof);
		Proof diagnosticProof = context.createProof();

		Proof result = analysis(List.of(attempt)).prove(
				context, diagnosticProof);

		assertSame(selectedProof, result);
		String description = result.toString();
		assertTrue(description.indexOf("decisive proof trace")
				< description.indexOf("* Concurrent TRS proof attempts:"));
		assertTrue(description.contains(
				"  - Selected variant: successful (NO)"));
		assertFalse(diagnosticProof.toString().contains(
				"Concurrent TRS proof attempts"));
	}

	@Test
	@DisplayName("append the attempt summary to diagnostics when no proof exists")
	void appendAttemptSummaryToDiagnosticsWhenNoProofExists() {
		AnalysisContext context = context(true);
		DependencyPairFrameworkAttempt attempt =
				new DependencyPairFrameworkAttempt("Broken variant", () -> {
					throw new IllegalStateException("variant failure");
				});
		Proof diagnosticProof = context.createProof();

		Proof result = analysis(List.of(attempt)).prove(
				context, diagnosticProof);

		assertNull(result);
		assertTrue(diagnosticProof.toString().contains(
				"* Concurrent TRS proof attempts:\n"
				+ "  - Broken variant: error"));
	}

	@Test
	@DisplayName("omit the attempt summary from non-verbose proofs")
	void omitAttemptSummaryFromNonVerboseProofs() {
		AnalysisContext context = context(false);
		Proof selectedProof = successfulProof(context, "");
		DependencyPairFrameworkAttempt attempt =
				new DependencyPairFrameworkAttempt(
						"Selected variant", () -> selectedProof);
		Proof diagnosticProof = context.createProof();

		Proof result = analysis(List.of(attempt)).prove(
				context, diagnosticProof);

		assertSame(selectedProof, result);
		assertFalse(result.toString().contains("Concurrent TRS proof attempts"));
		assertFalse(diagnosticProof.toString().contains(
				"Concurrent TRS proof attempts"));
	}

	@Test
	@DisplayName("bound the original dependency graph before building variants")
	void boundOriginalDependencyGraphBeforeBuildingVariants()
			throws IOException {
		Trs trs = new Trs(
				"dense.trs", parseDenseSelfLoops(317), "FULL");
		AtomicBoolean factoryCalled = new AtomicBoolean();
		DependencyPairAnalysis analysis = new DependencyPairAnalysis(
				trs, (ignoredTrs, context) -> {
					factoryCalled.set(true);
					return List.of();
				});
		AnalysisContext context = context(true);
		Proof diagnosticProof = context.createProof();

		Proof result = analysis.prove(context, diagnosticProof);

		assertNull(result);
		assertFalse(factoryCalled.get());
		assertTrue(diagnosticProof.toString().contains(
				"Dependency pair analysis stopped: Dependency graph "
				+ "construction exceeded 100000 approximate arcs"));
	}

	private static DependencyPairAnalysis analysis(
			List<DependencyPairFrameworkAttempt> attempts) {

		Trs trs = new Trs("analysis.trs", new LinkedList<>(), "FULL");
		return new DependencyPairAnalysis(trs, (ignoredTrs, context) -> attempts);
	}

	private static Proof successfulProof(
			AnalysisContext context, String trace) {

		Proof proof = context.createProof();
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument("successful dependency pair proof");
		proof.printlnIfVerbose(trace);
		return proof;
	}

	private static AnalysisContext context(boolean verbose) {
		return new AnalysisContext(verbose, null);
	}

	private static List<RuleTrs> parseDenseSelfLoops(int ruleCount)
			throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new ArrayList<>();
		for (int ruleIndex = 0; ruleIndex < ruleCount; ruleIndex++) {
			String variableName = "X" + ruleIndex;
			rules.add(parser.parseTrsRule(
					"f(" + variableName + ") -> f(" + variableName + ")",
					variables));
		}
		return rules;
	}
}
