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

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Variable;

class TrsTerminationProverTest {

	@Test
	@DisplayName("skip DP analysis when a generalized rule proves nontermination")
	void skipDependencyPairAnalysisAfterGeneralizedRuleSuccess() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(
				parseTrs("f(X) -> Y"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
	}

	@Test
	@DisplayName("detect a bounded right-spine context loop before DP analysis")
	void detectRightSpineContextLoopBeforeDependencyPairAnalysis() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"f(a,f(a,f(b,f(X,Y)))) -> f(b,f(c,f(b,f(a,f(a,f(a,f(X,Y)))))))",
				"f(a,f(c,f(X,Y))) -> f(b,f(X,Y))"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("right-spine context loop", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains("rewrites in 12 steps"));
		assertTrue(proof.toString().contains("Found a right-spine context loop!"));
	}

	@Test
	@DisplayName("do not report a context loop for a terminating right-spine rule")
	void doNotReportAbsentRightSpineContextLoop() throws IOException {
		Proof proof = new TechRightSpineLoop().run(
				parseTrs("f(a,f(b,f(X,Y))) -> f(b,f(X,Y))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("ignore a right-spine abstraction whose variable residual changes")
	void ignoreChangedRightSpineResidual() throws IOException {
		Proof proof = new TechRightSpineLoop().run(
				parseTrs("f(a,f(a,f(X,Y))) -> f(a,f(a,f(Y,X)))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect a root variant cycle before DP analysis")
	void detectRootVariantCycleBeforeDependencyPairAnalysis() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"f(X) -> g(X)", "g(Y) -> f(Y)"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("root variant cycle", proof.getArgument().getWitnessKind());
		assertTrue(proof.toString().contains("Found a root variant cycle!"));
	}

	@Test
	@DisplayName("detect a bounded ground context loop before DP analysis")
	void detectGroundContextLoopBeforeDependencyPairAnalysis() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"active(zeros) -> mark(cons(zero,zeros))",
				"active(u11(tt,L)) -> mark(u12(tt,L))",
				"active(u12(tt,L)) -> mark(s(length(L)))",
				"active(length(cons(N,L))) -> mark(u11(tt,L))",
				"mark(zeros) -> active(zeros)",
				"mark(zero) -> active(zero)",
				"mark(tt) -> active(tt)",
				"mark(u11(X1,X2)) -> active(u11(mark(X1),X2))",
				"mark(u12(X1,X2)) -> active(u12(mark(X1),X2))",
				"mark(s(X)) -> active(s(mark(X)))",
				"mark(length(X)) -> active(length(mark(X)))",
				"u11(mark(X1),X2) -> u11(X1,X2)",
				"u12(mark(X1),X2) -> u12(X1,X2)",
				"s(mark(X)) -> s(X)",
				"length(mark(X)) -> length(X)"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("ground context loop", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains("rewrites in 12 steps"));
		assertTrue(proof.getArgument().toString().contains("position [0]"));
		assertTrue(proof.toString().contains("Found a ground context loop!"));
	}

	@Test
	@DisplayName("use a ground left-hand side to instantiate a context-loop seed")
	void useGroundLeftHandSideAsContextLoopSeed() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"active(f(a,b,X)) -> mark(f(X,X,X))",
				"active(c) -> mark(a)",
				"active(c) -> mark(b)",
				"mark(f(X1,X2,X3)) -> active(f(X1,X2,mark(X3)))",
				"mark(a) -> active(a)",
				"mark(b) -> active(b)",
				"mark(c) -> active(c)",
				"f(mark(X1),X2,X3) -> f(X1,X2,X3)",
				"f(X1,mark(X2),X3) -> f(X1,X2,X3)",
				"f(X1,X2,mark(X3)) -> f(X1,X2,X3)",
				"f(active(X1),X2,X3) -> f(X1,X2,X3)",
				"f(X1,active(X2),X3) -> f(X1,X2,X3)",
				"f(X1,X2,active(X3)) -> f(X1,X2,X3)"), analysis)
				.prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("ground context loop", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"active(f(a,b,active(c)))"));
		assertTrue(proof.getArgument().toString().contains("rewrites in 7 steps"));
	}

	@Test
	@DisplayName("detect a context loop from a mixed ground substitution")
	void detectMixedGroundContextLoopBeforeDependencyPairAnalysis()
			throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"active(f(X,g(X),Y)) -> mark(f(Y,Y,Y))",
				"active(g(b)) -> mark(c)",
				"active(b) -> mark(c)",
				"mark(f(X1,X2,X3)) -> active(f(X1,X2,X3))",
				"mark(g(X)) -> active(g(mark(X)))",
				"mark(b) -> active(b)",
				"mark(c) -> active(c)",
				"f(mark(X1),X2,X3) -> f(X1,X2,X3)",
				"f(X1,mark(X2),X3) -> f(X1,X2,X3)",
				"f(X1,X2,mark(X3)) -> f(X1,X2,X3)",
				"f(active(X1),X2,X3) -> f(X1,X2,X3)",
				"f(X1,active(X2),X3) -> f(X1,X2,X3)",
				"f(X1,X2,active(X3)) -> f(X1,X2,X3)",
				"g(mark(X)) -> g(X)",
				"g(active(X)) -> g(X)"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("ground context loop", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"active(f(mark(c),g(mark(c)),mark(g(b))))"));
		assertTrue(proof.getArgument().toString().contains("rewrites in 9 steps"));
	}

	@Test
	@DisplayName("detect a mixed ground loop from a linear seed rule")
	void detectMixedGroundLoopFromLinearSeedRule() throws IOException {
		Proof proof = new TechGroundContextLoop().run(parseTrs(
				"active(f(a,b,X)) -> mark(f(X,X,X))",
				"active(c) -> mark(a)",
				"active(c) -> mark(b)",
				"mark(f(X1,X2,X3)) -> " +
						"active(f(mark(X1),X2,mark(X3)))",
				"mark(a) -> active(a)",
				"mark(b) -> active(b)",
				"mark(c) -> active(c)",
				"f(mark(X1),X2,X3) -> f(X1,X2,X3)",
				"f(X1,mark(X2),X3) -> f(X1,X2,X3)",
				"f(X1,X2,mark(X3)) -> f(X1,X2,X3)",
				"f(active(X1),X2,X3) -> f(X1,X2,X3)",
				"f(X1,active(X2),X3) -> f(X1,X2,X3)",
				"f(X1,X2,active(X3)) -> f(X1,X2,X3)"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("ground context loop", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"mark(f(mark(a),mark(b),active(c)))"));
		assertTrue(proof.getArgument().toString().contains("rewrites in 9 steps"));
	}

	@Test
	@DisplayName("do not infer a ground context loop from mere growth")
	void doNotReportAbsentGroundContextLoop() throws IOException {
		Proof proof = new TechGroundContextLoop().run(
				parseTrs("f(f(a)) -> f(a)"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect bounded unary counter growth before DP analysis")
	void detectUnaryCounterGrowthBeforeDependencyPairAnalysis()
			throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"f(X,s(Y)) -> f(d(X),Y)",
				"f(X,0) -> f(s(0),X)",
				"d(0) -> 0",
				"d(s(X)) -> s(s(d(X)))"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("unary counter growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"f(s(0),s(s(0))) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"f(s(0),s(s(s(s(0)))))"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 8 steps"));
		assertTrue(proof.toString().contains("Found unary counter growth!"));
	}

	@Test
	@DisplayName("reject an incomplete unary counter growth schema")
	void doNotReportIncompleteUnaryCounterGrowthSchema() throws IOException {
		Proof proof = new TechUnaryCounterGrowth().run(parseTrs(
				"f(X,s(Y)) -> f(d(X),Y)",
				"f(X,0) -> f(s(0),X)",
				"d(0) -> 0",
				"d(s(X)) -> s(s(s(d(X))))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect arithmetic unary-counter growth with both addition forms")
	void detectArithmeticUnaryCounterGrowth() throws IOException {
		for (String additionRule : List.of(
				"add(next(X),Y) -> add(X,next(Y))",
				"add(next(X),Y) -> next(add(X,Y))")) {
			Proof proof = new TechUnaryCounterGrowth().run(parseTrs(
					"g(ok,X,Y) -> g(greater(X,Y),twice(X),next(Y))",
					"greater(next(X),zero) -> ok",
					"greater(next(X),next(Y)) -> greater(X,Y)",
					"twice(X) -> mult(X,next(next(zero)))",
					"mult(zero,Y) -> zero",
					"mult(next(X),Y) -> add(Y,mult(X,Y))",
					"add(zero,Y) -> Y",
					additionRule), context());

			assertEquals(Proof.ProofResult.NO, proof.getResult());
			assertEquals(
					"unary counter growth", proof.getArgument().getWitnessKind());
			assertTrue(proof.getArgument().toString().contains(
					"g(ok,next(next(zero)),next(zero)) is non-terminating"));
			assertTrue(proof.getArgument().toString().contains(
					"g(ok,next(next(next(next(zero)))),next(next(zero)))"));
			assertTrue(proof.getArgument().toString().contains(
					"rewrites in 13 steps"));
			assertEquals(13, proof.getArgument().getDetails(0).lines().count());
		}
	}

	@Test
	@DisplayName("reject a near arithmetic unary-counter schema")
	void doNotReportNearArithmeticUnaryCounterGrowth() throws IOException {
		Proof proof = new TechUnaryCounterGrowth().run(parseTrs(
				"g(ok,X,Y) -> g(greater(X,Y),twice(X),next(Y))",
				"greater(next(X),zero) -> ok",
				"greater(next(X),next(Y)) -> greater(X,Y)",
				"twice(X) -> mult(X,next(next(zero)))",
				"mult(zero,Y) -> zero",
				"mult(next(X),Y) -> add(X,mult(X,Y))",
				"add(zero,Y) -> Y",
				"add(next(X),Y) -> next(add(X,Y))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect three guarded unary-counter growth presentations")
	void detectGuardedUnaryCounterGrowth() throws IOException {
		List<List<String>> systems = List.of(
				List.of(
						"while(true,X,Y) -> cond(gt(X,zero),X,Y)",
						"cond(true,s(X),Y) -> while(gt(Y,zero),X,Y)",
						"cond(false,X,Y) -> " +
								"while(gt(s(Y),zero),s(Y),s(Y))",
						"gt(s(X),zero) -> true",
						"gt(zero,X) -> false"),
				List.of(
						"while(true,I,Y) -> " +
								"while(and(notZero(Y),positive(I)),minus(I,Y),Y)",
						"notZero(neg(s(X))) -> true",
						"positive(pos(s(X))) -> true",
						"and(true,true) -> true",
						"minus(pos(X),neg(Y)) -> pos(add(X,Y))",
						"add(zero,Y) -> Y",
						"add(s(X),Y) -> add(X,s(Y))"),
				List.of(
						"while(true,s(s(s(I)))) -> " +
								"while(gt(s(s(s(I))),s(zero)),f(s(s(s(I)))))",
						"gt(s(X),s(Y)) -> gt(X,Y)",
						"gt(s(X),zero) -> true",
						"f(I) -> if(neq(I,s(s(zero))),I)",
						"neq(s(X),s(Y)) -> neq(X,Y)",
						"neq(s(X),zero) -> true",
						"if(true,I) -> add(I,s(zero))",
						"add(zero,Y) -> Y",
						"add(s(X),Y) -> add(X,s(Y))"));

		for (List<String> system : systems) {
			AtomicBoolean analysisInvoked = new AtomicBoolean();
			DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
				analysisInvoked.set(true);
				return null;
			};
			Proof proof = new TrsTerminationProver(
					parseTrs(system.toArray(String[]::new)), analysis).prove(context());

			assertEquals(Proof.ProofResult.NO, proof.getResult());
			assertFalse(analysisInvoked.get());
			assertEquals("guarded unary counter growth",
					proof.getArgument().getWitnessKind());
			assertTrue(proof.getArgument().toString().contains("W(n+1)"));
			assertTrue(proof.toString().contains(
					"Found guarded unary counter growth!"));
		}
	}

	@Test
	@DisplayName("reject incomplete guarded unary-counter growth presentations")
	void doNotReportNearGuardedUnaryCounterGrowth() throws IOException {
		List<List<String>> systems = List.of(
				List.of(
						"while(true,X,Y) -> cond(gt(X,zero),X,Y)",
						"cond(true,s(X),Y) -> while(gt(Y,zero),X,Y)",
						"cond(false,X,Y) -> " +
								"while(gt(s(Y),zero),s(Y),Y)",
						"gt(s(X),zero) -> true",
						"gt(zero,X) -> false"),
				List.of(
						"while(true,I,Y) -> " +
								"while(and(notZero(Y),positive(I)),minus(I,Y),Y)",
						"notZero(neg(s(X))) -> true",
						"positive(pos(s(X))) -> true",
						"and(true,true) -> false",
						"minus(pos(X),neg(Y)) -> pos(add(X,Y))",
						"add(zero,Y) -> Y",
						"add(s(X),Y) -> add(X,s(Y))"),
				List.of(
						"while(true,s(s(s(I)))) -> " +
								"while(gt(s(s(s(I))),s(zero)),f(s(s(s(I)))))",
						"gt(s(X),s(Y)) -> gt(X,Y)",
						"gt(s(X),zero) -> true",
						"f(I) -> if(neq(I,s(s(zero))),I)",
						"neq(s(X),s(Y)) -> neq(X,Y)",
						"neq(s(X),zero) -> true",
						"if(true,I) -> add(I,s(s(zero)))",
						"add(zero,Y) -> Y",
						"add(s(X),Y) -> add(X,s(Y))"));

		for (List<String> system : systems) {
			Proof proof = new TechGuardedUnaryCounterGrowth().run(
					parseTrs(system.toArray(String[]::new)), context());
			assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
			assertFalse(proof.isSuccess());
		}
	}

	@Test
	@DisplayName("detect three guarded evaluator-growth presentations")
	void detectGuardedEvaluatorGrowth() throws IOException {
		List<List<String>> systems = List.of(
				List.of(
						"both(ok,ok) -> ok",
						"nat(zero) -> ok",
						"nat(next(X)) -> nat(X)",
						"list(empty) -> ok",
						"list(node(X,XS)) -> both(nat(X),list(XS))",
						"produce(XS) -> branch(list(XS),XS)",
						"branch(ok,node(X,XS)) -> " +
								"produce(node(next(X),node(X,XS)))"),
				List.of(
						"list(empty) -> ok",
						"list(node(X,XS)) -> list(XS)",
						"generate(zero) -> empty",
						"generate(next(X)) -> node(next(X),generate(X))",
						"produce(X) -> branch(list(generate(X)),next(X))",
						"branch(ok,X) -> produce(X)"),
				List.of(
						"state(ok,ok,X,next(Y)) -> " +
								"state(nat(X),nat(Y),next(X),twice(next(Y)))",
						"nat(zero) -> ok",
						"nat(next(X)) -> nat(X)",
						"twice(zero) -> zero",
						"twice(next(X)) -> next(next(twice(X)))"));
		List<Integer> firstPhaseLengths = List.of(6, 4, 5);

		for (int index = 0; index < systems.size(); index++) {
			AtomicBoolean analysisInvoked = new AtomicBoolean();
			DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
				analysisInvoked.set(true);
				return null;
			};
			Proof proof = new TrsTerminationProver(
					parseTrs(systems.get(index).toArray(String[]::new)), analysis)
					.prove(context());

			assertEquals(Proof.ProofResult.NO, proof.getResult());
			assertFalse(analysisInvoked.get());
			assertEquals(
					"guarded evaluator growth",
					proof.getArgument().getWitnessKind());
			assertTrue(proof.getArgument().toString().contains("W(n+1)"));
			assertEquals(
					firstPhaseLengths.get(index).longValue(),
					proof.getArgument().getDetails(0).lines().count());
			assertTrue(proof.toString().contains(
					"Found guarded evaluator growth!"));
		}
	}

	@Test
	@DisplayName("reject incomplete guarded evaluator-growth presentations")
	void doNotReportNearGuardedEvaluatorGrowth() throws IOException {
		List<List<String>> systems = List.of(
				List.of(
						"both(ok,ok) -> ok",
						"nat(zero) -> ok",
						"nat(next(X)) -> nat(next(X))",
						"list(empty) -> ok",
						"list(node(X,XS)) -> both(nat(X),list(XS))",
						"produce(XS) -> branch(list(XS),XS)",
						"branch(ok,node(X,XS)) -> " +
								"produce(node(next(X),node(X,XS)))"),
				List.of(
						"list(empty) -> ok",
						"list(node(X,XS)) -> list(XS)",
						"generate(zero) -> empty",
						"generate(next(X)) -> node(X,generate(X))",
						"produce(X) -> branch(list(generate(X)),next(X))",
						"branch(ok,X) -> produce(X)"),
				List.of(
						"state(ok,ok,X,next(Y)) -> " +
								"state(nat(X),nat(Y),next(X),twice(Y))",
						"nat(zero) -> ok",
						"nat(next(X)) -> nat(X)",
						"twice(zero) -> zero",
						"twice(next(X)) -> next(next(twice(X)))"));

		for (List<String> system : systems) {
			Proof proof = new TechGuardedEvaluatorGrowth().run(
					parseTrs(system.toArray(String[]::new)), context());
			assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
			assertFalse(proof.isSuccess());
		}
	}

	@Test
	@DisplayName("detect a bounded Owl-rule invariant before DP analysis")
	void detectOwlRuleBeforeDependencyPairAnalysis() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"a(a(delta,X),Y) -> a(Y,a(X,Y))"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("Owl-rule invariant", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"a(a(delta,delta),a(delta,delta)) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains("P(t) = 2"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 1, position 𝜀)"));
		assertTrue(proof.toString().contains(
				"[Endrullis and Zantema, RTA'15]"));
		assertTrue(proof.toString().contains("Found an Owl rule!"));
	}

	@Test
	@DisplayName("reject a near Owl rule with a changed duplicated variable")
	void doNotReportNearOwlRule() throws IOException {
		Proof proof = new TechOwlRule().run(parseTrs(
				"a(a(delta,X),Y) -> a(Y,a(Y,X))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect bounded list growth before DP analysis")
	void detectListGrowthBeforeDependencyPairAnalysis() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"f(tt,X) -> f(isList(X),cons(tt,X))",
				"isList(cons(X,XS)) -> isList(XS)",
				"isList(nil) -> tt"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("list growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"f(tt,nil) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"f(tt,cons(tt,nil))"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 2 steps"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 1, position 𝜀)"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 3, position [0])"));
		assertTrue(proof.toString().contains("Found list growth!"));
	}

	@Test
	@DisplayName("detect bounded list growth with a duplicated tail")
	void detectListGrowthWithDuplicatedTail() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"f(tt,X) -> f(isList(X),cons(X,X))",
				"isList(cons(X,XS)) -> isList(XS)",
				"isList(nil) -> tt"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("list growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"L(n+1) = cons(Ln,Ln)"));
		assertTrue(proof.getArgument().toString().contains(
				"f(tt,cons(nil,nil))"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 2 steps"));
	}

	@Test
	@DisplayName("reject a near list-growth rule with a changed tail")
	void doNotReportNearListGrowthRule() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"f(tt,X) -> f(isList(X),cons(tt,X))",
				"isList(cons(X,XS)) -> isList(X)",
				"isList(nil) -> tt"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect guarded list growth with renamed symbols")
	void detectGuardedListGrowthWithRenamedSymbols() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"g(ok,N,XS) -> g(both(nat(N),list(XS)),N,node(N,XS))",
				"list(node(H,T)) -> list(T)",
				"list(empty) -> ok",
				"nat(zero) -> ok",
				"both(ok,ok) -> ok"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("list growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"g(ok,zero,empty) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"g(ok,zero,node(zero,empty))"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 4 steps"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 4, position [0, 0])"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 3, position [0, 1])"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 5, position [0])"));
	}

	@Test
	@DisplayName("reject guarded list growth without the true conjunction rule")
	void doNotReportNearGuardedListGrowth() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"g(ok,N,XS) -> g(both(nat(N),list(XS)),N,node(N,XS))",
				"list(node(H,T)) -> list(T)",
				"list(empty) -> ok",
				"nat(zero) -> ok",
				"both(ok,bad) -> ok"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect list growth through a symbolic evaluator")
	void detectListGrowthThroughSymbolicEvaluator() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"g(ok,XS) -> g(list(XS),cat(cell(a,empty),XS))",
				"list(empty) -> ok",
				"list(cell(H,T)) -> list(T)",
				"cat(empty,Y) -> Y",
				"cat(cell(H,T),Y) -> cell(H,cat(T,Y))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("list growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"g(ok,empty) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"g(ok,cell(a,empty))"));
		assertTrue(proof.getArgument().toString().contains(
				"symbolic evaluator path"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 4 steps"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 5, position [1])"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 4, position [1, 1])"));
	}

	@Test
	@DisplayName("reject an evaluator that does not retain the current tail")
	void doNotReportNearEvaluatorListGrowth() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"g(ok,XS) -> g(list(XS),cat(cell(a,empty),XS))",
				"list(empty) -> ok",
				"list(cell(H,T)) -> list(T)",
				"cat(empty,Y) -> Y",
				"cat(cell(H,T),Y) -> cell(H,cat(T,empty))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect list growth behind a length-equality guard")
	void detectLengthGuardedListGrowth() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"g(ok,XS) -> g(same(next(size(XS)),size(node(mark,XS)))," +
						"cat(node(value,empty),XS))",
				"size(empty) -> zero",
				"size(node(H,T)) -> next(size(T))",
				"same(zero,zero) -> ok",
				"same(next(X),next(Y)) -> same(X,Y)",
				"cat(empty,Y) -> Y",
				"cat(node(H,T),Y) -> node(H,cat(T,Y))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("list growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"g(ok,empty) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"g(ok,node(value,empty))"));
		assertTrue(proof.getArgument().toString().contains(
				"guard reduces to ok in 3n+5 steps"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 8 steps"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 3, position [0, 1])"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 5, position [0])"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 7, position [1])"));
	}

	@Test
	@DisplayName("reject a changed length-equality traversal")
	void doNotReportNearLengthGuardedListGrowth() throws IOException {
		Proof proof = new TechListGrowth().run(parseTrs(
				"g(ok,XS) -> g(same(next(size(XS)),size(node(mark,XS)))," +
						"node(value,XS))",
				"size(empty) -> zero",
				"size(node(H,T)) -> next(size(T))",
				"same(zero,zero) -> ok",
				"same(next(X),next(Y)) -> same(X,next(Y))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect bounded unary shuttle growth before DP analysis")
	void detectUnaryShuttleGrowthBeforeDependencyPairAnalysis()
			throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"r(X,a(Y)) -> r(a(X),Y)",
				"r(X,b) -> l(X,a(b))",
				"l(a(X),Y) -> l(X,a(Y))",
				"l(b,X) -> r(a(b),X)"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals(
				"unary shuttle growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"r(a(b),b) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"r(a(b),a(a(b)))"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 3 steps"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 2, position 𝜀)"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 3, position 𝜀)"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 4, position 𝜀)"));
		assertTrue(proof.toString().contains("Found unary shuttle growth!"));
	}

	@Test
	@DisplayName("reject a near unary-shuttle transfer rule")
	void doNotReportNearUnaryShuttleTransferRule() throws IOException {
		Proof proof = new TechUnaryShuttleGrowth().run(parseTrs(
				"r(X,a(Y)) -> r(a(X),Y)",
				"r(X,b) -> l(X,a(b))",
				"l(a(X),Y) -> l(Y,a(X))",
				"l(b,X) -> r(a(b),X)"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect unary-marker growth inside a context")
	void detectUnaryMarkerGrowthInsideContext() throws IOException {
		Proof proof = new TechUnaryShuttleGrowth().run(parseTrs(
				"a(l(X)) -> l(a(X))",
				"r(a(X)) -> a(r(X))",
				"b(l(X)) -> b(r(X))",
				"r(b(X)) -> l(a(b(X)))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals(
				"unary shuttle growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"b(r(b(_0))) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"C[r(Tn)] ->^(2n+2) C[r(T(n+1))]"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 4, position [0])"));
		assertTrue(proof.getArgument().toString().contains(
				"(rule 3, position 𝜀)"));
	}

	@Test
	@DisplayName("detect argument-swapping binary unary-marker growth")
	void detectArgumentSwappingBinaryUnaryMarkerGrowth() throws IOException {
		Proof proof = new TechUnaryShuttleGrowth().run(parseTrs(
				"a(l(X)) -> l(a(X))",
				"r(a(X)) -> a(r(X))",
				"f(l(X),l(Y)) -> f(a(r(Y)),r(X))",
				"r(b(X)) -> l(b(X))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals(
				"unary shuttle growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"f(l(a(b(_0))),l(b(_0))) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"f(l(Ap),l(Aq)) ->+ f(l(A(q+1)),l(A(p)))"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 6 steps"));
	}

	@Test
	@DisplayName("reject unary-marker growth without a pumping rule")
	void doNotReportUnaryMarkerGrowthWithoutPump() throws IOException {
		Proof proof = new TechUnaryShuttleGrowth().run(parseTrs(
				"a(l(X)) -> l(a(X))",
				"r(a(X)) -> a(r(X))",
				"b(l(X)) -> b(r(X))",
				"r(b(X)) -> l(b(X))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect expanding modular block shuttle")
	void detectExpandingModularBlockShuttle() throws IOException {
		Proof proof = new TechUnaryShuttleGrowth().run(parseTrs(
				"step(left(X)) -> left(step(X))",
				"right(step(step(X))) -> step(step(step(right(X))))",
				"wall(left(X)) -> wall(right(step(X)))",
				"right(wall(X)) -> left(wall(X))",
				"right(step(wall(X))) -> left(step(wall(X)))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals(
				"unary shuttle growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"wall(left(wall(_0))) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"wall(left(step(step(step(wall(_0))))))"));
		assertTrue(proof.getArgument().toString().contains(
				"n mod 2 = 0: rule 5"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 8 steps"));
	}

	@Test
	@DisplayName("detect parity-controlled modular block shuttle")
	void detectParityControlledModularBlockShuttle() throws IOException {
		Proof proof = new TechUnaryShuttleGrowth().run(parseTrs(
				"step(step(left(X))) -> left(step(step(X)))",
				"right(step(X)) -> step(right(X))",
				"wall(left(X)) -> wall(right(X))",
				"right(wall(X)) -> left(step(wall(X)))",
				"right(wall(X)) -> step(left(wall(X)))"), context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals(
				"unary shuttle growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"wall(left(step(step(wall(_0)))))"));
		assertTrue(proof.getArgument().toString().contains(
				"n mod 2 = 1: rule 5"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 6 steps"));
	}

	@Test
	@DisplayName("reject a non-growing modular block shuttle")
	void doNotReportNonGrowingModularBlockShuttle() throws IOException {
		Proof proof = new TechUnaryShuttleGrowth().run(parseTrs(
				"step(left(X)) -> left(step(X))",
				"right(step(step(X))) -> step(right(X))",
				"wall(left(X)) -> wall(right(step(X)))",
				"right(wall(X)) -> left(wall(X))",
				"right(step(wall(X))) -> left(step(wall(X)))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect bounded unary swap-decrement growth before DP analysis")
	void detectUnarySwapDecrementGrowthBeforeDependencyPairAnalysis()
			throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"f(tt,X) -> f(swap(X,z),s(X))",
				"swap(s(X),Y) -> swap(X,s(Y))",
				"swap(z,s(Y)) -> decr(s(Y))",
				"decr(s(Y)) -> decr(Y)",
				"decr(z) -> tt"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("unary swap-decrement growth",
				proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"f(tt,s(z)) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains(
				"f(tt,s(s(z)))"));
		assertTrue(proof.getArgument().toString().contains(
				"rewrites in 5 steps"));
		for (int ruleNumber = 1; ruleNumber <= 5; ruleNumber++)
			assertTrue(proof.getArgument().toString().contains(
					"(rule " + ruleNumber + ", position"));
		assertTrue(proof.toString().contains(
				"Found unary swap-decrement growth!"));
	}

	@Test
	@DisplayName("reject a near unary swap-exit rule")
	void doNotReportNearUnarySwapExitRule() throws IOException {
		Proof proof = new TechUnarySwapDecrementGrowth().run(parseTrs(
				"f(tt,X) -> f(swap(X,z),s(X))",
				"swap(s(X),Y) -> swap(X,s(Y))",
				"swap(z,s(Y)) -> decr(Y)",
				"decr(s(Y)) -> decr(Y)",
				"decr(z) -> tt"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect bounded guarded context growth before DP analysis")
	void detectGuardedContextGrowthBeforeDependencyPairAnalysis() throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"work(a) -> mark(b)",
				"proper(b) -> ok(b)",
				"work(b) -> mark(s(a))",
				"proper(s(X)) -> s(proper(X))",
				"proper(a) -> ok(a)",
				"s(ok(X)) -> ok(s(X))",
				"s(mark(X)) -> mark(s(X))",
				"work(s(X)) -> s(work(X))",
				"top(mark(X)) -> top(proper(X))",
				"top(ok(X)) -> top(work(X))"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals("guarded context growth", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains(
				"top(work(a)) is non-terminating"));
		assertTrue(proof.getArgument().toString().contains("Core phase 2"));
		assertTrue(proof.toString().contains("Found guarded context growth!"));
	}

	@Test
	@DisplayName("do not infer guarded growth without a pumping core cycle")
	void doNotReportAbsentGuardedContextGrowth() throws IOException {
		Proof proof = new TechGuardedContextGrowth().run(parseTrs(
				"work(a) -> mark(b)",
				"proper(b) -> ok(b)",
				"work(b) -> mark(c)",
				"proper(c) -> ok(c)",
				"proper(s(X)) -> s(proper(X))",
				"s(ok(X)) -> ok(s(X))",
				"s(mark(X)) -> mark(s(X))",
				"work(s(X)) -> s(work(X))",
				"top(mark(X)) -> top(proper(X))",
				"top(ok(X)) -> top(work(X))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect both bounded forward-closure ground cycles")
	void detectForwardClosureGroundCycles() throws IOException {
		Proof first = new TechForwardClosureGroundCycle().run(parseTrs(
				"f(f(Y,P),f(Z,f(X,a))) -> f(f(Z,f(Y,a)),f(P,X))"),
				context());
		Proof second = new TechForwardClosureGroundCycle().run(parseTrs(
				"f(f(f(X,f(Y,a)),Z),P) -> f(f(f(f(a,P),Y),X),Z)"),
				context());

		assertEquals(Proof.ProofResult.NO, first.getResult());
		assertEquals(Proof.ProofResult.NO, second.getResult());
		assertEquals(
				"forward-closure ground cycle",
				first.getArgument().getWitnessKind());
		assertTrue(first.getArgument().toString().contains(
				"ground instance rewrites in 17 steps"));
		assertTrue(second.getArgument().toString().contains(
				"ground instance rewrites in 19 steps"));
		assertTrue(second.getArgument().toString().contains(
				"rule 1, position [0, 0, 0, 0, 0, 1]"));
	}

	@Test
	@DisplayName("reject a terminating forward-closure near-schema")
	void doNotReportAbsentForwardClosureGroundCycle() throws IOException {
		Proof proof = new TechForwardClosureGroundCycle().run(parseTrs(
				"f(f(X,Y),Z) -> f(X,f(Y,Z))"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("detect synchronized argument instantiation before DP analysis")
	void detectSynchronizedArgumentLoopBeforeDependencyPairAnalysis()
			throws IOException {
		AtomicBoolean analysisInvoked = new AtomicBoolean();
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			analysisInvoked.set(true);
			return null;
		};

		Proof proof = new TrsTerminationProver(parseTrs(
				"eq(n__zero,n__zero) -> true",
				"eq(n__s(X),n__s(Y)) -> eq(activate(X),activate(Y))",
				"eq(X,Y) -> false",
				"inf(X) -> cons(X,n__inf(n__s(X)))",
				"take(zero,X) -> nil",
				"take(s(X),cons(Y,L)) -> " +
						"cons(activate(Y),n__take(activate(X),activate(L)))",
				"length(nil) -> zero",
				"length(cons(X,L)) -> s(n__length(activate(L)))",
				"zero -> n__zero",
				"s(X) -> n__s(X)",
				"inf(X) -> n__inf(X)",
				"take(X1,X2) -> n__take(X1,X2)",
				"length(X) -> n__length(X)",
				"activate(n__zero) -> zero",
				"activate(n__s(X)) -> s(X)",
				"activate(n__inf(X)) -> inf(activate(X))",
				"activate(n__take(X1,X2)) -> " +
						"take(activate(X1),activate(X2))",
				"activate(n__length(X)) -> length(activate(X))",
				"activate(X) -> X"), analysis).prove(context());

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertFalse(analysisInvoked.get());
		assertEquals(
				"synchronized argument loop", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains("rewrites in 13 steps"));
		assertTrue(proof.getArgument().toString().contains("rule 2, position 𝜀"));
		assertTrue(proof.toString().contains(
				"Found a synchronized argument loop!"));
	}

	@Test
	@DisplayName("do not infer synchronized growth without an instantiation loop")
	void doNotReportAbsentSynchronizedArgumentLoop() throws IOException {
		Proof proof = new TechSynchronizedArgumentLoop().run(parseTrs(
				"pair(s(X),s(Y)) -> pair(active(X),active(Y))",
				"active(X) -> X"), context());

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("merge the proof selected by the DP analysis")
	void mergeProofSelectedByDependencyPairAnalysis() throws IOException {
		DependencyPairAnalysisRunner analysis = (context, diagnosticProof) -> {
			Proof proof = context.createProof();
			proof.setResult(Proof.ProofResult.YES);
			proof.setArgument("dependency pair proof");
			return proof;
		};

		Proof proof = new TrsTerminationProver(
				parseTrs("f(X) -> X"), analysis).prove(context());

		assertEquals(Proof.ProofResult.YES, proof.getResult());
		assertEquals("dependency pair proof", proof.getArgument().toString());
		assertTrue(proof.isSuccess());
		String description = proof.toString();
		assertTrue(description.contains(
				"## Searching for a bounded right-spine context loop..."));
		assertTrue(description.contains("No right-spine context loop found!"));
		assertTrue(description.contains("## Searching for a root variant cycle..."));
		assertTrue(description.contains("No root variant cycle found!"));
		assertTrue(description.contains(
				"## Searching for a bounded forward-closure ground cycle..."));
		assertTrue(description.contains(
				"No forward-closure ground cycle found!"));
		assertTrue(description.contains(
				"## Searching for a bounded ground context loop..."));
		assertTrue(description.contains("No ground context loop found!"));
		assertTrue(description.contains(
				"## Searching for bounded unary counter growth..."));
		assertTrue(description.contains("No unary counter growth found!"));
		assertTrue(description.contains(
				"## Searching for bounded guarded unary counter growth..."));
		assertTrue(description.contains(
				"No guarded unary counter growth found!"));
		assertTrue(description.contains(
				"## Searching for bounded guarded evaluator growth..."));
		assertTrue(description.contains(
				"No guarded evaluator growth found!"));
		assertTrue(description.contains(
				"## Searching for a bounded Owl rule " +
				"[Endrullis and Zantema, RTA'15]..."));
		assertTrue(description.contains("No Owl rule found!"));
		assertTrue(description.contains(
				"## Searching for bounded list growth..."));
		assertTrue(description.contains("No list growth found!"));
		assertTrue(description.contains(
				"## Searching for bounded unary shuttle growth..."));
		assertTrue(description.contains("No unary shuttle growth found!"));
		assertTrue(description.contains(
				"## Searching for bounded unary swap-decrement growth..."));
		assertTrue(description.contains(
				"No unary swap-decrement growth found!"));
		assertTrue(description.contains(
				"## Searching for bounded guarded context growth..."));
		assertTrue(description.contains("No guarded context growth found!"));
		assertTrue(description.contains(
				"## Searching for a bounded synchronized argument loop..."));
		assertTrue(description.contains("No synchronized argument loop found!"));
		assertTrue(description.contains(
				"## Searching for a bounded regular-language " +
						"nontermination certificate " +
						"[Endrullis and Zantema, RTA'15]..."));
		assertTrue(description.contains(
				"No regular-language nontermination certificate found!"));
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
