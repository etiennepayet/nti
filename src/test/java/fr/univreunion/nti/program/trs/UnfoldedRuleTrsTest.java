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

package fr.univreunion.nti.program.trs;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.argument.ArgumentLoopByUnfolding;
import fr.univreunion.nti.program.trs.ruleunfolding.SimpleCycleRegistry;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class UnfoldedRuleTrsTest {

	@Test
	@DisplayName("recognize shallow matching, unification and failure")
	void recognizeShallowMatchingUnificationAndFailure() throws IOException {
		TestUnfoldedRule matching = testRule("f(X) -> f(a)");
		TestUnfoldedRule unifying = testRule("f(a) -> f(X)");
		TestUnfoldedRule failing = testRule("f(a) -> g(a)");

		assertNotNull(UnfoldedRuleTrs.shallowMatchAndUnifyTest(matching));
		assertNotNull(UnfoldedRuleTrs.shallowMatchAndUnifyTest(unifying));
		assertNull(UnfoldedRuleTrs.shallowMatchAndUnifyTest(failing));
		assertEquals("f(_0) -> f(a)", matching.toString());
		assertEquals("f(a) -> f(_0)", unifying.toString());
	}

	@Test
	@DisplayName("find a deep witness below the root")
	void findADeepWitnessBelowTheRoot() throws IOException {
		TestUnfoldedRule rule = testRule("f(X) -> g(f(a))");

		assertNull(UnfoldedRuleTrs.shallowMatchAndUnifyTest(rule));
		assertNotNull(UnfoldedRuleTrs.deepMatchAndUnifyTest(rule));
		assertEquals("f(_0) -> g(f(a))", rule.toString());
	}

	@Test
	@DisplayName("recognize shallow left-unification without modifying the rule")
	void recognizeShallowLeftUnificationWithoutModification() throws IOException {
		TestUnfoldedRule looping = testRule("f(X) -> f(a)");
		TestUnfoldedRule failing = testRule("f(a) -> g(a)");

		assertNotNull(UnfoldedRuleTrs.shallowLeftUnifyTest(looping));
		assertNull(UnfoldedRuleTrs.shallowLeftUnifyTest(failing));
		assertEquals("f(_0) -> f(a)", looping.toString());
	}

	@Test
	@DisplayName("delegate elimination when no witness is found")
	void delegateEliminationWhenNoWitnessIsFound() throws IOException {
		TestUnfoldedRule source = testRule("f -> g");
		TestUnfoldedRule first = testRule("a -> b");
		TestUnfoldedRule second = testRule("c -> d");
		source.eliminationResult = List.of(first, second);
		Proof proof = new Proof(false);

		Collection<UnfoldedRuleTrs> result = source.elimAndProve(
				new Parameters(), emptyTrs(), new SimpleCycleRegistry(), proof);

		assertEquals(List.of(first, second), result);
		assertEquals(1, source.eliminationCount);
		assertFalse(proof.isSuccess());
	}

	@Test
	@DisplayName("retain a witness and skip elimination")
	void retainAWitnessAndSkipElimination() throws IOException {
		TestUnfoldedRule source = testRule("f -> f");
		source.witness = true;
		Proof proof = new Proof(false);

		Collection<UnfoldedRuleTrs> result = source.elimAndProve(
				new Parameters(), emptyTrs(), new SimpleCycleRegistry(), proof);

		assertEquals(List.of(source), result);
		assertEquals(0, source.eliminationCount);
		assertTrue(proof.isSuccess());
		assertSame(source, ((ArgumentLoopByUnfolding) proof.getArgument())
				.getUnfoldedRule());
	}

	@Test
	@DisplayName("enumerate forward before backward unfolding in TRS order")
	void enumerateForwardBeforeBackwardUnfoldingInTrsOrder() throws IOException {
		List<String> calls = new ArrayList<>();
		TestUnfoldedRule source = testRule("f -> g");
		source.calls = calls;
		TestUnfoldedRule forward = testRule("u -> v");
		TestUnfoldedRule backward = testRule("w -> x");
		source.forwardResult = List.of(forward);
		source.backwardResult = List.of(backward);
		forward.eliminationResult = List.of(forward);
		backward.eliminationResult = List.of(backward);
		Trs trs = parseTrs("a -> b", "c -> d");

		Collection<UnfoldedRuleTrs> result = source.unfold(
				new Parameters(), trs, new SimpleCycleRegistry(), 4, null);

		assertEquals(List.of("F:a -> b", "F:c -> d", "B:a -> b", "B:c -> d"),
				calls);
		assertEquals(List.of(forward, forward, backward, backward), result);
		assertEquals(2, forward.eliminationCount);
		assertEquals(2, backward.eliminationCount);
	}

	@Test
	@DisplayName("stop unfolding as soon as a generated rule proves nontermination")
	void stopUnfoldingAsSoonAsAGeneratedRuleProvesNontermination()
			throws IOException {

		List<String> calls = new ArrayList<>();
		TestUnfoldedRule source = testRule("f -> g");
		source.calls = calls;
		TestUnfoldedRule witness = testRule("u -> u");
		TestUnfoldedRule ignored = testRule("w -> x");
		witness.witness = true;
		source.forwardResult = List.of(witness, ignored);
		source.backwardResult = List.of(ignored);
		Proof proof = new Proof(false);

		Collection<UnfoldedRuleTrs> result = source.unfold(
				new Parameters(), parseTrs("a -> b", "c -> d"),
				new SimpleCycleRegistry(), 1, proof);

		assertEquals(List.of("F:a -> b"), calls);
		assertEquals(List.of(witness), result);
		assertTrue(proof.isSuccess());
		assertEquals(0, ignored.eliminationCount);
	}

	@Test
	@DisplayName("do not serialize independent unfolding eliminations")
	void doNotSerializeIndependentUnfoldingEliminations() throws Exception {
		CountDownLatch eliminationsStarted = new CountDownLatch(2);
		CountDownLatch releaseEliminations = new CountDownLatch(1);
		TestUnfoldedRule first = testRule("f -> g");
		TestUnfoldedRule second = testRule("h -> i");
		first.eliminationResult = List.of(first);
		second.eliminationResult = List.of(second);
		first.blockElimination(eliminationsStarted, releaseEliminations);
		second.blockElimination(eliminationsStarted, releaseEliminations);
		Proof firstProof = new Proof(false);
		Proof secondProof = new Proof(false);
		LinkedList<UnfoldedRuleTrs> firstResult = new LinkedList<>();
		LinkedList<UnfoldedRuleTrs> secondResult = new LinkedList<>();
		ExecutorService executor = Executors.newFixedThreadPool(2);

		try {
			Future<Boolean> firstFuture = executor.submit(() ->
					TestUnfoldedRule.addForTest(
							first, firstProof, firstResult));
			Future<Boolean> secondFuture = executor.submit(() ->
					TestUnfoldedRule.addForTest(
							second, secondProof, secondResult));

			assertTrue(eliminationsStarted.await(2, TimeUnit.SECONDS));
			releaseEliminations.countDown();
			assertFalse(firstFuture.get(2, TimeUnit.SECONDS));
			assertFalse(secondFuture.get(2, TimeUnit.SECONDS));
		}
		finally {
			releaseEliminations.countDown();
			executor.shutdownNow();
		}

		assertEquals(List.of(first), firstResult);
		assertEquals(List.of(second), secondResult);
		assertFalse(firstProof.isSuccess());
		assertFalse(secondProof.isSuccess());
	}

	private static TestUnfoldedRule testRule(String text) throws IOException {
		RuleTrs rule = parseRule(text);
		return new TestUnfoldedRule(rule.getLeft(), rule.getRight(), 0, null);
	}

	private static Trs emptyTrs() {
		return new Trs("", List.of(), "FULL");
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		return new Trs("", parseRules(ruleTexts), "FULL");
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		return parseRules(ruleText).get(0);
	}

	private static List<RuleTrs> parseRules(String... ruleTexts)
			throws IOException {

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new ArrayList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return rules;
	}

	private static final class TestUnfoldedRule extends UnfoldedRuleTrs {

		private boolean witness;
		private int eliminationCount;
		private List<String> calls = new ArrayList<>();
		private Collection<UnfoldedRuleTrs> eliminationResult = List.of();
		private Collection<UnfoldedRuleTrs> forwardResult = List.of();
		private Collection<UnfoldedRuleTrs> backwardResult = List.of();
		private CountDownLatch eliminationStarted;
		private CountDownLatch releaseElimination;

		private TestUnfoldedRule(Function left, Term right, int iteration,
				ParentTrs parent) {
			super(left, right, iteration, parent);
		}

		private static boolean addForTest(TestUnfoldedRule rule, Proof proof,
				LinkedList<UnfoldedRuleTrs> result) {

			return add(new Parameters(), emptyTrs(), new SimpleCycleRegistry(),
					proof, rule, result);
		}

		private void blockElimination(CountDownLatch started,
				CountDownLatch release) {

			this.eliminationStarted = started;
			this.releaseElimination = release;
		}

		@Override
		public TestUnfoldedRule deepCopy(int iteration, ParentTrs parent) {
			Map<Term, Term> copies = new HashMap<>();
			TestUnfoldedRule copy = new TestUnfoldedRule(
					(Function) this.left.deepCopy(copies),
					this.right.deepCopy(copies), iteration, parent);
			copy.witness = this.witness;
			return copy;
		}

		@Override
		public Argument nonTerminationTest() {
			if (!this.witness)
				return null;
			return new ArgumentLoopByUnfolding(
					this, true, new Position(), this.left,
					new Substitution(), new Substitution());
		}

		@Override
		public Collection<UnfoldedRuleTrs> elim(
				Parameters parameters, Trs trs,
				SimpleCycleRegistry simpleCycles) {
			this.eliminationCount++;
			if (this.eliminationStarted != null) {
				this.eliminationStarted.countDown();
				try {
					this.releaseElimination.await();
				}
				catch (InterruptedException e) {
					Thread.currentThread().interrupt();
					throw new IllegalStateException(
							"interrupted while characterizing elimination", e);
				}
			}
			return this.eliminationResult;
		}

		@Override
		public Collection<UnfoldedRuleTrs> unfoldForwardsWith(
				Parameters parameters, RuleTrs rule, Position position,
				int iteration) {
			this.calls.add("F:" + rule);
			return this.forwardResult;
		}

		@Override
		public Collection<UnfoldedRuleTrs> unfoldBackwardsWith(
				Parameters parameters, RuleTrs rule, Position position,
				int iteration) {
			this.calls.add("B:" + rule);
			return this.backwardResult;
		}
	}
}
