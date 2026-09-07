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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.dependencypair;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.PrimitiveIterator;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class DependencyPairTargetIndexTest {

	@Test
	@DisplayName("filter direct-argument conflicts and preserve wildcard targets")
	void filterDirectArgumentConflictsAndPreserveWildcardTargets()
			throws IOException {
		List<RuleTrs> targets = parseRules(
				"p(a(X), b(X)) -> X",
				"p(c(X), b(X)) -> X",
				"p(a(X), d(X)) -> X",
				"p(X, d(X)) -> X",
				"p(c(X), X) -> X",
				"p(X, Y) -> X",
				"p(X, X) -> X",
				"q(a(X), b(X)) -> X");
		DependencyPairTargetIndex index = new DependencyPairTargetIndex(
				new DependencyPairs(targets));

		assertEquals(
				List.of(targets.get(0), targets.get(5), targets.get(6)),
				toList(index, index.candidateSelectionFor(
						parseRight("r(X) -> p(a(X), b(X))")).indexes()));
	}

	@Test
	@DisplayName("constrain only functional pattern arguments and retain order")
	void constrainOnlyFunctionalPatternArgumentsAndRetainOrder()
			throws IOException {
		List<RuleTrs> targets = parseRules(
				"p(a(X), b(X)) -> X",
				"p(c(X), b(X)) -> X",
				"p(a(X), d(X)) -> X",
				"p(X, d(X)) -> X",
				"p(c(X), X) -> X",
				"p(X, Y) -> X",
				"p(X, X) -> X",
				"q(a(X), b(X)) -> X");
		DependencyPairTargetIndex index = new DependencyPairTargetIndex(
				new DependencyPairs(targets));

		assertEquals(
				List.of(
						targets.get(0), targets.get(1), targets.get(4),
						targets.get(5), targets.get(6)),
				toList(index, index.candidateSelectionFor(
						parseRight("r(X) -> p(X, b(X))")).indexes()));
		assertEquals(
				targets,
				toList(index, index.candidateSelectionFor(
						parseRight("r(X) -> X")).indexes()));
	}

	@Test
	@DisplayName("filter depth-two conflicts and retain ancestor wildcards")
	void filterDepthTwoConflictsAndRetainAncestorWildcards()
			throws IOException {
		List<RuleTrs> targets = parseRules(
				"p(a(b(X))) -> X",
				"p(a(c(X))) -> X",
				"p(a(X)) -> X",
				"p(X) -> X",
				"p(d(b(X))) -> X",
				"q(a(b(X))) -> X");
		DependencyPairTargetIndex index = new DependencyPairTargetIndex(
				new DependencyPairs(targets));

		assertEquals(
				List.of(targets.get(0), targets.get(2), targets.get(3)),
				toList(index, index.candidateSelectionFor(
						parseRight("r(X) -> p(a(b(X)))")).indexes()));
		assertEquals(
				List.of(
						targets.get(0), targets.get(1),
						targets.get(2), targets.get(3)),
				toList(index, index.candidateSelectionFor(
						parseRight("r(X) -> p(a(X))")).indexes()));
	}

	@Test
	@DisplayName("guarantee only candidates without rigid repeated-variable conflicts")
	void guaranteeOnlyCandidatesWithoutRigidRepeatedVariableConflicts()
			throws IOException {
		List<RuleTrs> targets = parseRules(
				"p(X, Y) -> X",
				"p(X, X) -> X",
				"q(a(b(d(X)))) -> X");
		DependencyPairTargetIndex index = new DependencyPairTargetIndex(
				new DependencyPairs(targets));
		Term coveredPattern = parseRight("r(X, Y) -> p(a(X), b(Y))");
		Term flexiblePattern = parseRight("r(X, Y) -> p(X, a(Y))");
		Term deeperPattern = parseRight("r(X) -> q(a(b(c(X))))");

		assertTrue(index.coversAllFunctionPositions(coveredPattern));
		DependencyPairTargetIndex.CandidateSelection coveredSelection =
				index.candidateSelectionFor(coveredPattern);
		assertTrue(coveredSelection.hasNoRepeatedVariableConflict(0));
		assertFalse(coveredSelection.hasNoRepeatedVariableConflict(1));
		assertEquals(
				List.of(targets.get(0), targets.get(1)),
				toList(index, coveredSelection.indexes()));
		assertFalse(destructiveUnifiability(
				coveredPattern, targets.get(1).getLeft()));

		DependencyPairTargetIndex.CandidateSelection flexibleSelection =
				index.candidateSelectionFor(flexiblePattern);
		assertTrue(flexibleSelection.hasNoRepeatedVariableConflict(1));
		assertTrue(destructiveUnifiability(
				flexiblePattern, targets.get(1).getLeft()));

		assertFalse(index.coversAllFunctionPositions(deeperPattern));
		assertEquals(
				List.of(targets.get(2)),
				toList(index,
						index.candidateSelectionFor(deeperPattern).indexes()));
		assertFalse(destructiveUnifiability(
				deeperPattern, targets.get(2).getLeft()));
		assertTrue(index.coversAllFunctionPositions(new Variable()));
	}

	@Test
	@DisplayName("guaranteed candidates agree with destructive unification")
	void guaranteedCandidatesAgreeWithDestructiveUnification() {
		FunctionSymbol unary = FunctionSymbol.intern(
				"target-index-guarantee-unary", 1);
		FunctionSymbol pair = FunctionSymbol.intern(
				"target-index-guarantee-pair", 2);
		FunctionSymbol root = FunctionSymbol.intern(
				"target-index-guarantee-root", 1);
		Function firstConstant = new Function(FunctionSymbol.intern(
				"target-index-guarantee-first", 0), List.of());
		Function secondConstant = new Function(FunctionSymbol.intern(
				"target-index-guarantee-second", 0), List.of());
		List<Term> smallTerms = smallTerms(
				2, unary, pair, firstConstant, secondConstant,
				new Variable(), new Variable());
		List<RuleTrs> targets = new ArrayList<>(smallTerms.size());
		for (Term target : smallTerms)
			targets.add(new RuleTrs(
					new Function(root, List.of(target)), firstConstant));
		DependencyPairTargetIndex index = new DependencyPairTargetIndex(
				new DependencyPairs(targets));
		Trs emptyTrs = new Trs("", List.of(), "FULL");

		for (Term sourceTemplate : smallTerms) {
			Term source = new Function(root, List.of(sourceTemplate))
					.buildConnectabilityPattern(emptyTrs);
			boolean fullyIndexed = index.coversAllFunctionPositions(source);
			DependencyPairTargetIndex.CandidateSelection selection =
					index.candidateSelectionFor(source);
			PrimitiveIterator.OfInt candidateIndexes =
					selection.indexes();
			while (candidateIndexes.hasNext()) {
				int targetIndex = candidateIndexes.nextInt();
				if (fullyIndexed &&
						selection.hasNoRepeatedVariableConflict(targetIndex))
					assertTrue(
							destructiveUnifiability(
									source, index.targetAt(targetIndex).getLeft()),
							() -> source + " and " +
									index.targetAt(targetIndex).getLeft());
			}
		}
	}

	private static List<RuleTrs> toList(
			DependencyPairTargetIndex index,
			PrimitiveIterator.OfInt targetIndexes) {
		List<RuleTrs> result = new ArrayList<>();
		while (targetIndexes.hasNext())
			result.add(index.targetAt(targetIndexes.nextInt()));
		return result;
	}

	private static Term parseRight(String ruleText) throws IOException {
		return parseRules(ruleText).get(0).getRight();
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

	private static boolean destructiveUnifiability(Term source, Term target) {
		Map<Term, Term> copies = new HashMap<>();
		return source.deepCopy(copies).unifyWith(target.deepCopy(copies));
	}

	private static List<Term> smallTerms(
			int depth,
			FunctionSymbol unary,
			FunctionSymbol pair,
			Term firstConstant,
			Term secondConstant,
			Variable firstVariable,
			Variable secondVariable) {
		if (depth == 0)
			return new ArrayList<>(List.of(
					firstVariable, secondVariable,
					firstConstant, secondConstant));

		List<Term> children = smallTerms(
				depth - 1, unary, pair,
				firstConstant, secondConstant,
				firstVariable, secondVariable);
		List<Term> terms = new ArrayList<>(children);
		for (Term child : children)
			terms.add(new Function(unary, List.of(child)));
		for (Term left : children)
			for (Term right : children)
				terms.add(new Function(pair, List.of(left, right)));
		return terms;
	}
}
