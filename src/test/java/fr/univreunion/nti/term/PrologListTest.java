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

package fr.univreunion.nti.term;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.reducpair.LexOrder;
import fr.univreunion.nti.program.trs.reducpair.PolyInterpretation;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.leftunif.LuEquation;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;

class PrologListTest {
	private static final int HEAD_INDEX = 0;
	private static final int TAIL_INDEX = 1;

	@Test
	@DisplayName("reuse and render the empty Prolog list singleton")
	void reuseAndRenderEmptyPrologListSingleton() {
		PrologList empty = PrologList.emptyPrologList();

		assertSame(empty, PrologList.emptyPrologList());
		assertSame(PrologList.PROLOG_LIST_ROOT_SYMBOL, empty.getRootSymbol());
		assertEquals("[]", empty.toString());
		assertNull(empty.get(0));
		assertNull(empty.get(1));
		assertSame(empty, empty.shallowCopy());
		assertSame(empty, empty.deepCopy());
	}

	@Test
	@DisplayName("validate non-empty Prolog list construction")
	void validateNonEmptyPrologListConstruction() {
		Variable element = new Variable();

		assertThrows(NullPointerException.class,
				() -> new PrologList(null));
		assertThrows(NoSuchElementException.class,
				() -> new PrologList(List.of()));
		assertThrows(NullPointerException.class,
				() -> new PrologList(new ArrayList<>(List.of(element)), null));

		List<Term> nullElement = new ArrayList<>();
		nullElement.add(null);
		assertThrows(NullPointerException.class,
				() -> new PrologList(nullElement));

		List<Term> laterNullElement = new ArrayList<>();
		laterNullElement.add(element);
		laterNullElement.add(null);
		assertThrows(NullPointerException.class,
				() -> new PrologList(laterNullElement));
	}

	@Test
	@DisplayName("render proper and improper lists with accessible head and tail")
	void renderProperAndImproperListsWithAccessibleHeadAndTail() {
		Function first = constant("prolog-list-first");
		Function second = constant("prolog-list-second");
		Variable suffix = new Variable();
		Map<Variable, String> names = new HashMap<>();
		names.put(suffix, "Tail");
		PrologList proper = new PrologList(List.of(first, second));
		PrologList improper = new PrologList(List.of(first, second), suffix);

		assertEquals("[" + first + "," + second + "]", proper.toString());
		assertEquals("[" + first + "," + second + "|Tail]",
				improper.toString(names, false));
		assertSame(first, proper.get(0));
		assertTrue(proper.get(1) instanceof PrologList);
		PrologList secondNode = (PrologList) proper.get(1);
		assertSame(second, secondNode.get(0));
		assertSame(PrologList.emptyPrologList(), secondNode.get(1));
		assertNull(proper.get(-1));
		assertNull(proper.get(2));
	}

	@Test
	@DisplayName("distinguish shallow deep and schema-resolved list copies")
	void distinguishShallowDeepAndSchemaResolvedListCopies() {
		Variable repeatedVariable = new Variable();
		Variable suffix = new Variable();
		PrologList source = new PrologList(
				List.of(repeatedVariable, repeatedVariable), suffix);

		PrologList shallow = (PrologList) source.shallowCopy();
		PrologList deep = (PrologList) source.deepCopy();
		PrologList shallowTail = (PrologList) shallow.get(1);
		PrologList deepTail = (PrologList) deep.get(1);

		assertNotSame(source, shallow);
		assertSame(repeatedVariable, shallow.get(0));
		assertSame(repeatedVariable, shallowTail.get(0));
		assertSame(suffix, shallowTail.get(1));
		assertNotSame(source, deep);
		assertNotSame(repeatedVariable, deep.get(0));
		assertSame(deep.get(0), deepTail.get(0));
		assertNotSame(suffix, deepTail.get(1));

		assertTrue(suffix.unifyWith(PrologList.emptyPrologList()));
		assertEquals("[_0,_0]", source.toString());
		Map<Variable, String> names = new HashMap<>();
		names.put(repeatedVariable, "X");
		names.put(suffix, "StoredTail");
		assertEquals("[X|[X|StoredTail]]", source.toString(names, true));
		assertEquals("[X,X]", source.toString(names, false));
	}

	@Test
	@DisplayName("compare empty, proper and improper lists structurally")
	void compareEmptyProperAndImproperListsStructurally() {
		Variable repeated = new Variable();
		Variable suffix = new Variable();
		Function constant = constant("prolog-list-equality");
		PrologList first = new PrologList(List.of(repeated, constant));
		PrologList equal = new PrologList(List.of(repeated, constant));
		PrologList distinctVariable = new PrologList(
				List.of(new Variable(), constant));
		PrologList improper = new PrologList(
				List.of(repeated, constant), suffix);

		assertTrue(PrologList.emptyPrologList().deepEquals(
				PrologList.emptyPrologList()));
		assertFalse(PrologList.emptyPrologList().deepEquals(first));
		assertTrue(first.deepEquals(equal));
		assertTrue(first.deepEquals(equal));
		assertFalse(first.deepEquals(distinctVariable));
		assertFalse(first.deepEquals(improper));

		assertTrue(suffix.unifyWith(PrologList.emptyPrologList()));
		assertTrue(first.deepEquals(improper));
	}

	@Test
	@DisplayName("find exact and schema-reachable terms in list nodes")
	void findExactAndSchemaReachableTermsInListNodes() {
		Variable schemaArgument = new Variable();
		Function schema = new Function(
				FunctionSymbol.intern(
						"prolog-list-schema-" + UUID.randomUUID(), 1),
				List.of(schemaArgument));
		Variable storedVariable = new Variable();
		storedVariable.union(schema);
		Function second = constant("prolog-list-contained");
		PrologList list = new PrologList(List.of(storedVariable, second));
		Term tail = list.get(1);

		assertTrue(list.contains(list));
		assertTrue(list.contains(schema));
		assertTrue(list.contains(schemaArgument));
		assertTrue(list.contains(second));
		assertTrue(list.contains(tail));
		assertTrue(list.contains(PrologList.emptyPrologList()));
		assertFalse(list.contains(storedVariable));
		assertFalse(list.contains(new Variable()));
	}

	@Test
	@DisplayName("collect list variables, occurrences and function symbols")
	void collectListVariablesOccurrencesAndFunctionSymbols() {
		Variable repeated = new Variable();
		Variable schemaVariable = new Variable();
		FunctionSymbol schemaSymbol = FunctionSymbol.intern(
				"prolog-list-query-schema-" + UUID.randomUUID(), 0);
		schemaVariable.union(new Function(schemaSymbol, List.of()));
		PrologList list = new PrologList(
				List.of(repeated, repeated), schemaVariable);
		Map<Variable, Integer> occurrences = new HashMap<>();

		assertFalse(list.isGround());
		assertEquals(Set.of(repeated), list.getVariables());
		list.getVariableOccurrences(occurrences);
		assertEquals(Map.of(repeated, 2), occurrences);
		assertEquals(
				Set.of(PrologList.PROLOG_LIST_ROOT_SYMBOL, schemaSymbol),
				list.getFunSymbols());
		assertTrue(new PrologList(List.of(constant("prolog-list-ground")))
				.isGround());
		assertTrue(PrologList.emptyPrologList().isGround());
		assertEquals(Set.of(PrologList.PROLOG_LIST_ROOT_SYMBOL),
				PrologList.emptyPrologList().getFunSymbols());
	}

	@Test
	@DisplayName("collect deepest distinct hat subterms in list order")
	void collectDeepestDistinctHatSubtermsInListOrder() {
		HatFunctionSymbol firstSymbol = hatSymbol("prolog-list-first-hat");
		HatFunctionSymbol secondSymbol = hatSymbol("prolog-list-second-hat");
		Variable sharedArgument = new Variable();
		HatFunction first = new HatFunction(
				firstSymbol, sharedArgument, List.of(2, 3));
		HatFunction duplicate = new HatFunction(
				firstSymbol, sharedArgument, List.of(0, 2, 3));
		HatFunction second = new HatFunction(
				secondSymbol, new Variable(), List.of(4, 5));
		PrologList list = new PrologList(List.of(first, duplicate, second));

		assertEquals(List.of(first, second),
				new ArrayList<>(list.getHatSubterms()));
		assertTrue(PrologList.emptyPrologList().getHatSubterms().isEmpty());
		assertTrue(list.containsHatSubterm());
		assertFalse(PrologList.emptyPrologList().containsHatSubterm());
	}

	@Test
	@DisplayName("look up only direct list children while preserving stored terms")
	void lookUpOnlyDirectListChildrenWhilePreservingStoredTerms() {
		Variable storedHead = new Variable();
		Function schema = constant("prolog-list-lookup-schema");
		storedHead.union(schema);
		Variable storedSuffix = new Variable();
		PrologList list = new PrologList(List.of(storedHead), storedSuffix);

		assertSame(storedHead, list.get(0));
		assertSame(storedSuffix, list.get(1));
		assertNull(list.get(-1));
		assertNull(list.get(2));
		assertNull(PrologList.emptyPrologList().get(0));
		assertNull(PrologList.emptyPrologList().get(1));
	}

	@Test
	@DisplayName("look up and iterate over deep and shallow list positions")
	void lookUpAndIterateOverDeepAndShallowListPositions() {
		Variable nestedArgument = new Variable();
		Function head = new Function(
				FunctionSymbol.intern("prolog-list-position-head", 1),
				List.of(nestedArgument));
		Variable storedSuffix = new Variable();
		Variable suffixArgument = new Variable();
		Function suffixSchema = new Function(
				FunctionSymbol.intern("prolog-list-position-suffix", 1),
				List.of(suffixArgument));
		storedSuffix.union(suffixSchema);
		PrologList list = new PrologList(List.of(head), storedSuffix);
		PrologList empty = PrologList.emptyPrologList();
		Position headPosition = new Position(HEAD_INDEX);
		Position nestedHeadPosition = headPosition.addLast(0);
		Position tailPosition = new Position(TAIL_INDEX);
		Position nestedTailPosition = tailPosition.addLast(0);

		assertSame(list, list.get(new Position()));
		assertSame(list, list.get(new Position(), true));
		assertSame(empty, empty.get(new Position()));
		assertSame(empty, empty.get(new Position(), true));
		assertSame(head, list.get(headPosition));
		assertSame(nestedArgument, list.get(nestedHeadPosition));
		assertSame(suffixSchema, list.get(tailPosition));
		assertSame(storedSuffix, list.get(tailPosition, true));
		assertSame(suffixArgument, list.get(nestedTailPosition));
		assertNull(list.get(nestedTailPosition, true));
		assertNull(list.get(new Position(-1)));
		assertNull(list.get(new Position(2)));
		assertNull(empty.get(new Position(HEAD_INDEX)));

		assertEquals(
				List.of("root", "[0]", "[0, 0]", "[1]", "[1, 0]"),
				positionLabels(list.iterator()));
		assertEquals(
				List.of("root", "[0]", "[0, 0]", "[1]"),
				positionLabels(list.shallowIterator()));
		assertEquals(List.of("root"), positionLabels(empty.iterator()));
		assertEquals(List.of("root"), positionLabels(empty.shallowIterator()));
	}

	@Test
	@DisplayName("keep list iterator state stable after exhaustion")
	void exhaustListPositionIterator() {
		Iterator<Position> positions =
				PrologList.emptyPrologList().iterator();

		assertTrue(positions.hasNext());
		assertTrue(positions.hasNext());
		assertTrue(positions.next().isEmpty());
		assertFalse(positions.hasNext());
		assertFalse(positions.hasNext());
		assertThrows(NoSuchElementException.class, positions::next);
		assertThrows(NoSuchElementException.class, positions::next);
		assertThrows(UnsupportedOperationException.class, positions::remove);
	}

	@Test
	@DisplayName("report every list disagreement only at the root")
	void reportEveryListDisagreementOnlyAtTheRoot() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		PrologList first = new PrologList(List.of(firstVariable));
		PrologList second = new PrologList(List.of(secondVariable));

		assertTrue(first.dpos(first, false).isEmpty());
		assertTrue(first.dpos(
				new PrologList(List.of(firstVariable)), false).isEmpty());
		assertSingleRootPosition(first.dpos(second, false));
		assertSingleRootPosition(first.dpos(second, true));
		assertSingleRootPosition(first.dpos(constant("prolog-list-dpos"), true));
		assertSingleRootPosition(PrologList.emptyPrologList().dpos(first, false));
	}

	@Test
	@DisplayName("replace list roots and nested subterms without source mutation")
	void replaceListRootsAndNestedSubtermsWithoutSourceMutation() {
		Variable nestedVariable = new Variable();
		Function nestedHead = new Function(
				FunctionSymbol.intern("prolog-list-replaced-head", 1),
				List.of(nestedVariable));
		Variable suffix = new Variable();
		PrologList list = new PrologList(List.of(nestedHead), suffix);
		Variable storedReplacement = new Variable();
		Function replacementSchema = constant("prolog-list-replacement");
		storedReplacement.union(replacementSchema);

		assertSame(replacementSchema,
				list.replace(new Position(), storedReplacement));

		PrologList replaced = (PrologList) list.replace(
				new Position(HEAD_INDEX).addLast(0),
				replacementSchema);
		Function copiedHead = (Function) replaced.get(HEAD_INDEX);
		assertNotSame(nestedHead, copiedHead);
		assertSame(replacementSchema, copiedHead.getChild(0));
		assertSame(suffix, replaced.get(TAIL_INDEX));
		assertSame(nestedVariable, nestedHead.getChild(0));

		PrologList tailReplaced = (PrologList) list.replace(
				new Position(TAIL_INDEX), replacementSchema);
		assertSame(replacementSchema, tailReplaced.get(TAIL_INDEX));
		assertNotSame(nestedHead, tailReplaced.get(HEAD_INDEX));
		assertSame(nestedVariable,
				((Function) tailReplaced.get(HEAD_INDEX)).getChild(0));

		assertThrows(IndexOutOfBoundsException.class,
				() -> list.replace(new Position(-1), replacementSchema));
		assertThrows(IndexOutOfBoundsException.class,
				() -> list.replace(new Position(2), replacementSchema));
		assertThrows(IndexOutOfBoundsException.class,
				() -> PrologList.emptyPrologList().replace(
						new Position(HEAD_INDEX), replacementSchema));
	}

	@Test
	@DisplayName("replace list variables recursively without mutating the source")
	void replaceListVariablesRecursivelyWithoutMutatingTheSource() {
		Variable firstVariable = new Variable();
		Variable suffixVariable = new Variable();
		PrologList source = new PrologList(
				List.of(firstVariable, firstVariable), suffixVariable);
		Function replacement = constant("prolog-list-variable-replacement");

		PrologList result = (PrologList) source.replaceVariables(replacement);
		PrologList resultTail = (PrologList) result.get(1);

		assertNotSame(source, result);
		assertSame(replacement, result.get(0));
		assertSame(replacement, resultTail.get(0));
		assertSame(replacement, resultTail.get(1));
		assertSame(firstVariable, source.get(0));
		assertSame(suffixVariable, ((PrologList) source.get(1)).get(1));
		assertSame(PrologList.emptyPrologList(),
				PrologList.emptyPrologList().replaceVariables(replacement));
	}

	@Test
	@DisplayName("match list heads then tails while retaining partial bindings")
	void matchListHeadsThenTailsWhileRetainingPartialBindings() {
		Variable repeated = new Variable();
		Variable suffix = new Variable();
		PrologList pattern = new PrologList(List.of(repeated), suffix);
		Function targetElement = constant("prolog-list-match-target");
		PrologList target = new PrologList(List.of(targetElement));
		Substitution matcher = new Substitution();

		assertTrue(pattern.isMoreGeneralThan(target, matcher));
		assertSame(targetElement, matcher.get(repeated));
		assertSame(PrologList.emptyPrologList(), matcher.get(suffix));
		assertTrue(pattern.isMoreGeneralThan(target));
		assertFalse(target.isMoreGeneralThan(pattern));

		Variable conflictingRepeated = new Variable();
		PrologList conflictingPattern = new PrologList(
				List.of(conflictingRepeated, conflictingRepeated));
		Function firstTarget = constant("prolog-list-match-first");
		Function conflictingTarget = constant("prolog-list-match-conflict");
		Substitution partialMatcher = new Substitution();

		assertFalse(conflictingPattern.isMoreGeneralThan(
				new PrologList(List.of(firstTarget, conflictingTarget)),
				partialMatcher));
		assertSame(firstTarget, partialMatcher.get(conflictingRepeated));
		assertFalse(PrologList.emptyPrologList().isMoreGeneralThan(target));
	}

	@Test
	@DisplayName("unify empty and non-empty lists with their distinct contracts")
	void unifyEmptyAndNonEmptyListsWithTheirDistinctContracts() {
		PrologList empty = PrologList.emptyPrologList();
		PrologList nonEmpty = new PrologList(
				List.of(constant("prolog-list-unification-element")));

		assertTrue(empty.unifyWith(empty));
		assertFalse(empty.unifyWith(nonEmpty));
		assertFalse(nonEmpty.unifyWith(empty));

		Variable variable = new Variable();
		PrologList target = new PrologList(
				List.of(constant("prolog-list-variable-target")));
		Substitution mgu = new Substitution();

		assertTrue(target.unifyWith(variable, mgu));
		assertTrue(variable.deepEquals(target));
		assertSame(target.findSchema(), mgu.get(variable));
	}

	@Test
	@DisplayName("unify improper and proper lists and extract their solution")
	void unifyImproperAndProperListsAndExtractTheirSolution() {
		Variable headVariable = new Variable();
		Variable suffixVariable = new Variable();
		PrologList improper = new PrologList(
				List.of(headVariable), suffixVariable);
		Function targetElement = constant("prolog-list-unification-target");
		PrologList proper = new PrologList(List.of(targetElement));
		Substitution mgu = new Substitution();

		assertTrue(improper.unifyWith(proper, mgu));
		assertTrue(improper.deepEquals(proper));
		assertSame(targetElement.findSchema(), mgu.get(headVariable));
		assertTrue(suffixVariable.deepEquals(PrologList.emptyPrologList()));

		Variable withoutExtraction = new Variable();
		assertTrue(new PrologList(List.of(withoutExtraction)).unifyWith(
				new PrologList(List.of(targetElement))));
		assertTrue(withoutExtraction.deepEquals(targetElement));
	}

	@Test
	@DisplayName("retain head unification mutations after a tail conflict")
	void retainHeadUnificationMutationsAfterTailConflict() {
		Variable repeated = new Variable();
		Function firstTarget = constant("prolog-list-unification-first");
		Function conflictingTarget = constant("prolog-list-unification-conflict");
		PrologList pattern = new PrologList(List.of(repeated, repeated));
		PrologList target = new PrologList(
				List.of(firstTarget, conflictingTarget));
		Substitution partialMgu = new Substitution();

		assertFalse(pattern.unifyWith(target, partialMgu));
		assertTrue(repeated.deepEquals(firstTarget));
		assertTrue(pattern.deepEquals(target));
		assertNull(partialMgu.get(repeated));
	}

	@Test
	@DisplayName("apply substitutions functionally across list heads and tails")
	void applySubstitutionsFunctionallyAcrossListHeadsAndTails() {
		Variable repeated = new Variable();
		Variable suffix = new Variable();
		Variable mappedArgument = new Variable();
		Function mapped = new Function(
				FunctionSymbol.intern(
						"prolog-list-application-" + UUID.randomUUID(), 1),
				List.of(mappedArgument));
		PrologList source = new PrologList(List.of(repeated, repeated), suffix);
		Substitution substitution = new Substitution();
		substitution.add(repeated, mapped);
		substitution.add(suffix, PrologList.emptyPrologList());

		PrologList applied = (PrologList) source.apply(substitution);
		Function appliedFirst = (Function) applied.get(0);
		PrologList appliedTail = (PrologList) applied.get(1);
		Function appliedSecond = (Function) appliedTail.get(0);

		assertNotSame(source, applied);
		assertNotSame(mapped, appliedFirst);
		assertNotSame(mapped, appliedSecond);
		assertNotSame(appliedFirst, appliedSecond);
		assertSame(mapped.getRootSymbol(), appliedFirst.getRootSymbol());
		assertSame(mappedArgument, appliedFirst.getChild(0));
		assertSame(mappedArgument, appliedSecond.getChild(0));
		assertSame(PrologList.emptyPrologList(), appliedTail.get(1));
		assertSame(repeated, source.get(0));
		assertSame(suffix, ((PrologList) source.get(1)).get(1));
		assertSame(PrologList.emptyPrologList(),
				PrologList.emptyPrologList().apply(substitution));
		assertThrows(UnsupportedOperationException.class,
				() -> source.applyInPlace(substitution));
	}

	@Test
	@DisplayName("reject list left-unification transformations without mutation")
	void rejectListLeftUnificationTransformationsWithoutMutation() {
		Variable element = new Variable();
		PrologList list = new PrologList(List.of(element));
		Variable mappedVariable = new Variable();
		Function mappedTerm = constant("prolog-list-left-unification-mapped");
		Substitution rho = new Substitution();
		rho.add(mappedVariable, mappedTerm);
		LuEquation equation = new LuEquation(new Variable(), new Variable());
		String originalRendering = list.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> list.distribute(2));
		assertThrows(UnsupportedOperationException.class,
				() -> list.reduceWithLeftUnificationRule(equation));
		assertThrows(UnsupportedOperationException.class,
				() -> list.applyAndCompleteRho(rho));
		assertEquals(originalRendering, list.toString());
		assertSame(element, list.get(0));
		assertSame(mappedTerm, rho.get(mappedVariable));
	}

	@Test
	@DisplayName("reject inner list rewriting after inspecting root rules")
	void rejectInnerListRewritingAfterInspectingRootRules() {
		Variable element = new Variable();
		PrologList list = new PrologList(List.of(element));
		Variable ruleVariable = new Variable();
		Function ruleLeft = new Function(
				FunctionSymbol.intern(
						"prolog-list-rewriting-left-" + UUID.randomUUID(), 1),
				List.of(ruleVariable));
		Function ruleRight = new Function(
				FunctionSymbol.intern(
						"prolog-list-rewriting-right-" + UUID.randomUUID(), 1),
				List.of(ruleVariable));
		RuleTrs rule = new RuleTrs(ruleLeft, ruleRight);
		Trs trs = new Trs("prolog-list-rewriting", List.of(rule), "FULL");
		String listRendering = list.toString();
		String ruleRendering = rule.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> list.rewriteWith(trs));
		assertEquals(listRendering, list.toString());
		assertEquals(ruleRendering, rule.toString());
		assertSame(element, list.get(0));
		assertSame(ruleLeft, rule.getLeft());
		assertSame(ruleRight, rule.getRight());
	}

	@Test
	@DisplayName("distinguish root list unfolding results from inner rejection")
	void distinguishRootListUnfoldingResultsFromInnerRejection() {
		Variable element = new Variable();
		PrologList list = new PrologList(List.of(element));
		Variable ruleVariable = new Variable();
		Function ruleLeft = new Function(
				FunctionSymbol.intern(
						"prolog-list-unfolding-left-" + UUID.randomUUID(), 1),
				List.of(ruleVariable));
		Function ruleRight = constant("prolog-list-unfolding-right");
		RuleTrs rule = new RuleTrs(ruleLeft, ruleRight);
		Map<Term, Term> forwardCopies = new HashMap<>();
		Map<Term, Term> backwardCopies = new HashMap<>();
		Map<Term, Term> innerCopies = new HashMap<>();
		Variable sentinel = new Variable();
		innerCopies.put(sentinel, sentinel);
		String listRendering = list.toString();
		String ruleRendering = rule.toString();

		assertNull(list.unfoldWith(
				rule, new Position(), false, false, forwardCopies));
		assertTrue(forwardCopies.containsKey(element));
		assertNotSame(element, forwardCopies.get(element));

		RuleTrs variableRightRule = new RuleTrs(ruleLeft, new Variable());
		Term backwardResult = list.unfoldWith(
				variableRightRule, new Position(), true, false, backwardCopies);
		assertTrue(backwardResult instanceof Function);
		assertSame(ruleLeft.getRootSymbol(), backwardResult.getRootSymbol());
		assertNotSame(ruleLeft, backwardResult);
		assertTrue(backwardCopies.containsKey(element));

		assertThrows(UnsupportedOperationException.class,
				() -> list.unfoldWith(
						rule, new Position(0), true, true, innerCopies));
		assertEquals(1, innerCopies.size());
		assertSame(sentinel, innerCopies.get(sentinel));
		assertEquals(listRendering, list.toString());
		assertEquals(ruleRendering, rule.toString());
		assertSame(element, list.get(0));
	}

	@Test
	@DisplayName("reject unsupported list metrics interpretations and conversions")
	void rejectUnsupportedListMetricsInterpretationsAndConversions() {
		Variable element = new Variable();
		PrologList list = new PrologList(List.of(element));
		PrologList distinct = new PrologList(List.of(new Variable()));
		PolyInterpretation interpretation = new PolyInterpretation();
		WeightFunction weights = new WeightFunction();
		Trs emptyTrs = new Trs("prolog-list-connectability", List.of(), "FULL");
		String originalRendering = list.toString();

		assertThrows(UnsupportedOperationException.class, list::depth);
		assertThrows(UnsupportedOperationException.class, list::maxArity);
		assertTrue(list.embeds(list));
		assertThrows(UnsupportedOperationException.class,
				() -> list.embeds(distinct));
		assertThrows(UnsupportedOperationException.class,
				() -> list.isConnectableTo(new Variable(), emptyTrs));
		assertThrows(UnsupportedOperationException.class,
				() -> list.toPolynomial(interpretation));
		assertThrows(UnsupportedOperationException.class,
				() -> list.generateKBOWeights(weights));
		assertThrows(UnsupportedOperationException.class,
				() -> list.getWeight(weights));
		assertThrows(UnsupportedOperationException.class, list::toTuple);
		assertThrows(UnsupportedOperationException.class, list::toFunction);
		assertTrue(interpretation.getAllCoefficients().isEmpty());
		assertTrue(weights.getAllCoefficients().isEmpty());
		assertEquals(originalRendering, list.toString());
		assertSame(element, list.get(0));
	}

	@Test
	@DisplayName("preserve equal-list order fast paths and reject strict comparisons")
	void preserveEqualListOrderFastPathsAndRejectStrictComparisons() {
		Variable sharedElement = new Variable();
		PrologList list = new PrologList(List.of(sharedElement));
		PrologList equivalent = new PrologList(List.of(sharedElement));
		PrologList distinct = new PrologList(
				List.of(constant("prolog-list-order-distinct")));
		LexOrder order = new LexOrder();
		WeightFunction weights = new WeightFunction();
		String orderRendering = order.toString();

		assertTrue(list.completeLPO(order, equivalent));
		assertThrows(UnsupportedOperationException.class,
				() -> list.completeLPOStrict(order, distinct));
		assertTrue(list.completeKBO(order, weights, equivalent));
		assertThrows(UnsupportedOperationException.class,
				() -> list.completeKBOStrict(order, weights, distinct));
		assertEquals(orderRendering, order.toString());
		assertTrue(weights.getAllCoefficients().isEmpty());
		assertSame(sharedElement, list.get(0));
	}

	@Test
	@DisplayName("reject list argument filtering before collaborator mutation")
	void rejectListArgumentFilteringBeforeCollaboratorMutation() {
		Variable element = new Variable();
		PrologList list = new PrologList(List.of(element));
		ArgFiltering filtering = new ArgFiltering();

		assertThrows(UnsupportedOperationException.class,
				() -> list.buildFilters(filtering));
		assertThrows(UnsupportedOperationException.class,
				() -> list.applyFilters(filtering));
		assertTrue(filtering.getAllFilters().isEmpty());
		assertSame(element, list.get(0));
	}

	@Test
	@DisplayName("render stored and schema-resolved list tails with stable names")
	void renderStoredAndSchemaResolvedListTailsWithStableNames() {
		Variable head = new Variable();
		Variable storedTail = new Variable();
		Variable resolvedElement = new Variable();
		PrologList source = new PrologList(List.of(head), storedTail);
		PrologList resolvedTail = new PrologList(List.of(resolvedElement));
		Map<Variable, String> names = new HashMap<>();
		names.put(head, "Head");
		names.put(storedTail, "StoredTail");
		names.put(resolvedElement, "Resolved");

		assertEquals("[Head|StoredTail]", source.toString(names, true));
		assertEquals("[Head|StoredTail]", source.toString(names, false));

		assertTrue(storedTail.unifyWith(resolvedTail));
		assertEquals("[Head|StoredTail]", source.toString(names, true));
		assertEquals("[Head,Resolved]", source.toString(names, false));
		assertEquals("[]", PrologList.emptyPrologList().toString(names, true));
		assertEquals("[]", PrologList.emptyPrologList().toString(names, false));
	}

	private static void assertSingleRootPosition(
			Iterable<Position> positions) {

		List<Position> collected = new ArrayList<>();
		positions.forEach(collected::add);
		assertEquals(1, collected.size());
		assertTrue(collected.getFirst().isEmpty());
	}

	private static List<String> positionLabels(Iterator<Position> positions) {
		List<String> labels = new ArrayList<>();
		while (positions.hasNext()) {
			Position position = positions.next();
			labels.add(position.isEmpty() ? "root" : position.toString());
		}
		return labels;
	}

	private static Function constant(String prefix) {
		return new Function(
				FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), 0),
				List.of());
	}

	private static HatFunctionSymbol hatSymbol(String prefix) {
		Variable contextVariable = new Variable();
		Function context = new Function(
				FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), 1),
				List.of(contextVariable));
		return HatFunctionSymbol.intern(context, contextVariable);
	}
}
