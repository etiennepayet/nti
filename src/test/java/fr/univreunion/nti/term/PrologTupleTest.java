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
import java.util.List;
import java.util.Map;
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

class PrologTupleTest {

	@Test
	@DisplayName("validate tuple construction while accepting one element")
	void validateTupleConstructionWhileAcceptingOneElement() {
		Variable element = new Variable();

		assertThrows(NullPointerException.class,
				() -> new PrologTuple(null));
		assertThrows(IllegalArgumentException.class,
				() -> new PrologTuple(List.of()));

		List<Term> nullElement = new ArrayList<>();
		nullElement.add(null);
		assertThrows(NullPointerException.class,
				() -> new PrologTuple(nullElement));

		PrologTuple singleton = new PrologTuple(List.of(element));
		assertSame(PrologTuple.PROLOG_TUPLE_ROOT_SYMBOL,
				singleton.getRootSymbol());
		assertSame(element, singleton.get(0));
		assertNull(singleton.get(-1));
		assertNull(singleton.get(1));
		assertEquals("(_0)", singleton.toString());
	}

	@Test
	@DisplayName("flatten nested tuples while preserving element identity and order")
	void flattenNestedTuplesWhilePreservingElementIdentityAndOrder() {
		Function first = constant("prolog-tuple-first");
		Variable second = new Variable();
		Function third = constant("prolog-tuple-third");
		PrologTuple nested = new PrologTuple(List.of(second, third));
		PrologTuple tuple = new PrologTuple(List.of(first, nested));
		Map<Variable, String> names = new HashMap<>();
		names.put(second, "Second");

		assertSame(first, tuple.get(0));
		assertSame(second, tuple.get(1));
		assertSame(third, tuple.get(2));
		assertNull(tuple.get(3));
		assertEquals("(" + first + ",Second," + third + ")",
				tuple.toString(names, false));
	}

	@Test
	@DisplayName("distinguish shallow and deep tuple variable copies")
	void distinguishShallowAndDeepTupleVariableCopies() {
		Variable repeated = new Variable();
		Variable preserved = new Variable();
		PrologTuple source = new PrologTuple(
				List.of(repeated, repeated, preserved));

		PrologTuple shallow = (PrologTuple) source.shallowCopy();
		PrologTuple deep = (PrologTuple) source.deepCopy();
		PrologTuple selective = (PrologTuple) source.deepCopy(Set.of(repeated));

		assertNotSame(source, shallow);
		assertSame(repeated, shallow.get(0));
		assertSame(repeated, shallow.get(1));
		assertSame(preserved, shallow.get(2));
		assertNotSame(repeated, deep.get(0));
		assertSame(deep.get(0), deep.get(1));
		assertNotSame(preserved, deep.get(2));
		assertNotSame(repeated, selective.get(0));
		assertSame(selective.get(0), selective.get(1));
		assertSame(preserved, selective.get(2));
	}

	@Test
	@DisplayName("resolve element schemas in copies and deep rendering")
	void resolveElementSchemasInCopiesAndDeepRendering() {
		Variable storedVariable = new Variable();
		Variable schemaArgument = new Variable();
		Function schema = new Function(
				FunctionSymbol.intern(
						"prolog-tuple-schema-" + UUID.randomUUID(), 1),
				List.of(schemaArgument));
		PrologTuple source = new PrologTuple(List.of(storedVariable));
		Map<Variable, String> names = new HashMap<>();
		names.put(storedVariable, "Stored");
		names.put(schemaArgument, "Argument");

		assertTrue(storedVariable.unifyWith(schema));
		assertEquals("(Stored)", source.toString(names, true));
		assertEquals("(" + schema.getRootSymbol() + "(Argument))",
				source.toString(names, false));

		PrologTuple shallow = (PrologTuple) source.shallowCopy();
		PrologTuple deep = (PrologTuple) source.deepCopy();
		assertTrue(shallow.get(0) instanceof Function);
		assertNotSame(schema, shallow.get(0));
		assertSame(schemaArgument, ((Function) shallow.get(0)).getChild(0));
		assertTrue(deep.get(0) instanceof Function);
		assertNotSame(schemaArgument, ((Function) deep.get(0)).getChild(0));
		assertSame(storedVariable, source.get(0));
	}

	@Test
	@DisplayName("compare tuple arity order and variable identity structurally")
	void compareTupleArityOrderAndVariableIdentityStructurally() {
		Variable variable = new Variable();
		Function constant = constant("prolog-tuple-equality");
		PrologTuple tuple = new PrologTuple(List.of(variable, constant));

		assertTrue(tuple.deepEquals(tuple));
		assertTrue(tuple.deepEquals(new PrologTuple(List.of(variable, constant))));
		assertTrue(tuple.deepEquals(new PrologTuple(List.of(variable, constant))));
		assertFalse(tuple.deepEquals(new PrologTuple(
				List.of(new Variable(), constant))));
		assertFalse(tuple.deepEquals(new PrologTuple(List.of(constant, variable))));
		assertFalse(tuple.deepEquals(new PrologTuple(List.of(variable))));
		assertFalse(tuple.deepEquals(constant));
	}

	@Test
	@DisplayName("follow tuple schemas in containment and structural queries")
	void followTupleSchemasInContainmentAndStructuralQueries() {
		Variable repeated = new Variable();
		Variable schemaArgument = new Variable();
		FunctionSymbol schemaSymbol = FunctionSymbol.intern(
				"prolog-tuple-query-schema-" + UUID.randomUUID(), 1);
		Function schema = new Function(schemaSymbol, List.of(schemaArgument));
		Variable storedVariable = new Variable();
		storedVariable.union(schema);
		PrologTuple tuple = new PrologTuple(
				List.of(repeated, repeated, storedVariable));
		Map<Variable, Integer> occurrences = new HashMap<>();

		assertTrue(tuple.contains(tuple));
		assertTrue(tuple.contains(repeated));
		assertTrue(tuple.contains(schema));
		assertTrue(tuple.contains(schemaArgument));
		assertFalse(tuple.contains(storedVariable));
		assertFalse(tuple.isGround());
		assertEquals(Set.of(repeated, schemaArgument), tuple.getVariables());
		tuple.getVariableOccurrences(occurrences);
		assertEquals(Map.of(repeated, 2, schemaArgument, 1), occurrences);
		assertEquals(Set.of(
				PrologTuple.PROLOG_TUPLE_ROOT_SYMBOL, schemaSymbol),
				tuple.getFunSymbols());
		assertTrue(new PrologTuple(List.of(constant("prolog-tuple-ground")))
				.isGround());
	}

	@Test
	@DisplayName("look up tuple positions in shallow and deep modes")
	void lookUpTuplePositionsInShallowAndDeepModes() {
		Variable nestedArgument = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern(
						"prolog-tuple-position-" + UUID.randomUUID(), 1),
				List.of(nestedArgument));
		Variable storedVariable = new Variable();
		storedVariable.union(nested);
		PrologTuple tuple = new PrologTuple(List.of(storedVariable));

		assertSame(tuple, tuple.get(new Position()));
		assertSame(storedVariable, tuple.get(0));
		assertSame(nested, tuple.get(new Position(0)));
		assertSame(storedVariable, tuple.get(new Position(0), true));
		assertSame(nestedArgument,
				tuple.get(new Position(0).addLast(0)));
		assertNull(tuple.get(new Position(-1)));
		assertNull(tuple.get(new Position(1)));
		assertNull(tuple.get(new Position(0).addLast(1)));
	}

	@Test
	@DisplayName("collect deepest distinct hat subterms in tuple order")
	void collectDeepestDistinctHatSubtermsInTupleOrder() {
		HatFunctionSymbol firstSymbol = hatSymbol("prolog-tuple-first-hat");
		HatFunctionSymbol secondSymbol = hatSymbol("prolog-tuple-second-hat");
		Variable sharedArgument = new Variable();
		HatFunction first = new HatFunction(
				firstSymbol, sharedArgument, List.of(2, 3));
		HatFunction duplicate = new HatFunction(
				firstSymbol, sharedArgument, List.of(0, 2, 3));
		HatFunction second = new HatFunction(
				secondSymbol, new Variable(), List.of(4, 5));
		PrologTuple tuple = new PrologTuple(List.of(first, duplicate, second));

		assertEquals(List.of(first, second),
				new ArrayList<>(tuple.getHatSubterms()));
		assertTrue(tuple.containsHatSubterm());
		assertFalse(new PrologTuple(List.of(new Variable())).containsHatSubterm());
	}

	@Test
	@DisplayName("reject tuple disagreements except for the identity fast path")
	void rejectTupleDisagreementsExceptForTheIdentityFastPath() {
		PrologTuple tuple = new PrologTuple(List.of(new Variable()));
		PrologTuple distinct = new PrologTuple(List.of(new Variable()));

		assertTrue(tuple.dpos(tuple, false).isEmpty());
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.dpos(distinct, false));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.dpos(distinct, true));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.dpos(constant("prolog-tuple-dpos"), true));
	}

	@Test
	@DisplayName("replace only the tuple root and reject inner replacements")
	void replaceOnlyTheTupleRootAndRejectInnerReplacements() {
		PrologTuple tuple = new PrologTuple(
				List.of(constant("prolog-tuple-replaced-element")));
		Variable storedReplacement = new Variable();
		Function replacementSchema = constant("prolog-tuple-replacement");
		storedReplacement.union(replacementSchema);

		assertSame(replacementSchema,
				tuple.replace(new Position(), storedReplacement));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.replace(new Position(0), replacementSchema));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.replace(new Position(-1), replacementSchema));
	}

	@Test
	@DisplayName("replace tuple variables recursively and flatten replacements")
	void replaceTupleVariablesRecursivelyAndFlattenReplacements() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		PrologTuple source = new PrologTuple(
				List.of(firstVariable, secondVariable));
		Function firstReplacement = constant("prolog-tuple-replacement-first");
		Function secondReplacement = constant("prolog-tuple-replacement-second");
		PrologTuple replacement = new PrologTuple(
				List.of(firstReplacement, secondReplacement));

		PrologTuple result = (PrologTuple) source.replaceVariables(replacement);

		assertEquals("(" + firstReplacement + "," + secondReplacement + ","
				+ firstReplacement + "," + secondReplacement + ")",
				result.toString());
		assertSame(firstReplacement, result.get(0));
		assertSame(secondReplacement, result.get(1));
		assertSame(firstReplacement, result.get(2));
		assertSame(secondReplacement, result.get(3));
		assertSame(firstVariable, source.get(0));
		assertSame(secondVariable, source.get(1));
	}

	@Test
	@DisplayName("match tuple prefixes and retain bindings after suffix failure")
	void matchTuplePrefixesAndRetainBindingsAfterSuffixFailure() {
		Variable firstPattern = new Variable();
		Variable suffixPattern = new Variable();
		PrologTuple pattern = new PrologTuple(
				List.of(firstPattern, suffixPattern));
		Function firstTarget = constant("prolog-tuple-match-first");
		Function secondTarget = constant("prolog-tuple-match-second");
		Function thirdTarget = constant("prolog-tuple-match-third");
		PrologTuple target = new PrologTuple(
				List.of(firstTarget, secondTarget, thirdTarget));
		Substitution matcher = new Substitution();

		assertTrue(pattern.isMoreGeneralThan(target, matcher));
		assertSame(firstTarget, matcher.get(firstPattern));
		Term matchedSuffix = matcher.get(suffixPattern);
		assertTrue(matchedSuffix instanceof PrologTuple);
		assertEquals("(" + secondTarget + "," + thirdTarget + ")",
				matchedSuffix.toString());
		assertFalse(target.isMoreGeneralThan(pattern));

		Variable repeated = new Variable();
		PrologTuple conflictingPattern = new PrologTuple(
				List.of(repeated, repeated));
		Substitution partialMatcher = new Substitution();
		assertFalse(conflictingPattern.isMoreGeneralThan(
				new PrologTuple(List.of(firstTarget, secondTarget)),
				partialMatcher));
		assertSame(firstTarget, partialMatcher.get(repeated));
	}

	@Test
	@DisplayName("unify tuples with variables and extract equal-arity solutions")
	void unifyTuplesWithVariablesAndExtractEqualAritySolutions() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		PrologTuple pattern = new PrologTuple(
				List.of(firstVariable, secondVariable));
		Function firstTarget = constant("prolog-tuple-unify-first");
		Function secondTarget = constant("prolog-tuple-unify-second");
		PrologTuple target = new PrologTuple(List.of(firstTarget, secondTarget));
		Substitution mgu = new Substitution();

		assertTrue(pattern.unifyWith(target, mgu));
		assertTrue(pattern.deepEquals(target));
		assertSame(firstTarget.findSchema(), mgu.get(firstVariable));
		assertSame(secondTarget.findSchema(), mgu.get(secondVariable));

		Variable tupleVariable = new Variable();
		PrologTuple tuple = new PrologTuple(
				List.of(constant("prolog-tuple-variable-orientation")));
		Substitution tupleMgu = new Substitution();
		assertTrue(tuple.unifyWith(tupleVariable, tupleMgu));
		assertTrue(tupleVariable.deepEquals(tuple));
		assertSame(tuple.findSchema(), tupleMgu.get(tupleVariable));
	}

	@Test
	@DisplayName("unify a final tuple element with the longer tuple suffix")
	void unifyFinalTupleElementWithLongerTupleSuffix() {
		Variable firstVariable = new Variable();
		Variable suffixVariable = new Variable();
		PrologTuple shorter = new PrologTuple(
				List.of(firstVariable, suffixVariable));
		Function firstTarget = constant("prolog-tuple-unify-prefix");
		Function secondTarget = constant("prolog-tuple-unify-suffix-first");
		Function thirdTarget = constant("prolog-tuple-unify-suffix-second");
		PrologTuple longer = new PrologTuple(
				List.of(firstTarget, secondTarget, thirdTarget));

		assertTrue(longer.unifyWith(shorter));
		assertTrue(firstVariable.deepEquals(firstTarget));
		assertEquals("(" + secondTarget + "," + thirdTarget + ")",
				suffixVariable.toString());
		assertTrue(longer.deepEquals(shorter));
	}

	@Test
	@DisplayName("retain tuple unification mutations after a later conflict")
	void retainTupleUnificationMutationsAfterLaterConflict() {
		Variable repeated = new Variable();
		Function firstTarget = constant("prolog-tuple-unify-partial-first");
		Function conflictingTarget = constant("prolog-tuple-unify-partial-conflict");
		PrologTuple pattern = new PrologTuple(List.of(repeated, repeated));
		PrologTuple target = new PrologTuple(
				List.of(firstTarget, conflictingTarget));
		Substitution partialMgu = new Substitution();

		assertFalse(pattern.unifyWith(target, partialMgu));
		assertTrue(repeated.deepEquals(firstTarget));
		assertTrue(pattern.deepEquals(target));
		assertNull(partialMgu.get(repeated));
	}

	@Test
	@DisplayName("distinguish functional flattening from in-place tuple application")
	void distinguishFunctionalFlatteningFromInPlaceTupleApplication() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		PrologTuple source = new PrologTuple(
				List.of(firstVariable, secondVariable));
		Function firstReplacement = constant("prolog-tuple-apply-first");
		Function secondReplacement = constant("prolog-tuple-apply-second");
		PrologTuple tupleReplacement = new PrologTuple(
				List.of(firstReplacement, secondReplacement));
		Substitution substitution = new Substitution();
		substitution.add(firstVariable, tupleReplacement);
		substitution.add(secondVariable, firstReplacement);

		PrologTuple functional = (PrologTuple) source.apply(substitution);
		assertNotSame(firstReplacement, functional.get(0));
		assertTrue(firstReplacement.deepEquals(functional.get(0)));
		assertNotSame(secondReplacement, functional.get(1));
		assertTrue(secondReplacement.deepEquals(functional.get(1)));
		assertNotSame(firstReplacement, functional.get(2));
		assertTrue(firstReplacement.deepEquals(functional.get(2)));
		assertSame(firstVariable, source.get(0));

		source.applyInPlace(substitution);
		assertTrue(source.get(0) instanceof PrologTuple);
		assertNotSame(tupleReplacement, source.get(0));
		assertTrue(tupleReplacement.deepEquals(source.get(0)));
		assertNotSame(firstReplacement, source.get(1));
		assertTrue(firstReplacement.deepEquals(source.get(1)));
	}

	@Test
	@DisplayName("reject tuple left-unification transformations and position iteration")
	void rejectTupleLeftUnificationTransformationsAndPositionIteration() {
		Variable element = new Variable();
		PrologTuple tuple = new PrologTuple(List.of(element));
		Variable mappedVariable = new Variable();
		Function mappedTerm = constant("prolog-tuple-left-unification-mapped");
		Substitution rho = new Substitution();
		rho.add(mappedVariable, mappedTerm);
		LuEquation equation = new LuEquation(new Variable(), new Variable());

		assertThrows(UnsupportedOperationException.class,
				() -> tuple.distribute(2));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.reduceWithLeftUnificationRule(equation));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.applyAndCompleteRho(rho));
		assertThrows(UnsupportedOperationException.class, tuple::iterator);
		assertThrows(UnsupportedOperationException.class, tuple::shallowIterator);
		assertSame(element, tuple.get(0));
		assertSame(mappedTerm, rho.get(mappedVariable));
	}

	@Test
	@DisplayName("reject inner tuple rewriting after inspecting root rules")
	void rejectInnerTupleRewritingAfterInspectingRootRules() {
		Variable element = new Variable();
		PrologTuple tuple = new PrologTuple(List.of(element));
		Variable ruleVariable = new Variable();
		Function ruleLeft = new Function(
				FunctionSymbol.intern(
						"prolog-tuple-rewriting-left-" + UUID.randomUUID(), 1),
				List.of(ruleVariable));
		Function ruleRight = new Function(
				FunctionSymbol.intern(
						"prolog-tuple-rewriting-right-" + UUID.randomUUID(), 1),
				List.of(ruleVariable));
		RuleTrs rule = new RuleTrs(ruleLeft, ruleRight);
		Trs trs = new Trs("prolog-tuple-rewriting", List.of(rule), "FULL");
		String tupleRendering = tuple.toString();
		String ruleRendering = rule.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> tuple.rewriteWith(trs));
		assertEquals(tupleRendering, tuple.toString());
		assertEquals(ruleRendering, rule.toString());
		assertSame(element, tuple.get(0));
		assertSame(ruleLeft, rule.getLeft());
		assertSame(ruleRight, rule.getRight());
	}

	@Test
	@DisplayName("distinguish root tuple unfolding from inner rejection")
	void distinguishRootTupleUnfoldingFromInnerRejection() {
		Variable element = new Variable();
		PrologTuple tuple = new PrologTuple(List.of(element));
		Variable ruleVariable = new Variable();
		Function ruleLeft = new Function(
				FunctionSymbol.intern(
						"prolog-tuple-unfolding-left-" + UUID.randomUUID(), 1),
				List.of(ruleVariable));
		RuleTrs forwardRule = new RuleTrs(
				ruleLeft, constant("prolog-tuple-unfolding-right"));
		Map<Term, Term> forwardCopies = new HashMap<>();
		Map<Term, Term> backwardCopies = new HashMap<>();
		Map<Term, Term> innerCopies = new HashMap<>();
		Variable sentinel = new Variable();
		innerCopies.put(sentinel, sentinel);

		assertNull(tuple.unfoldWith(
				forwardRule, new Position(), false, false, forwardCopies));
		assertTrue(forwardCopies.containsKey(element));
		assertNotSame(element, forwardCopies.get(element));

		RuleTrs backwardRule = new RuleTrs(ruleLeft, new Variable());
		Term backwardResult = tuple.unfoldWith(
				backwardRule, new Position(), true, false, backwardCopies);
		assertTrue(backwardResult instanceof Function);
		assertSame(ruleLeft.getRootSymbol(), backwardResult.getRootSymbol());
		assertNotSame(ruleLeft, backwardResult);
		assertTrue(backwardCopies.containsKey(element));

		assertThrows(UnsupportedOperationException.class,
				() -> tuple.unfoldWith(
						forwardRule, new Position(0), true, true, innerCopies));
		assertEquals(1, innerCopies.size());
		assertSame(sentinel, innerCopies.get(sentinel));
		assertSame(element, tuple.get(0));
	}

	@Test
	@DisplayName("reject unsupported tuple metrics interpretations and conversions")
	void rejectUnsupportedTupleMetricsInterpretationsAndConversions() {
		Variable element = new Variable();
		PrologTuple tuple = new PrologTuple(List.of(element));
		PrologTuple distinct = new PrologTuple(List.of(new Variable()));
		PolyInterpretation interpretation = new PolyInterpretation();
		WeightFunction weights = new WeightFunction();
		Trs emptyTrs = new Trs("prolog-tuple-connectability", List.of(), "FULL");
		String originalRendering = tuple.toString();

		assertThrows(UnsupportedOperationException.class, tuple::depth);
		assertThrows(UnsupportedOperationException.class, tuple::maxArity);
		assertTrue(tuple.embeds(tuple));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.embeds(distinct));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.isConnectableTo(new Variable(), emptyTrs));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.toPolynomial(interpretation));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.generateKBOWeights(weights));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.getWeight(weights));
		assertThrows(UnsupportedOperationException.class, tuple::toTuple);
		assertThrows(UnsupportedOperationException.class, tuple::toFunction);
		assertTrue(interpretation.getAllCoefficients().isEmpty());
		assertTrue(weights.getAllCoefficients().isEmpty());
		assertEquals(originalRendering, tuple.toString());
		assertSame(element, tuple.get(0));
	}

	@Test
	@DisplayName("preserve equal-tuple order fast paths and reject strict comparisons")
	void preserveEqualTupleOrderFastPathsAndRejectStrictComparisons() {
		Variable sharedElement = new Variable();
		PrologTuple tuple = new PrologTuple(List.of(sharedElement));
		PrologTuple equivalent = new PrologTuple(List.of(sharedElement));
		PrologTuple distinct = new PrologTuple(
				List.of(constant("prolog-tuple-order-distinct")));
		LexOrder order = new LexOrder();
		WeightFunction weights = new WeightFunction();
		String orderRendering = order.toString();

		assertTrue(tuple.completeLPO(order, equivalent));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.completeLPOStrict(order, distinct));
		assertTrue(tuple.completeKBO(order, weights, equivalent));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.completeKBOStrict(order, weights, distinct));
		assertEquals(orderRendering, order.toString());
		assertTrue(weights.getAllCoefficients().isEmpty());
		assertSame(sharedElement, tuple.get(0));
	}

	@Test
	@DisplayName("reject tuple filtering before collaborator mutation")
	void rejectTupleFilteringBeforeCollaboratorMutation() {
		Variable first = new Variable();
		Variable second = new Variable();
		PrologTuple tuple = new PrologTuple(List.of(first, second));
		ArgFiltering filtering = new ArgFiltering();
		Map<Variable, String> names = new HashMap<>();
		names.put(first, "First");
		names.put(second, "Second");
		String rendering = tuple.toString(names, false);

		assertThrows(UnsupportedOperationException.class,
				() -> tuple.buildFilters(filtering));
		assertThrows(UnsupportedOperationException.class,
				() -> tuple.applyFilters(filtering));
		assertTrue(filtering.getAllFilters().isEmpty());
		assertEquals("(First,Second)", rendering);
		assertEquals(rendering, tuple.toString(names, false));
		assertSame(first, tuple.get(0));
		assertSame(second, tuple.get(1));
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
