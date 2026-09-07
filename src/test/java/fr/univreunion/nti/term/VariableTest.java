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
import fr.univreunion.nti.program.trs.polynomial.Polynomial;
import fr.univreunion.nti.program.trs.reducpair.LexOrder;
import fr.univreunion.nti.program.trs.reducpair.PolyInterpretation;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.leftunif.LuEquation;
import fr.univreunion.nti.term.leftunif.LuVariable;

class VariableTest {

	@Test
	@DisplayName("initialize a fresh variable as its own representative schema")
	void initializeFreshVariableAsOwnRepresentativeSchema() {
		Variable variable = new Variable();

		assertSame(variable, variable.getSchema());
		assertSame(variable, variable.findSchema());
		assertSame(Variable.VARIABLE_ROOT_SYMBOL, variable.getRootSymbol());
		assertTrue(variable.isVariable());
		assertFalse(variable.isGround());
		assertEquals(Set.of(variable), variable.getVariables());
		assertTrue(variable.getFunSymbols().isEmpty());
		assertFalse(variable.hasChanged());
	}

	@Test
	@DisplayName("resolve variable unions to one function schema")
	void resolveVariableUnionsToOneFunctionSchema() {
		Variable first = new Variable();
		Variable second = new Variable();
		Variable nestedVariable = new Variable();
		Function schema = new Function(
				symbol("variable-union-schema", 1), List.of(nestedVariable));

		first.union(second);

		assertSame(second, first.findSchema());
		assertSame(second, second.findSchema());
		assertTrue(first.deepEquals(second));

		first.union(schema);

		assertSame(schema, first.findSchema());
		assertSame(schema, second.findSchema());
		assertTrue(first.deepEquals(schema));
		assertTrue(second.deepEquals(schema));
		assertFalse(first.isVariable());
		assertEquals(Set.of(nestedVariable), second.getVariables());
	}

	@Test
	@DisplayName("distinguish shallow deep and selective variable copies")
	void distinguishShallowDeepAndSelectiveVariableCopies() {
		Variable variable = new Variable();
		Map<Term, Term> copies = new HashMap<>();

		assertSame(variable, variable.shallowCopy());

		Term firstDeepCopy = variable.deepCopy(copies);
		Term repeatedDeepCopy = variable.deepCopy(copies);

		assertNotSame(variable, firstDeepCopy);
		assertSame(firstDeepCopy, repeatedDeepCopy);
		assertSame(firstDeepCopy, copies.get(variable));
		assertSame(variable, variable.deepCopy(List.of()));
		assertNotSame(variable, variable.deepCopy(List.of(variable)));
	}

	@Test
	@DisplayName("copy a resolved schema and preserve identity-based rendering")
	void copyResolvedSchemaAndPreserveIdentityBasedRendering() {
		Variable storedVariable = new Variable();
		Variable reachableVariable = new Variable();
		Function schema = new Function(
				symbol("variable-copy-schema", 1), List.of(reachableVariable));
		Variable distinctVariable = new Variable();
		Map<Variable, String> names = new HashMap<>();
		names.put(storedVariable, "stored");
		names.put(reachableVariable, "reachable");

		assertEquals("_0", storedVariable.toString());
		assertEquals("stored", storedVariable.toString(names, true));
		assertFalse(storedVariable.deepEquals(distinctVariable));
		assertTrue(storedVariable.hasSameStructureAs(distinctVariable));
		assertTrue(storedVariable.hasSameStructureAs(schema));
		assertTrue(storedVariable.sameAs(storedVariable));
		assertFalse(storedVariable.sameAs(distinctVariable));

		storedVariable.union(schema);
		Function shallowCopy = (Function) storedVariable.shallowCopy();
		Function deepCopy = (Function) storedVariable.deepCopy();

		assertNotSame(schema, shallowCopy);
		assertSame(reachableVariable, shallowCopy.getChild(0));
		assertNotSame(schema, deepCopy);
		assertNotSame(reachableVariable, deepCopy.getChild(0));
		assertEquals(schema.toString(names, false),
				storedVariable.toString(names, false));
		assertEquals("stored", storedVariable.toString(names, true));
	}

	@Test
	@DisplayName("report fresh variable structure and occurrence counts")
	void reportFreshVariableStructureAndOccurrenceCounts() {
		Variable variable = new Variable();
		Variable other = new Variable();
		Map<Variable, Integer> occurrences = new HashMap<>();
		occurrences.put(variable, 2);

		assertTrue(variable.contains(variable));
		assertFalse(variable.contains(other));
		assertFalse(variable.isGround());
		assertEquals(Set.of(variable), variable.getVariables());
		variable.getVariableOccurrences(occurrences);
		assertEquals(3, occurrences.get(variable));
		assertTrue(variable.getFunSymbols().isEmpty());
		assertTrue(variable.getHatSubterms().isEmpty());
		assertFalse(variable.containsHatSubterm());
	}

	@Test
	@DisplayName("look up only the fresh variable root")
	void lookUpOnlyFreshVariableRoot() {
		Variable variable = new Variable();

		assertSame(variable, variable.get(new Position()));
		assertSame(variable, variable.get(new Position(), true));
		assertNull(variable.get(-1));
		assertNull(variable.get(0));
		assertNull(variable.get(new Position(-1)));
		assertNull(variable.get(new Position(0)));
		assertNull(variable.get(new Position(0), true));
	}

	@Test
	@DisplayName("distinguish deep and shallow schema positions")
	void distinguishDeepAndShallowSchemaPositions() {
		Variable storedVariable = new Variable();
		Variable reachableVariable = new Variable();
		Function schema = new Function(
				symbol("variable-position-schema", 1),
				List.of(reachableVariable));
		Position childPosition = new Position(0);

		storedVariable.union(schema);

		assertSame(schema, storedVariable.get(new Position()));
		assertSame(storedVariable,
				storedVariable.get(new Position(), true));
		assertSame(reachableVariable, storedVariable.get(childPosition));
		assertNull(storedVariable.get(childPosition, true));
		assertEquals(List.of("root", "[0]"),
				positionLabels(storedVariable.iterator()));
		assertEquals(List.of("root"),
				positionLabels(storedVariable.shallowIterator()));
	}

	@Test
	@DisplayName("visit the resolved schema subterms of a unified variable")
	void visitResolvedSchemaSubterms() {
		Variable storedVariable = new Variable();
		Variable reachableVariable = new Variable();
		Function schema = new Function(
				symbol("variable-subterm-schema", 1),
				List.of(reachableVariable));
		List<Term> subterms = new ArrayList<>();
		storedVariable.union(schema);

		storedVariable.forEachSubterm(subterms::add);

		assertEquals(2, subterms.size());
		assertSame(schema, subterms.get(0));
		assertSame(reachableVariable, subterms.get(1));
	}

	@Test
	@DisplayName("exhaust fresh variable position iterators")
	void exhaustFreshVariablePositionIterators() {
		Variable variable = new Variable();
		Iterator<Position> deepPositions = variable.iterator();
		Iterator<Position> shallowPositions = variable.shallowIterator();

		assertTrue(deepPositions.hasNext());
		assertTrue(deepPositions.hasNext());
		assertTrue(deepPositions.next().isEmpty());
		assertFalse(deepPositions.hasNext());
		assertThrows(NoSuchElementException.class, deepPositions::next);
		assertTrue(shallowPositions.next().isEmpty());
		assertFalse(shallowPositions.hasNext());
		assertThrows(NoSuchElementException.class, shallowPositions::next);
	}

	@Test
	@DisplayName("report variable disagreements according to pair policy")
	void reportVariableDisagreementsAccordingToPairPolicy() {
		Variable first = new Variable();
		Variable second = new Variable();
		Function function = new Function(
				symbol("variable-disagreement-function", 0), List.of());

		assertTrue(first.dpos(first, true).isEmpty());
		assertTrue(first.dpos(second, false).isEmpty());
		assertEquals(List.of("root"),
				positionLabels(first.dpos(second, true).iterator()));
		assertEquals(List.of("root"),
				positionLabels(first.dpos(function, false).iterator()));

		first.union(function);

		assertTrue(first.dpos(function, true).isEmpty());
	}

	@Test
	@DisplayName("replace a variable root and reject deeper positions")
	void replaceVariableRootAndRejectDeeperPositions() {
		Variable variable = new Variable();
		Function replacement = new Function(
				symbol("variable-replacement", 0), List.of());

		assertSame(replacement,
				variable.replace(new Position(), replacement));
		assertSame(replacement, variable.replaceVariables(replacement));
		assertThrows(IndexOutOfBoundsException.class,
				() -> variable.replace(new Position(0), replacement));
		assertSame(variable, variable.findSchema());
		assertEquals(replacement.getRootSymbol().toString(),
				replacement.toString());
	}

	@Test
	@DisplayName("insert preserve and reject variable matcher bindings")
	void insertPreserveAndRejectVariableMatcherBindings() {
		Variable pattern = new Variable();
		Function firstTarget = new Function(
				symbol("variable-matcher-first", 0), List.of());
		Function equivalentTarget = new Function(
				firstTarget.getRootSymbol(), List.of());
		Function conflictingTarget = new Function(
				symbol("variable-matcher-conflict", 0), List.of());
		Substitution matcher = new Substitution();

		assertTrue(pattern.isMoreGeneralThan(firstTarget, matcher));
		assertSame(firstTarget, matcher.get(pattern));
		assertTrue(pattern.isMoreGeneralThan(equivalentTarget, matcher));
		assertSame(firstTarget, matcher.get(pattern));
		assertFalse(pattern.isMoreGeneralThan(conflictingTarget, matcher));
		assertSame(firstTarget, matcher.get(pattern));
		assertFalse(pattern.isMoreGeneralThan(pattern, matcher));
		assertSame(firstTarget, matcher.get(pattern));
		assertFalse(firstTarget.isMoreGeneralThan(pattern));
	}

	@Test
	@DisplayName("delegate matching through a resolved variable schema")
	void delegateMatchingThroughResolvedVariableSchema() {
		Variable storedVariable = new Variable();
		Variable schemaVariable = new Variable();
		FunctionSymbol wrapper = symbol("variable-matcher-schema", 1);
		Function schema = new Function(wrapper, List.of(schemaVariable));
		Function targetArgument = new Function(
				symbol("variable-matcher-schema-target", 0), List.of());
		Function target = new Function(wrapper, List.of(targetArgument));
		Substitution matcher = new Substitution();

		storedVariable.union(schema);

		assertTrue(storedVariable.isMoreGeneralThan(target, matcher));
		assertNull(matcher.get(storedVariable));
		assertSame(targetArgument, matcher.get(schemaVariable));
	}

	@Test
	@DisplayName("apply substitutions by identity or shallow mapped copies")
	void applySubstitutionsByIdentityOrShallowMappedCopies() {
		Variable variable = new Variable();
		Variable mappedVariable = new Variable();
		Function mappedTerm = new Function(
				symbol("variable-apply-mapped", 1), List.of(mappedVariable));
		Substitution substitution = new Substitution();

		assertSame(variable, variable.apply(substitution));

		substitution.addReplace(variable, mappedTerm);
		Function applied = (Function) variable.apply(substitution);

		assertNotSame(mappedTerm, applied);
		assertSame(mappedVariable, applied.getChild(0));
		assertSame(mappedVariable, mappedTerm.getChild(0));
		assertThrows(UnsupportedOperationException.class,
				() -> variable.applyInPlace(substitution));
		assertSame(variable, variable.findSchema());
	}

	@Test
	@DisplayName("resolve a variable schema before substitution application")
	void resolveVariableSchemaBeforeSubstitutionApplication() {
		Variable storedVariable = new Variable();
		Variable schemaVariable = new Variable();
		Function schema = new Function(
				symbol("variable-apply-schema", 1), List.of(schemaVariable));
		Function replacement = new Function(
				symbol("variable-apply-schema-replacement", 0), List.of());
		Substitution substitution = new Substitution();
		substitution.addReplace(storedVariable, replacement);
		substitution.addReplace(schemaVariable, replacement);

		storedVariable.union(schema);
		Function applied = (Function) storedVariable.apply(substitution);

		assertNotSame(schema, applied);
		assertNotSame(replacement, applied.getChild(0));
		assertTrue(replacement.deepEquals(applied.getChild(0)));
		assertSame(schemaVariable, schema.getChild(0));
		assertSame(replacement, substitution.get(storedVariable));
	}

	@Test
	@DisplayName("orient variable union MGU toward the second schema")
	void orientVariableUnionMguTowardSecondSchema() {
		Variable first = new Variable();
		Variable second = new Variable();
		Substitution mgu = new Substitution();

		assertTrue(first.unifyWith(second, mgu));

		assertTrue(first.deepEquals(second));
		assertSame(second, first.findSchema());
		assertSame(second, mgu.get(first));
		assertNull(mgu.get(second));

		Variable robinsonVariable = new Variable();
		Function target = new Function(
				symbol("variable-robinson-target", 0), List.of());
		Substitution robinsonUnifier = new Substitution();

		assertTrue(robinsonVariable.isUnifiableWith(target, robinsonUnifier));
		assertNotSame(target, robinsonUnifier.get(robinsonVariable));
		assertTrue(target.deepEquals(robinsonUnifier.get(robinsonVariable)));
		assertSame(robinsonVariable, robinsonVariable.findSchema());
	}

	@Test
	@DisplayName("distribute only positive rho powers from a variable")
	void distributeOnlyPositiveRhoPowersFromVariable() {
		Variable variable = new Variable();

		assertSame(variable, variable.distribute(-1));
		assertSame(variable, variable.distribute(0));

		LuVariable distributed = (LuVariable) variable.distribute(3);

		assertNotSame(variable, distributed);
		assertSame(variable, distributed.getVariable());
		assertEquals(3, distributed.getRho());
		assertSame(variable, variable.findSchema());
	}

	@Test
	@DisplayName("reduce a matching variable to a shallow right-hand copy")
	void reduceMatchingVariableToShallowRightHandCopy() {
		Variable variable = new Variable();
		Variable rightVariable = new Variable();
		Function right = new Function(
				symbol("variable-left-unification-right", 1),
				List.of(rightVariable));
		LuEquation matchingEquation = new LuEquation(variable, right);

		Function reduced = (Function)
				variable.reduceWithLeftUnificationRule(matchingEquation);

		assertTrue(variable.hasChanged());
		assertNotSame(right, reduced);
		assertSame(rightVariable, reduced.getChild(0));
		assertSame(rightVariable, right.getChild(0));

		LuEquation nonMatchingEquation = new LuEquation(
				new Variable(), right);
		assertSame(variable,
				variable.reduceWithLeftUnificationRule(nonMatchingEquation));
		assertFalse(variable.hasChanged());
	}

	@Test
	@DisplayName("keep standard-variable rho operations neutral")
	void keepStandardVariableRhoOperationsNeutral() {
		Variable variable = new Variable();
		Variable right = new Variable();
		Variable domain = new Variable();
		Variable image = new Variable();
		Substitution rho = new Substitution();
		rho.addReplace(domain, image);

		assertSame(variable, variable.applyAndCompleteRho(rho));
		assertSame(variable, variable.applyRho(rho));
		variable.completeRho(rho, right);
		assertSame(image, rho.get(domain));
		assertNull(rho.get(variable));
		assertNull(rho.get(right));

		Variable storedVariable = new Variable();
		Variable schemaVariable = new Variable();
		Function schema = new Function(
				symbol("variable-left-unification-schema", 1),
				List.of(schemaVariable));
		storedVariable.union(schema);
		Function distributedSchema =
				(Function) storedVariable.distribute(2);
		LuVariable distributedArgument =
				(LuVariable) distributedSchema.getChild(0);
		assertSame(schemaVariable, distributedArgument.getVariable());
		assertEquals(2, distributedArgument.getRho());
	}

	@Test
	@DisplayName("produce no rewrites for a fresh variable")
	void produceNoRewritesForFreshVariable() {
		Variable variable = new Variable();
		Variable ruleVariable = new Variable();
		Function left = new Function(
				symbol("variable-rewrite-left", 1), List.of(ruleVariable));
		Function right = new Function(
				symbol("variable-rewrite-right", 1), List.of(ruleVariable));
		RuleTrs rule = new RuleTrs(left, right);
		Trs trs = new Trs("variable-rewriting", List.of(rule), "FULL");
		String ruleRendering = rule.toString();

		assertTrue(variable.rewriteWith(trs).isEmpty());
		assertSame(variable, variable.findSchema());
		assertEquals(ruleRendering, rule.toString());
		assertSame(left, rule.getLeft());
		assertSame(right, rule.getRight());
	}

	@Test
	@DisplayName("gate variable-root unfolding and preserve originals")
	void gateVariableRootUnfoldingAndPreserveOriginals() {
		Variable source = new Variable();
		Variable ruleVariable = new Variable();
		FunctionSymbol leftSymbol = symbol("variable-unfold-left", 1);
		FunctionSymbol rightSymbol = symbol("variable-unfold-right", 1);
		Function left = new Function(leftSymbol, List.of(ruleVariable));
		Function right = new Function(rightSymbol, List.of(ruleVariable));
		RuleTrs rule = new RuleTrs(left, right);
		Map<Term, Term> disabledCopies = new HashMap<>();
		Map<Term, Term> forwardCopies = new HashMap<>();
		Map<Term, Term> backwardCopies = new HashMap<>();
		String ruleRendering = rule.toString();

		assertNull(source.unfoldWith(
				rule, new Position(), false, false, disabledCopies));
		assertTrue(disabledCopies.isEmpty());

		Function forward = (Function) source.unfoldWith(
				rule, new Position(), false, true, forwardCopies);
		Function backward = (Function) source.unfoldWith(
				rule, new Position(), true, true, backwardCopies);

		assertSame(rightSymbol, forward.getRootSymbol());
		assertSame(leftSymbol, backward.getRootSymbol());
		assertTrue(forwardCopies.containsKey(source));
		assertTrue(backwardCopies.containsKey(source));
		assertNotSame(source, forwardCopies.get(source));
		assertNotSame(source, backwardCopies.get(source));
		assertSame(source, source.findSchema());
		assertEquals(ruleRendering, rule.toString());
		assertSame(ruleVariable, left.getChild(0));
		assertSame(ruleVariable, right.getChild(0));
	}

	@Test
	@DisplayName("reject variable inner unfolding before copy-map mutation")
	void rejectVariableInnerUnfoldingBeforeCopyMapMutation() {
		Variable source = new Variable();
		Variable ruleVariable = new Variable();
		RuleTrs rule = new RuleTrs(
				new Function(symbol("variable-inner-unfold-left", 1),
						List.of(ruleVariable)),
				new Function(symbol("variable-inner-unfold-right", 1),
						List.of(ruleVariable)));
		Position invalidPosition = new Position(0);
		Map<Term, Term> copies = new HashMap<>();
		Variable sentinel = new Variable();
		copies.put(sentinel, sentinel);

		assertThrows(IndexOutOfBoundsException.class,
				() -> source.unfoldWith(
						rule, invalidPosition, false, true, copies));
		assertEquals(1, copies.size());
		assertSame(sentinel, copies.get(sentinel));
		assertEquals("[0]", invalidPosition.toString());
		assertSame(source, source.findSchema());
	}

	@Test
	@DisplayName("report variable depth arity embedding and conversions")
	void reportVariableDepthArityEmbeddingAndConversions() {
		Variable variable = new Variable();
		Variable other = new Variable();
		Trs emptyTrs = new Trs("variable-rencap", List.of(), "FULL");

		assertEquals(0, variable.depth());
		assertEquals(-1, variable.maxArity());
		assertTrue(variable.embeds(variable));
		assertFalse(variable.embeds(other));
		assertSame(variable, variable.toTuple());
		assertSame(variable, variable.toFunction());

		Term renamedCap = variable.rencap(emptyTrs, false);
		assertTrue(renamedCap instanceof Variable);
		assertNotSame(variable, renamedCap);
	}

	@Test
	@DisplayName("interpret variables without adding symbol coefficients")
	void interpretVariablesWithoutAddingSymbolCoefficients() {
		Variable variable = new Variable();
		PolyInterpretation interpretation = new PolyInterpretation();
		WeightFunction weights = new WeightFunction();

		Polynomial polynomial = variable.toPolynomial(interpretation);

		assertEquals(variable.toString(), polynomial.toString());
		assertTrue(interpretation.getAllCoefficients().isEmpty());
		variable.generateKBOWeights(weights);
		assertTrue(weights.getAllCoefficients().isEmpty());
		assertNull(variable.getWeight(weights));
		weights.getVariableWeight().setValue(7);
		assertEquals(7, variable.getWeight(weights));
	}

	@Test
	@DisplayName("complete only non-strict equal variable orders")
	void completeOnlyNonStrictEqualVariableOrders() {
		Variable variable = new Variable();
		Variable other = new Variable();
		Function function = new Function(
				symbol("variable-order-function", 0), List.of());
		LexOrder order = new LexOrder();
		WeightFunction weights = new WeightFunction();
		weights.getVariableWeight().setValue(1);
		String orderRendering = order.toString();

		assertTrue(variable.completeLPO(order, variable));
		assertFalse(variable.completeLPO(order, other));
		assertFalse(variable.completeLPOStrict(order, function));
		assertTrue(variable.completeKBO(order, weights, variable));
		assertFalse(variable.completeKBO(order, weights, other));
		assertFalse(variable.completeKBOStrict(order, weights, function));
		assertEquals(orderRendering, order.toString());
	}

	@Test
	@DisplayName("leave argument filtering unchanged for a variable")
	void leaveArgumentFilteringUnchangedForVariable() {
		Variable variable = new Variable();
		ArgFiltering filtering = new ArgFiltering();

		variable.buildFilters(filtering);

		assertTrue(filtering.getAllFilters().isEmpty());
		assertSame(variable, variable.applyFilters(filtering));
		assertSame(variable, variable.findSchema());
	}

	private static List<String> positionLabels(Iterator<Position> positions) {
		List<String> labels = new ArrayList<>();
		while (positions.hasNext()) {
			Position position = positions.next();
			labels.add(position.isEmpty() ? "root" : position.toString());
		}
		return labels;
	}

	private static FunctionSymbol symbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}
}
