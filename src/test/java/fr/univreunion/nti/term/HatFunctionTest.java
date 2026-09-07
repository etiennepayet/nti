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
import java.util.Collection;
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

class HatFunctionTest {

	@Test
	@DisplayName("subtract equal-length exponent lists at their boundary")
	void subtractEqualLengthExponentListsAtBoundary() {
		HatFixture fixture = hatFixture("hat-minus-equal");
		Variable minuendArgument = new Variable();
		Variable subtrahendArgument = new Variable();
		HatFunction minuend = new HatFunction(
				fixture.hatSymbol(), minuendArgument, List.of(3, 2, 1));
		HatFunction subtrahend = new HatFunction(
				fixture.hatSymbol(), subtrahendArgument, List.of(3, 2, 1));

		Term[] result = minuend.minus(subtrahend);

		assertHat(result[0], fixture.hatSymbol(), minuendArgument, 0, 0, 0);
		assertSame(subtrahendArgument, result[1]);
		assertEquals(List.of(3, 2, 1), minuend.getExponents());
		assertEquals(List.of(3, 2, 1), subtrahend.getExponents());
	}

	@Test
	@DisplayName("align different exponent-list lengths from the closing exponent")
	void alignDifferentExponentListLengthsFromClosingExponent() {
		HatFixture fixture = hatFixture("hat-minus-lengths");
		Variable minuendArgument = new Variable();
		Variable shorterArgument = new Variable();
		HatFunction minuend = new HatFunction(
				fixture.hatSymbol(), minuendArgument, List.of(5, 4, 3));
		HatFunction shorter = new HatFunction(
				fixture.hatSymbol(), shorterArgument, List.of(2, 1));

		Term[] shorterResult = minuend.minus(shorter);

		assertHat(shorterResult[0], fixture.hatSymbol(), minuendArgument, 5, 2, 2);
		assertSame(shorterArgument, shorterResult[1]);

		HatFunction longerWithLeadingZero = new HatFunction(
				fixture.hatSymbol(), shorterArgument, List.of(0, 2, 1));
		HatFunction shorterMinuend = new HatFunction(
				fixture.hatSymbol(), minuendArgument, List.of(4, 3));
		Term[] longerResult = shorterMinuend.minus(longerWithLeadingZero);

		assertHat(longerResult[0], fixture.hatSymbol(), minuendArgument, 2, 2);
		assertSame(shorterArgument, longerResult[1]);
	}

	@Test
	@DisplayName("reject incompatible or excessive hat subtraction")
	void rejectIncompatibleOrExcessiveHatSubtraction() {
		HatFixture fixture = hatFixture("hat-minus-rejected");
		HatFixture otherFixture = hatFixture("hat-minus-other-context");
		Variable argument = new Variable();
		HatFunction minuend = new HatFunction(
				fixture.hatSymbol(), argument, List.of(4, 3));

		assertNull(minuend.minus(new HatFunction(
				otherFixture.hatSymbol(), new Variable(), List.of(1, 1))));
		assertNull(minuend.minus(new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(4, 4))));
		assertNull(minuend.minus(new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(1, 4, 3))));
		assertNull(minuend.minus(new Variable()));
		assertEquals(List.of(4, 3), minuend.getExponents());
		assertSame(argument, minuend.getArgument());
	}

	@Test
	@DisplayName("subtract context towers up to the closing-exponent boundary")
	void subtractContextTowersUpToClosingExponentBoundary() {
		HatFixture fixture = hatFixture("hat-minus-tower");
		Variable hatArgument = new Variable();
		Variable towerBase = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), hatArgument, List.of(3, 2));
		Function oneLevel = new Function(
				fixture.contextSymbol(), List.of(towerBase));
		Function twoLevels = new Function(
				fixture.contextSymbol(), List.of(oneLevel));
		Function threeLevels = new Function(
				fixture.contextSymbol(), List.of(twoLevels));

		Term[] result = hat.minus(twoLevels);

		assertHat(result[0], fixture.hatSymbol(), hatArgument, 3, 0);
		assertSame(towerBase, result[1]);
		assertNull(hat.minus(threeLevels));
		assertNull(hat.minus(new Function(
				symbol("hat-minus-foreign", 1), List.of(towerBase))));
		assertEquals(List.of(3, 2), hat.getExponents());
		assertSame(hatArgument, hat.getArgument());
	}

	@Test
	@DisplayName("sum shorter inner-hat exponents from the closing exponent")
	void sumShorterInnerHatExponentsFromClosingExponent() {
		HatFixture fixture = hatFixture("hat-apply-shorter-inner");
		Variable outerArgument = new Variable();
		Variable innerArgument = new Variable();
		HatFunction outer = new HatFunction(
				fixture.hatSymbol(), outerArgument, List.of(5, 4, 3));
		HatFunction inner = new HatFunction(
				fixture.hatSymbol(), innerArgument, List.of(2, 1));
		Substitution substitution = new Substitution();
		substitution.addReplace(outerArgument, inner);

		HatFunction result = (HatFunction) outer.apply(substitution);

		assertHat(result, fixture.hatSymbol(), innerArgument, 5, 6, 4);
		assertEquals(List.of(5, 4, 3), outer.getExponents());
		assertEquals(List.of(2, 1), inner.getExponents());
		assertSame(outerArgument, outer.getArgument());
		assertSame(innerArgument, inner.getArgument());
	}

	@Test
	@DisplayName("retain leading exponents from a longer inner hat")
	void retainLeadingExponentsFromLongerInnerHat() {
		HatFixture fixture = hatFixture("hat-apply-longer-inner");
		Variable outerArgument = new Variable();
		Variable innerArgument = new Variable();
		HatFunction outer = new HatFunction(
				fixture.hatSymbol(), outerArgument, List.of(4, 3));
		HatFunction inner = new HatFunction(
				fixture.hatSymbol(), innerArgument, List.of(7, 2, 1));
		Substitution substitution = new Substitution();
		substitution.addReplace(outerArgument, inner);

		HatFunction result = (HatFunction) outer.apply(substitution);

		assertHat(result, fixture.hatSymbol(), innerArgument, 7, 6, 4);
		assertEquals(List.of(4, 3), outer.getExponents());
		assertEquals(List.of(7, 2, 1), inner.getExponents());
	}

	@Test
	@DisplayName("absorb a matching context tower into the closing exponent")
	void absorbMatchingContextTowerIntoClosingExponent() {
		HatFixture fixture = hatFixture("hat-apply-tower");
		Variable outerArgument = new Variable();
		Variable towerBase = new Variable();
		HatFunction outer = new HatFunction(
				fixture.hatSymbol(), outerArgument, List.of(3, 2));
		Function firstLevel = new Function(
				fixture.contextSymbol(), List.of(towerBase));
		Function secondLevel = new Function(
				fixture.contextSymbol(), List.of(firstLevel));
		Substitution substitution = new Substitution();
		substitution.addReplace(outerArgument, secondLevel);

		HatFunction result = (HatFunction) outer.apply(substitution);

		assertHat(result, fixture.hatSymbol(), towerBase, 3, 4);
		assertEquals(List.of(3, 2), outer.getExponents());
		assertSame(outerArgument, outer.getArgument());
		assertSame(firstLevel, secondLevel.getChild(0));
		assertSame(towerBase, firstLevel.getChild(0));
	}

	@Test
	@DisplayName("reject closing-exponent overflow when absorbing a context tower")
	void rejectClosingExponentOverflowWhenAbsorbingAContextTower() {
		HatFixture fixture = hatFixture("hat-apply-tower-overflow");
		Variable outerArgument = new Variable();
		Variable towerBase = new Variable();
		HatFunction outer = new HatFunction(
				fixture.hatSymbol(), outerArgument, 1, Integer.MAX_VALUE);
		Function oneLevel = new Function(
				fixture.contextSymbol(), List.of(towerBase));
		Substitution substitution = new Substitution();
		substitution.addReplace(outerArgument, oneLevel);

		assertThrows(ArithmeticException.class, () -> outer.apply(substitution));
		assertEquals(List.of(1, Integer.MAX_VALUE), outer.getExponents());
		assertSame(outerArgument, outer.getArgument());
	}

	@Test
	@DisplayName("retain the outer hat for an incompatible applied context")
	void retainOuterHatForIncompatibleAppliedContext() {
		HatFixture outerFixture = hatFixture("hat-apply-outer");
		HatFixture innerFixture = hatFixture("hat-apply-incompatible");
		Variable outerArgument = new Variable();
		Variable innerArgument = new Variable();
		HatFunction outer = new HatFunction(
				outerFixture.hatSymbol(), outerArgument, List.of(3, 2));
		HatFunction inner = new HatFunction(
				innerFixture.hatSymbol(), innerArgument, List.of(5, 4));
		Substitution substitution = new Substitution();
		substitution.addReplace(outerArgument, inner);

		HatFunction result = (HatFunction) outer.apply(substitution);

		assertNotSame(outer, result);
		assertHat(result, outerFixture.hatSymbol(), result.getArgument(), 3, 2);
		HatFunction retainedInner = (HatFunction) result.getArgument();
		assertNotSame(inner, retainedInner);
		assertHat(retainedInner, innerFixture.hatSymbol(), innerArgument, 5, 4);
		assertEquals(List.of(3, 2), outer.getExponents());
		assertEquals(List.of(5, 4), inner.getExponents());
	}

	@Test
	@DisplayName("report arity and pumping and closing exponents")
	void reportArityAndPumpingAndClosingExponents() {
		HatFixture fixture = hatFixture("hat-exponent-queries");
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 4, 7));

		assertEquals(2, hat.getArity());
		assertEquals(6, hat.getA());
		assertEquals(7, hat.getB());
		assertEquals(List.of(2, 4, 7), hat.getExponents());
	}

	@Test
	@DisplayName("sum pumping exponents exactly at the integer boundary")
	void sumPumpingExponentsExactlyAtTheIntegerBoundary() {
		HatFixture fixture = hatFixture("hat-pumping-sum-boundary");
		HatFunction boundary = new HatFunction(
				fixture.hatSymbol(), new Variable(),
				List.of(Integer.MAX_VALUE - 1, 1, Integer.MAX_VALUE));
		HatFunction overflow = new HatFunction(
				fixture.hatSymbol(), new Variable(),
				List.of(Integer.MAX_VALUE, 1, Integer.MAX_VALUE));

		assertEquals(Integer.MAX_VALUE, boundary.getA());
		assertThrows(ArithmeticException.class, overflow::getA);
	}

	@Test
	@DisplayName("reject exponent overflow when composing hat functions")
	void rejectExponentOverflowWhenComposingHatFunctions() {
		HatFixture fixture = hatFixture("hat-composition-overflow");
		Variable outerArgument = new Variable();
		HatFunction outer = new HatFunction(
				fixture.hatSymbol(), outerArgument,
				List.of(Integer.MAX_VALUE, 0));
		HatFunction inner = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(1, 0));
		Substitution substitution = new Substitution();
		substitution.addReplace(outerArgument, inner);

		assertThrows(ArithmeticException.class, () -> outer.apply(substitution));
		assertEquals(List.of(Integer.MAX_VALUE, 0), outer.getExponents());
		assertEquals(List.of(1, 0), inner.getExponents());
	}

	@Test
	@DisplayName("iterate over a defensive exponent snapshot")
	void iterateOverDefensiveExponentSnapshot() {
		HatFixture fixture = hatFixture("hat-exponent-iterator");
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 4, 7));
		Iterator<Integer> exponents = hat.exponentsDescendingIterator();

		assertEquals(7, exponents.next());
		exponents.remove();

		assertEquals(List.of(2, 4, 7), hat.getExponents());
		assertEquals(4, exponents.next());
		assertEquals(2, exponents.next());
		assertFalse(exponents.hasNext());
	}

	@Test
	@DisplayName("ignore only excess leading zero exponents when comparing")
	void ignoreOnlyExcessLeadingZeroExponentsWhenComparing() {
		HatFixture fixture = hatFixture("hat-exponent-comparison");
		HatFixture otherFixture = hatFixture("hat-exponent-other-symbol");
		HatFunction shorter = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 3));
		HatFunction longerWithZero = new HatFunction(
				otherFixture.hatSymbol(), new Variable(), List.of(0, 2, 3));
		HatFunction longerWithNonZero = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(1, 2, 3));
		HatFunction differentClosingExponent = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 4));

		assertTrue(shorter.equalExponents(longerWithZero));
		assertTrue(longerWithZero.equalExponents(shorter));
		assertFalse(shorter.equalExponents(longerWithNonZero));
		assertFalse(longerWithNonZero.equalExponents(shorter));
		assertFalse(shorter.equalExponents(differentClosingExponent));
	}

	@Test
	@DisplayName("return defensive exponent lists and replace only b")
	void returnDefensiveExponentListsAndReplaceOnlyB() {
		HatFixture fixture = hatFixture("hat-exponent-update");
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 4, 7));
		List<Integer> exponents = hat.getExponents();

		exponents.set(0, 99);
		hat.setB(11);

		assertEquals(List.of(99, 4, 7), exponents);
		assertEquals(List.of(2, 4, 11), hat.getExponents());
		assertEquals(6, hat.getA());
		assertEquals(11, hat.getB());
	}

	@Test
	@DisplayName("reject a negative closing exponent update")
	void rejectNegativeClosingExponentUpdate() {
		HatFixture fixture = hatFixture("hat-negative-exponent-update");
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 4, 7));

		assertThrows(IllegalArgumentException.class, () -> hat.setB(-1));
		assertEquals(List.of(2, 4, 7), hat.getExponents());
	}

	@Test
	@DisplayName("validate construction inputs and copy exponent lists")
	void validateConstructionInputsAndCopyExponentLists() {
		HatFixture fixture = hatFixture("hat-construction");
		HatFunctionSymbol hatSymbol = fixture.hatSymbol();
		Variable argument = new Variable();
		List<Integer> insufficientExponents = List.of(1);
		List<Integer> negativeExponents = List.of(1, -2);
		List<Integer> nullExponent = new ArrayList<>(List.of(1, 2));
		nullExponent.set(1, null);

		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(null, argument, 1, 2));
		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(hatSymbol, null, 1, 2));
		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(hatSymbol, argument, -1, 2));
		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(hatSymbol, argument, 1, -2));
		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(hatSymbol, argument, null));
		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(hatSymbol, argument, insufficientExponents));
		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(hatSymbol, argument, negativeExponents));
		assertThrows(IllegalArgumentException.class,
				() -> new HatFunction(hatSymbol, argument, nullExponent));

		List<Integer> exponents = new ArrayList<>(List.of(2, 3, 4));
		HatFunction hat = new HatFunction(
				hatSymbol, argument, exponents);
		exponents.set(0, 99);

		assertEquals(List.of(2, 3, 4), hat.getExponents());
		assertSame(argument, hat.getArgument());
	}

	@Test
	@DisplayName("copy a hat while sharing its root and argument")
	void copyHatWhileSharingRootAndArgument() {
		HatFixture fixture = hatFixture("hat-copy-constructor");
		Variable argument = new Variable();
		HatFunction source = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3, 4));

		HatFunction copy = new HatFunction(source);
		copy.setB(9);

		assertNotSame(source, copy);
		assertSame(fixture.hatSymbol(), copy.getRootSymbol());
		assertSame(argument, copy.getArgument());
		assertEquals(List.of(2, 3, 4), source.getExponents());
		assertEquals(List.of(2, 3, 9), copy.getExponents());
	}

	@Test
	@DisplayName("distinguish shallow and deep copies of hat arguments")
	void distinguishShallowAndDeepCopiesOfHatArguments() {
		HatFixture fixture = hatFixture("hat-structural-copies");
		Variable repeatedVariable = new Variable();
		FunctionSymbol pair = symbol("hat-copy-pair", 2);
		Function argument = new Function(
				pair, List.of(repeatedVariable, repeatedVariable));
		HatFunction source = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));

		HatFunction shallow = (HatFunction) source.shallowCopy();
		HatFunction deep = (HatFunction) source.deepCopy();
		Function shallowArgument = (Function) shallow.getArgument();
		Function deepArgument = (Function) deep.getArgument();

		assertNotSame(source, shallow);
		assertNotSame(argument, shallowArgument);
		assertSame(repeatedVariable, shallowArgument.getChild(0));
		assertSame(repeatedVariable, shallowArgument.getChild(1));
		assertNotSame(source, deep);
		assertNotSame(argument, deepArgument);
		assertNotSame(repeatedVariable, deepArgument.getChild(0));
		assertSame(deepArgument.getChild(0), deepArgument.getChild(1));
		assertSame(fixture.hatSymbol(), shallow.getRootSymbol());
		assertSame(fixture.hatSymbol(), deep.getRootSymbol());
		assertEquals(List.of(2, 3), shallow.getExponents());
		assertEquals(List.of(2, 3), deep.getExponents());
	}

	@Test
	@DisplayName("compare root exponents and arguments structurally")
	void compareRootExponentsAndArgumentsStructurally() {
		HatFixture fixture = hatFixture("hat-equality");
		HatFixture otherFixture = hatFixture("hat-equality-other-root");
		Variable sharedVariable = new Variable();
		FunctionSymbol wrapper = symbol("hat-equality-wrapper", 1);
		HatFunction source = new HatFunction(
				fixture.hatSymbol(),
				new Function(wrapper, List.of(sharedVariable)),
				List.of(2, 3));
		HatFunction equivalent = new HatFunction(
				fixture.hatSymbol(),
				new Function(wrapper, List.of(sharedVariable)),
				List.of(0, 2, 3));

		assertTrue(source.deepEquals(source));
		assertTrue(source.deepEquals(equivalent));
		assertTrue(equivalent.deepEquals(source));
		assertFalse(source.deepEquals(new HatFunction(
				otherFixture.hatSymbol(), source.getArgument(), List.of(2, 3))));
		assertFalse(source.deepEquals(new HatFunction(
				fixture.hatSymbol(), source.getArgument(), List.of(2, 4))));
		assertFalse(source.deepEquals(new HatFunction(
				fixture.hatSymbol(),
				new Function(wrapper, List.of(new Variable())),
				List.of(2, 3))));
	}

	@Test
	@DisplayName("contain self and recursively nested argument terms")
	void containSelfAndRecursivelyNestedArgumentTerms() {
		HatFixture fixture = hatFixture("hat-containment");
		Variable nestedVariable = new Variable();
		Function nested = new Function(
				symbol("hat-contained-function", 1), List.of(nestedVariable));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), nested, List.of(2, 3));

		assertTrue(hat.contains(hat));
		assertTrue(hat.contains(nested));
		assertTrue(hat.contains(nestedVariable));
		assertFalse(hat.contains(new Variable()));
	}

	@Test
	@DisplayName("traverse a unified argument variable schema")
	void traverseUnifiedArgumentVariableSchema() {
		HatFixture fixture = hatFixture("hat-schema-containment");
		Variable storedVariable = new Variable();
		Variable reachableVariable = new Variable();
		Function schema = new Function(
				symbol("hat-schema-function", 1), List.of(reachableVariable));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), storedVariable, List.of(2, 3));
		HatFunction explicitSchemaHat = new HatFunction(
				fixture.hatSymbol(), schema, List.of(2, 3));

		assertTrue(storedVariable.unifyWith(schema));

		assertFalse(hat.contains(storedVariable));
		assertTrue(hat.contains(schema));
		assertTrue(hat.contains(reachableVariable));
		assertTrue(hat.deepEquals(explicitSchemaHat));
	}

	@Test
	@DisplayName("report groundness variables and repeated occurrences")
	void reportGroundnessVariablesAndRepeatedOccurrences() {
		HatFixture fixture = hatFixture("hat-structural-queries");
		Variable repeatedVariable = new Variable();
		Variable otherVariable = new Variable();
		Function argument = new Function(
				symbol("hat-query-argument", 3),
				List.of(repeatedVariable, otherVariable, repeatedVariable));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		Map<Variable, Integer> occurrences = new HashMap<>();

		assertFalse(hat.isGround());
		assertEquals(Set.of(repeatedVariable, otherVariable), hat.getVariables());
		hat.getVariableOccurrences(occurrences);
		assertEquals(2, occurrences.get(repeatedVariable));
		assertEquals(1, occurrences.get(otherVariable));

		HatFunction groundHat = new HatFunction(
				fixture.hatSymbol(),
				new Function(symbol("hat-query-ground", 0), List.of()),
				List.of(2, 3));
		assertTrue(groundHat.isGround());
		assertTrue(groundHat.getVariables().isEmpty());
	}

	@Test
	@DisplayName("traverse argument schemas for supported structural queries")
	void traverseArgumentSchemasForSupportedStructuralQueries() {
		HatFixture fixture = hatFixture("hat-query-schema");
		Variable storedVariable = new Variable();
		Variable reachableVariable = new Variable();
		Function schema = new Function(
				symbol("hat-query-schema-function", 2),
				List.of(reachableVariable, reachableVariable));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), storedVariable, List.of(2, 3));
		Map<Variable, Integer> occurrences = new HashMap<>();

		assertTrue(storedVariable.unifyWith(schema));

		assertFalse(hat.isGround());
		assertEquals(Set.of(reachableVariable), hat.getVariables());
		hat.getVariableOccurrences(occurrences);
		assertEquals(2, occurrences.get(reachableVariable));
		assertFalse(occurrences.containsKey(storedVariable));
	}

	@Test
	@DisplayName("reject unsupported generic structural queries")
	void rejectUnsupportedGenericStructuralQueries() {
		HatFixture fixture = hatFixture("hat-unsupported-queries");
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 3));

		assertThrows(UnsupportedOperationException.class, hat::depth);
		assertThrows(UnsupportedOperationException.class, hat::maxArity);
		assertThrows(UnsupportedOperationException.class, hat::getFunSymbols);
	}

	@Test
	@DisplayName("look up root argument and nested positions")
	void lookUpRootArgumentAndNestedPositions() {
		HatFixture fixture = hatFixture("hat-positional-lookup");
		Variable nestedVariable = new Variable();
		Function argument = new Function(
				symbol("hat-position-argument", 1), List.of(nestedVariable));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));

		assertSame(hat, hat.get(new Position()));
		assertSame(argument, hat.get(0));
		assertSame(argument, hat.get(new Position(0)));
		assertSame(nestedVariable, hat.get(new Position(0).addLast(0)));
		assertNull(hat.get(-1));
		assertNull(hat.get(1));
		assertNull(hat.get(new Position(-1)));
		assertNull(hat.get(new Position(1)));
		assertNull(hat.get(new Position(0).addLast(1)));
		assertNull(hat.get(new Position(0).addLast(0).addLast(0)));
	}

	@Test
	@DisplayName("distinguish shallow and deep positional lookup through a schema")
	void distinguishShallowAndDeepPositionalLookupThroughSchema() {
		HatFixture fixture = hatFixture("hat-position-schema");
		Variable storedVariable = new Variable();
		Variable reachableVariable = new Variable();
		Function schema = new Function(
				symbol("hat-position-schema-function", 1),
				List.of(reachableVariable));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), storedVariable, List.of(2, 3));
		Position argumentPosition = new Position(0);
		Position nestedPosition = argumentPosition.addLast(0);

		assertTrue(storedVariable.unifyWith(schema));

		assertSame(schema, hat.get(argumentPosition));
		assertSame(storedVariable, hat.get(argumentPosition, true));
		assertSame(reachableVariable, hat.get(nestedPosition));
		assertNull(hat.get(nestedPosition, true));
		assertSame(storedVariable, hat.getArgument());
	}

	@Test
	@DisplayName("collect deepest distinct hat subterms in argument order")
	void collectDeepestDistinctHatSubtermsInArgumentOrder() {
		HatFixture outerFixture = hatFixture("hat-subterms-outer");
		HatFixture firstFixture = hatFixture("hat-subterms-first");
		HatFixture secondFixture = hatFixture("hat-subterms-second");
		Variable sharedArgument = new Variable();
		HatFunction first = new HatFunction(
				firstFixture.hatSymbol(), sharedArgument, List.of(2, 3));
		HatFunction duplicate = new HatFunction(
				firstFixture.hatSymbol(), sharedArgument, List.of(0, 2, 3));
		HatFunction second = new HatFunction(
				secondFixture.hatSymbol(), new Variable(), List.of(4, 5));
		Function argument = new Function(
				symbol("hat-subterms-argument", 3),
				List.of(first, duplicate, second));
		HatFunction outer = new HatFunction(
				outerFixture.hatSymbol(), argument, List.of(6, 7));

		Collection<Term> subterms = outer.getHatSubterms();
		HatFunction leaf = new HatFunction(
				outerFixture.hatSymbol(), new Variable(), List.of(6, 7));

		assertEquals(List.of(first, second), new ArrayList<>(subterms));
		assertSame(first, subterms.iterator().next());
		assertEquals(List.of(leaf), new ArrayList<>(leaf.getHatSubterms()));
		assertTrue(outer.containsHatSubterm());
		assertTrue(leaf.containsHatSubterm());
	}

	@Test
	@DisplayName("report hat root and prefixed argument disagreements")
	void reportHatRootAndPrefixedArgumentDisagreements() {
		HatFixture fixture = hatFixture("hat-dpos");
		HatFixture otherFixture = hatFixture("hat-dpos-other");
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		FunctionSymbol pair = symbol("hat-dpos-pair", 2);
		HatFunction first = new HatFunction(
				fixture.hatSymbol(),
				new Function(pair, List.of(firstVariable, new Variable())),
				List.of(2, 3));
		HatFunction second = new HatFunction(
				fixture.hatSymbol(),
				new Function(pair, List.of(secondVariable,
						new Function(symbol("hat-dpos-constant", 0), List.of()))),
				List.of(0, 2, 3));

		assertEquals(List.of("[0, 1]"),
				positionLabels(first.dpos(second, false).iterator()));
		assertEquals(List.of("[0, 0]", "[0, 1]"),
				positionLabels(first.dpos(second, true).iterator()));
		assertEquals(List.of("root"), positionLabels(first.dpos(
				new HatFunction(otherFixture.hatSymbol(), first.getArgument(),
						List.of(2, 3)), true).iterator()));
		assertEquals(List.of("root"), positionLabels(first.dpos(
				new HatFunction(fixture.hatSymbol(), first.getArgument(),
						List.of(2, 4)), false).iterator()));
	}

	@Test
	@DisplayName("resolve hat argument schemas before collecting disagreements")
	void resolveHatArgumentSchemasBeforeCollectingDisagreements() {
		HatFixture fixture = hatFixture("hat-dpos-schema");
		Variable storedVariable = new Variable();
		Variable schemaVariable = new Variable();
		FunctionSymbol wrapper = symbol("hat-dpos-schema-wrapper", 1);
		Function schema = new Function(wrapper, List.of(schemaVariable));
		HatFunction throughSchema = new HatFunction(
				fixture.hatSymbol(), storedVariable, List.of(2, 3));
		HatFunction explicitSchema = new HatFunction(
				fixture.hatSymbol(),
				new Function(wrapper, List.of(new Variable())), List.of(2, 3));

		assertTrue(storedVariable.unifyWith(schema));

		assertTrue(throughSchema.dpos(explicitSchema, false).isEmpty());
		assertEquals(List.of("[0, 0]"), positionLabels(
				throughSchema.dpos(explicitSchema, true).iterator()));
	}

	@Test
	@DisplayName("match compatible hat arguments directionally")
	void matchCompatibleHatArgumentsDirectionally() {
		HatFixture fixture = hatFixture("hat-matcher");
		Variable repeatedVariable = new Variable();
		FunctionSymbol pair = symbol("hat-matcher-pair", 2);
		Function targetArgument = new Function(
				symbol("hat-matcher-target", 0), List.of());
		HatFunction pattern = new HatFunction(
				fixture.hatSymbol(),
				new Function(pair, List.of(repeatedVariable, repeatedVariable)),
				List.of(2, 3));
		HatFunction target = new HatFunction(
				fixture.hatSymbol(),
				new Function(pair, List.of(targetArgument, targetArgument)),
				List.of(0, 2, 3));
		Substitution matcher = new Substitution();

		assertTrue(pattern.isMoreGeneralThan(target, matcher));
		assertSame(targetArgument, matcher.get(repeatedVariable));
		assertTrue(pattern.isMoreGeneralThan(target));
		assertFalse(target.isMoreGeneralThan(pattern));
	}

	@Test
	@DisplayName("retain partial hat matcher updates and reject roots early")
	void retainPartialHatMatcherUpdatesAndRejectRootsEarly() {
		HatFixture fixture = hatFixture("hat-matcher-failure");
		HatFixture otherFixture = hatFixture("hat-matcher-failure-other");
		Variable repeatedVariable = new Variable();
		FunctionSymbol pair = symbol("hat-matcher-failure-pair", 2);
		Function firstTarget = new Function(
				symbol("hat-matcher-first-target", 0), List.of());
		Function conflictingTarget = new Function(
				symbol("hat-matcher-conflicting-target", 0), List.of());
		HatFunction pattern = new HatFunction(
				fixture.hatSymbol(),
				new Function(pair, List.of(repeatedVariable, repeatedVariable)),
				List.of(2, 3));
		HatFunction conflicting = new HatFunction(
				fixture.hatSymbol(),
				new Function(pair, List.of(firstTarget, conflictingTarget)),
				List.of(2, 3));
		Substitution matcher = new Substitution();

		assertFalse(pattern.isMoreGeneralThan(conflicting, matcher));
		assertSame(firstTarget, matcher.get(repeatedVariable));

		Variable untouchedVariable = new Variable();
		HatFunction untouchedPattern = new HatFunction(
				fixture.hatSymbol(), untouchedVariable, List.of(2, 3));
		assertFalse(untouchedPattern.isMoreGeneralThan(new HatFunction(
				otherFixture.hatSymbol(), conflictingTarget, List.of(2, 3)), matcher));
		assertNull(matcher.get(untouchedVariable));
		assertFalse(untouchedPattern.isMoreGeneralThan(new HatFunction(
				fixture.hatSymbol(), conflictingTarget, List.of(2, 4)), matcher));
		assertNull(matcher.get(untouchedVariable));
	}

	@Test
	@DisplayName("iterate only the hat root with stable exhaustion")
	void iterateOnlyHatRootWithStableExhaustion() {
		HatFixture fixture = hatFixture("hat-position-iterator");
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(),
				new Function(symbol("hat-iterator-argument", 1),
						List.of(new Variable())),
				List.of(2, 3));
		Iterator<Position> positions = hat.iterator();

		assertTrue(positions.hasNext());
		assertTrue(positions.hasNext());
		assertTrue(positions.next().isEmpty());
		assertFalse(positions.hasNext());
		assertFalse(positions.hasNext());
		assertThrows(NoSuchElementException.class, positions::next);
		assertThrows(NoSuchElementException.class, positions::next);
		assertThrows(UnsupportedOperationException.class, positions::remove);
		assertThrows(UnsupportedOperationException.class, hat::shallowIterator);
	}

	@Test
	@DisplayName("render hat symbols exponents and stable variable names")
	void renderHatSymbolsExponentsAndStableVariableNames() {
		HatFixture fixture = hatFixture("hat-rendering");
		Variable repeatedVariable = new Variable();
		Variable otherVariable = new Variable();
		FunctionSymbol pair = symbol("hat-rendering-pair", 2);
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(),
				new Function(pair, List.of(repeatedVariable, repeatedVariable)),
				List.of(2, 4, 7));
		Map<Variable, String> variableNames = new HashMap<>();
		variableNames.put(repeatedVariable, "X");
		variableNames.put(otherVariable, "Y");
		String expectedPrefix = "hat[" + fixture.contextSymbol() + "(□)]";

		assertEquals(expectedPrefix + "^[2, 4, 7](" + pair + "(_0,_0))",
				hat.toString());
		assertEquals(expectedPrefix + "^[2, 4, 7](" + pair + "(X,X))",
				hat.toString(variableNames, false));
		assertEquals("X", variableNames.get(repeatedVariable));
		assertEquals("Y", variableNames.get(otherVariable));
	}

	@Test
	@DisplayName("distinguish shallow and deep rendering through a schema")
	void distinguishShallowAndDeepRenderingThroughSchema() {
		HatFixture fixture = hatFixture("hat-rendering-schema");
		Variable storedVariable = new Variable();
		Variable reachableVariable = new Variable();
		FunctionSymbol wrapper = symbol("hat-rendering-schema-wrapper", 1);
		Function schema = new Function(wrapper, List.of(reachableVariable));
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), storedVariable, List.of(2, 3));
		Map<Variable, String> variableNames = new HashMap<>();
		variableNames.put(storedVariable, "stored");
		variableNames.put(reachableVariable, "reachable");
		String expectedPrefix = "hat[" + fixture.contextSymbol() + "(□)]^[2, 3](";

		assertTrue(storedVariable.unifyWith(schema));

		assertEquals(expectedPrefix + "stored)",
				hat.toString(variableNames, true));
		assertEquals(expectedPrefix + wrapper + "(reachable))",
				hat.toString(variableNames, false));
	}

	@Test
	@DisplayName("replace a whole hat but reject replacement below its root")
	void replaceWholeHatButRejectReplacementBelowRoot() {
		HatFixture fixture = hatFixture("hat-replacement");
		Variable argument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		Function replacement = new Function(
				symbol("hat-replacement-term", 0), List.of());
		Position belowRootPosition = new Position(0);
		String originalRendering = hat.toString();

		assertSame(replacement, hat.replace(new Position(), replacement));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.replace(belowRootPosition, replacement));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.replaceVariables(replacement));
		assertEquals(originalRendering, hat.toString());
		assertSame(argument, hat.getArgument());
		assertEquals(List.of(2, 3), hat.getExponents());
		assertEquals(replacement.getRootSymbol().toString(), replacement.toString());
	}

	@Test
	@DisplayName("reject left-unification transformations without changing inputs")
	void rejectLeftUnificationTransformationsWithoutChangingInputs() {
		HatFixture fixture = hatFixture("hat-left-unification");
		Variable argument = new Variable();
		Variable mappedVariable = new Variable();
		Function mappedTerm = new Function(
				symbol("hat-left-unification-mapped", 0), List.of());
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		Substitution substitution = new Substitution();
		substitution.add(mappedVariable, mappedTerm);
		LuEquation equation = new LuEquation(new Variable(), new Variable());
		String originalRendering = hat.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> hat.distribute(2));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.reduceWithLeftUnificationRule(equation));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.applyAndCompleteRho(substitution));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.applyInPlace(substitution));
		assertEquals(originalRendering, hat.toString());
		assertSame(argument, hat.getArgument());
		assertEquals(List.of(2, 3), hat.getExponents());
		assertSame(mappedTerm, substitution.get(mappedVariable));
	}

	@Test
	@DisplayName("reject generic structure and distinct destructive unification")
	void rejectGenericStructureAndDistinctDestructiveUnification() {
		HatFixture fixture = hatFixture("hat-generic-unification");
		Variable argument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		HatFunction other = new HatFunction(
				fixture.hatSymbol(), new Variable(), List.of(2, 3));
		String hatRendering = hat.toString();
		String otherRendering = other.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> hat.hasSameStructureAs(other));
		assertTrue(hat.unifyWith(hat));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.unifyWith(other));
		assertEquals(hatRendering, hat.toString());
		assertEquals(otherRendering, other.toString());
		assertSame(argument, hat.getArgument());
	}

	@Test
	@DisplayName("reject inner rewriting after inspecting ordinary root rules")
	void rejectInnerRewritingAfterInspectingOrdinaryRootRules() {
		HatFixture fixture = hatFixture("hat-rewriting");
		Variable argument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		Variable ruleVariable = new Variable();
		Function ruleLeft = new Function(
				symbol("hat-rewriting-left", 1), List.of(ruleVariable));
		Function ruleRight = new Function(
				symbol("hat-rewriting-right", 1), List.of(ruleVariable));
		RuleTrs rule = new RuleTrs(ruleLeft, ruleRight);
		Trs trs = new Trs("hat-rewriting", List.of(rule), "FULL");
		String hatRendering = hat.toString();
		String ruleRendering = rule.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> hat.rewriteWith(trs));
		assertEquals(hatRendering, hat.toString());
		assertEquals(ruleRendering, rule.toString());
		assertSame(argument, hat.getArgument());
		assertSame(ruleLeft, rule.getLeft());
		assertSame(ruleRight, rule.getRight());
	}

	@Test
	@DisplayName("distinguish root and inner unfolding side effects")
	void distinguishRootAndInnerUnfoldingSideEffects() {
		HatFixture fixture = hatFixture("hat-unfolding");
		Variable argument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		Variable ruleVariable = new Variable();
		Function ruleLeft = new Function(
				symbol("hat-unfolding-left", 1), List.of(ruleVariable));
		Function ruleRight = new Function(
				symbol("hat-unfolding-right", 1), List.of(ruleVariable));
		RuleTrs rule = new RuleTrs(ruleLeft, ruleRight);
		Map<Term, Term> rootCopies = new HashMap<>();
		Map<Term, Term> innerCopies = new HashMap<>();
		Variable sentinel = new Variable();
		innerCopies.put(sentinel, sentinel);
		Position rootPosition = new Position();
		Position innerPosition = new Position(0);
		String hatRendering = hat.toString();
		String ruleRendering = rule.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> hat.unfoldWith(
						rule, rootPosition, false, false, rootCopies));
		assertFalse(rootCopies.containsKey(hat));
		assertTrue(rootCopies.containsKey(argument));
		assertNotSame(argument, rootCopies.get(argument));

		assertThrows(UnsupportedOperationException.class,
				() -> hat.unfoldWith(
						rule, innerPosition, true, true, innerCopies));
		assertEquals(1, innerCopies.size());
		assertSame(sentinel, innerCopies.get(sentinel));
		assertEquals("[0]", innerPosition.toString());
		assertEquals(hatRendering, hat.toString());
		assertEquals(ruleRendering, rule.toString());
		assertSame(argument, hat.getArgument());
	}

	@Test
	@DisplayName("preserve identity fast paths but reject delegated orders")
	void preserveIdentityFastPathsButRejectDelegatedOrders() {
		HatFixture fixture = hatFixture("hat-orders");
		Variable sharedArgument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), sharedArgument, List.of(2, 3));
		HatFunction equivalent = new HatFunction(
				fixture.hatSymbol(), sharedArgument, List.of(0, 2, 3));
		HatFunction distinct = new HatFunction(
				fixture.hatSymbol(), sharedArgument, List.of(2, 4));
		LexOrder order = new LexOrder();
		WeightFunction weights = new WeightFunction();
		String orderRendering = order.toString();

		assertTrue(hat.embeds(hat));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.embeds(distinct));
		assertTrue(hat.completeLPO(order, equivalent));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.completeLPOStrict(order, distinct));
		assertTrue(hat.completeKBO(order, weights, equivalent));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.completeKBOStrict(order, weights, distinct));
		assertEquals(orderRendering, order.toString());
		assertTrue(weights.getAllCoefficients().isEmpty());
		assertSame(sharedArgument, hat.getArgument());
	}

	@Test
	@DisplayName("reject interpretations weights and root conversions")
	void rejectInterpretationsWeightsAndRootConversions() {
		HatFixture fixture = hatFixture("hat-interpretation");
		Variable argument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		PolyInterpretation interpretation = new PolyInterpretation();
		WeightFunction weights = new WeightFunction();
		Trs emptyTrs = new Trs("hat-connectability", List.of(), "FULL");
		Variable target = new Variable();
		String originalRendering = hat.toString();

		assertThrows(UnsupportedOperationException.class,
				() -> hat.toPolynomial(interpretation));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.generateKBOWeights(weights));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.getWeight(weights));
		assertThrows(UnsupportedOperationException.class, hat::toTuple);
		assertThrows(UnsupportedOperationException.class, hat::toFunction);
		assertThrows(UnsupportedOperationException.class,
				() -> hat.isConnectableTo(target, emptyTrs));
		assertTrue(interpretation.getAllCoefficients().isEmpty());
		assertTrue(weights.getAllCoefficients().isEmpty());
		assertEquals(originalRendering, hat.toString());
		assertSame(argument, hat.getArgument());
	}

	@Test
	@DisplayName("reject argument filtering before collaborator mutation")
	void rejectArgumentFilteringBeforeCollaboratorMutation() {
		HatFixture fixture = hatFixture("hat-filtering");
		Variable argument = new Variable();
		HatFunction hat = new HatFunction(
				fixture.hatSymbol(), argument, List.of(2, 3));
		ArgFiltering filtering = new ArgFiltering();

		assertThrows(UnsupportedOperationException.class,
				() -> hat.buildFilters(filtering));
		assertThrows(UnsupportedOperationException.class,
				() -> hat.applyFilters(filtering));
		assertTrue(filtering.getAllFilters().isEmpty());
		assertSame(argument, hat.getArgument());
		assertEquals(List.of(2, 3), hat.getExponents());
	}

	private static List<String> positionLabels(Iterator<Position> positions) {
		List<String> labels = new ArrayList<>();
		while (positions.hasNext()) {
			Position position = positions.next();
			labels.add(position.isEmpty() ? "root" : position.toString());
		}
		return labels;
	}

	private static void assertHat(
			Term term,
			HatFunctionSymbol expectedSymbol,
			Term expectedArgument,
			Integer... expectedExponents) {

		HatFunction hat = (HatFunction) term;
		assertSame(expectedSymbol, hat.getRootSymbol());
		assertSame(expectedArgument, hat.getArgument());
		assertEquals(List.of(expectedExponents), hat.getExponents());
	}

	private static HatFixture hatFixture(String prefix) {
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol = symbol(prefix, 1);
		Function context = new Function(
				contextSymbol, List.of(contextVariable));
		return new HatFixture(
				contextSymbol,
				HatFunctionSymbol.intern(context, contextVariable));
	}

	private static FunctionSymbol symbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}

	private record HatFixture(
			FunctionSymbol contextSymbol,
			HatFunctionSymbol hatSymbol) {}
}
