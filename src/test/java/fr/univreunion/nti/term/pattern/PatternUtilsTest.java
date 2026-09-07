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

package fr.univreunion.nti.term.pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class PatternUtilsTest {

	@Test
	@DisplayName("reject null simplify arguments at the public boundary")
	void rejectNullSimplifyArgumentsAtThePublicBoundary() {
		Substitution substitution = new Substitution();
		NullPointerException nullTermException = assertThrows(
				NullPointerException.class,
				() -> PatternUtils.simplify(null, substitution));
		NullPointerException nullSubstitutionException = assertThrows(
				NullPointerException.class,
				() -> PatternUtils.simplify(new Variable(), null));

		assertEquals("term", nullTermException.getMessage());
		assertEquals("substitution", nullSubstitutionException.getMessage());
	}

	@Test
	@DisplayName("leave terms and substitutions without hats unchanged")
	void leaveTermsAndSubstitutionsWithoutHatsUnchanged() {
		Variable variable = new Variable();
		Function source = new Function(
				uniqueSymbol("pattern-simplify-ordinary-source", 1),
				List.of(variable));
		Function ordinaryImage = constant("pattern-simplify-ordinary-image");
		Substitution substitution = new Substitution();
		substitution.add(variable, ordinaryImage);

		assertSame(source, PatternUtils.simplify(source, substitution));
		assertSame(ordinaryImage, substitution.get(variable));
		assertSame(variable, source.getChild(0));
	}

	@Test
	@DisplayName("ignore a hat mapping whose variable is absent from the term")
	void ignoreAHatMappingWhoseVariableIsAbsentFromTheTerm() {
		Variable absentVariable = new Variable();
		Function source = constant("pattern-simplify-absent-source");
		HatFunction hatFunction = hatFunction(
				"pattern-simplify-absent-context", 1, 2);
		Substitution substitution = new Substitution();
		substitution.add(absentVariable, hatFunction);

		assertSame(source, PatternUtils.simplify(source, substitution));
		assertSame(hatFunction, substitution.get(absentVariable));
		assertEquals(2, hatFunction.getB());
	}

	@Test
	@DisplayName("shift hats by the minimum tower across repeated occurrences")
	void shiftHatsByTheMinimumTowerAcrossRepeatedOccurrences() {
		Variable variable = new Variable();
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol =
				uniqueSymbol("pattern-simplify-context", 1);
		Function context = new Function(
				contextSymbol, List.of(contextVariable));
		HatFunctionSymbol hatSymbol =
				HatFunctionSymbol.intern(context, contextVariable);
		HatFunction originalHat = new HatFunction(
				hatSymbol, constant("pattern-simplify-hat-base"), 1, 2);
		Function oneLevel = new Function(contextSymbol, List.of(variable));
		Function threeLevels = new Function(contextSymbol, List.of(
				new Function(contextSymbol, List.of(
						new Function(contextSymbol, List.of(variable))))));
		FunctionSymbol sourceSymbol = uniqueSymbol("pattern-simplify-source", 2);
		Function source = new Function(
				sourceSymbol, List.of(oneLevel, threeLevels));
		Term sourceSnapshot = source.shallowCopy();
		Substitution substitution = new Substitution();
		substitution.add(variable, originalHat);

		Term simplified = PatternUtils.simplify(source, substitution);
		HatFunction shiftedHat =
				(HatFunction) substitution.get(variable);
		Function expectedRemainder = new Function(contextSymbol, List.of(
				new Function(contextSymbol, List.of(variable))));
		Function expected = new Function(
				sourceSymbol, List.of(variable, expectedRemainder));

		assertTrue(expected.deepEquals(simplified));
		assertTrue(sourceSnapshot.deepEquals(source));
		assertNotSame(originalHat, shiftedHat);
		assertEquals(2, originalHat.getB());
		assertEquals(3, shiftedHat.getB());
		assertEquals(originalHat.getExponents().get(0),
				shiftedHat.getExponents().get(0));
	}

	@Test
	@DisplayName("reject closing-exponent overflow while simplifying a hat mapping")
	void rejectClosingExponentOverflowWhileSimplifyingAHatMapping() {
		Variable variable = new Variable();
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol =
				uniqueSymbol("pattern-simplify-overflow-context", 1);
		Function context = new Function(
				contextSymbol, List.of(contextVariable));
		HatFunction originalHat = new HatFunction(
				HatFunctionSymbol.intern(context, contextVariable),
				constant("pattern-simplify-overflow-base"),
				1, Integer.MAX_VALUE);
		Function source = new Function(contextSymbol, List.of(variable));
		Substitution substitution = new Substitution();
		substitution.add(variable, originalHat);

		assertThrows(
				ArithmeticException.class,
				() -> PatternUtils.simplify(source, substitution));
		assertSame(originalHat, substitution.get(variable));
		assertEquals(
				List.of(1, Integer.MAX_VALUE), originalHat.getExponents());
		assertSame(variable, source.getChild(0));
	}

	@Test
	@DisplayName("handle identity and missing-variable contexts")
	void handleIdentityAndMissingVariableContexts() {
		Variable contextVariable = new Variable();
		Variable otherVariable = new Variable();
		Function groundTerm = constant("pattern-get-context-ground");
		Function termWithoutContextVariable = new Function(
				uniqueSymbol("pattern-get-context-absent", 1),
				List.of(otherVariable));
		int[] exponent = {99};

		assertSame(contextVariable, PatternUtils.getContext(
				contextVariable, contextVariable, exponent));
		assertEquals(0, exponent[0]);
		assertNull(PatternUtils.getContext(
				otherVariable, contextVariable, exponent));
		assertEquals(0, exponent[0]);
		assertNull(PatternUtils.getContext(
				groundTerm, contextVariable, exponent));
		assertEquals(0, exponent[0]);
		assertNull(PatternUtils.getContext(
				termWithoutContextVariable, contextVariable, exponent));
		assertEquals(0, exponent[0]);
	}

	@Test
	@DisplayName("extract the smallest repeated-hole context and exponent")
	void extractTheSmallestRepeatedHoleContextAndExponent() {
		Variable contextVariable = new Variable();
		Function fixedArgument = constant("pattern-get-context-fixed");
		FunctionSymbol contextSymbol = uniqueSymbol("pattern-get-context-shared", 3);
		Function originalContext = new Function(contextSymbol,
				List.of(contextVariable, fixedArgument, contextVariable));
		Term tower = PatternUtils.embed(
				originalContext, contextVariable, 3, contextVariable);
		Term towerSnapshot = tower.shallowCopy();
		int[] exponent = {-1};

		Function extractedContext = (Function) PatternUtils.getContext(
				tower, contextVariable, exponent);

		assertEquals(3, exponent[0]);
		assertSame(contextSymbol, extractedContext.getRootSymbol());
		assertSame(contextVariable, extractedContext.getChild(0));
		assertNotSame(fixedArgument, extractedContext.getChild(1));
		assertTrue(fixedArgument.deepEquals(extractedContext.getChild(1)));
		assertSame(tower.get(1), extractedContext.getChild(1));
		assertSame(contextVariable, extractedContext.getChild(2));
		assertTrue(originalContext.deepEquals(extractedContext));
		assertTrue(towerSnapshot.deepEquals(tower));
	}

	@Test
	@DisplayName("reject inconsistent non-ground hole contents")
	void rejectInconsistentNonGroundHoleContents() {
		Variable contextVariable = new Variable();
		Function nestedVariable = new Function(
				uniqueSymbol("pattern-get-context-nested", 1),
				List.of(contextVariable));
		Function inconsistent = new Function(
				uniqueSymbol("pattern-get-context-inconsistent", 2),
				List.of(contextVariable, nestedVariable));
		int[] exponent = {99};

		assertNull(PatternUtils.getContext(
				inconsistent, contextVariable, exponent));
		assertEquals(0, exponent[0]);
		assertSame(contextVariable, inconsistent.getChild(0));
		assertSame(nestedVariable, inconsistent.getChild(1));
	}

	@Test
	@DisplayName("embed a shared-hole context repeatedly without mutation")
	void embedASharedHoleContextRepeatedlyWithoutMutation() {
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol = uniqueSymbol("pattern-embed-context", 2);
		Function context = new Function(
				contextSymbol, List.of(contextVariable, contextVariable));
		Function baseTerm = constant("pattern-embed-base");

		Term zero = PatternUtils.embed(context, contextVariable, 0, baseTerm);
		Term negative = PatternUtils.embed(context, contextVariable, -1, baseTerm);
		Term two = PatternUtils.embed(context, contextVariable, 2, baseTerm);
		Function firstLevel = new Function(
				contextSymbol, List.of(baseTerm, baseTerm));
		Function expectedTwo = new Function(
				contextSymbol, List.of(firstLevel, firstLevel));

		assertNotSame(baseTerm, zero);
		assertTrue(baseTerm.deepEquals(zero));
		assertNotSame(baseTerm, negative);
		assertTrue(baseTerm.deepEquals(negative));
		assertTrue(expectedTwo.deepEquals(two));
		assertSame(contextVariable, context.getChild(0));
		assertSame(contextVariable, context.getChild(1));
	}

	@Test
	@DisplayName("recognize exact towers with shared holes")
	void recognizeExactTowersWithSharedHoles() {
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol = uniqueSymbol("pattern-exact-context", 2);
		Function context = new Function(
				contextSymbol, List.of(contextVariable, contextVariable));
		Function baseTerm = constant("pattern-exact-base");
		Term tower = PatternUtils.embed(context, contextVariable, 2, baseTerm);

		assertEquals(2, PatternUtils.towerOfContexts(
				tower, context, contextVariable, baseTerm));
		assertEquals(0, PatternUtils.towerOfContexts(
				baseTerm, context, contextVariable, baseTerm));
		assertEquals(0, PatternUtils.towerOfContexts(
				tower, contextVariable, contextVariable, baseTerm));
		assertEquals(-1, PatternUtils.towerOfContexts(
				tower, context, contextVariable,
				constant("pattern-exact-wrong-base")));
		assertEquals(-1, PatternUtils.towerOfContexts(
				null, context, contextVariable, baseTerm));
		assertSame(contextVariable, context.getChild(0));
		assertSame(contextVariable, context.getChild(1));
	}

	@Test
	@DisplayName("reject inconsistent holes and fixed context arguments")
	void rejectInconsistentHolesAndFixedContextArguments() {
		Variable contextVariable = new Variable();
		Function fixedArgument = constant("pattern-context-fixed");
		FunctionSymbol contextSymbol = uniqueSymbol("pattern-context-validation", 3);
		Function context = new Function(contextSymbol,
				List.of(contextVariable, fixedArgument, contextVariable));
		Function baseTerm = constant("pattern-context-base");
		Function inconsistentHoles = new Function(contextSymbol,
				List.of(baseTerm, fixedArgument,
						constant("pattern-context-other-hole")));
		Function inconsistentFixedArgument = new Function(contextSymbol,
				List.of(baseTerm, constant("pattern-context-other-fixed"), baseTerm));

		assertEquals(-1, PatternUtils.towerOfContexts(
				inconsistentHoles, context, contextVariable, baseTerm));
		assertEquals(-1, PatternUtils.towerOfContexts(
				inconsistentFixedArgument, context, contextVariable, baseTerm));
	}

	@Test
	@DisplayName("extract the maximal consistent tower prefix")
	void extractTheMaximalConsistentTowerPrefix() {
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol = uniqueSymbol("pattern-prefix-context", 2);
		Function context = new Function(
				contextSymbol, List.of(contextVariable, contextVariable));
		Function baseTerm = constant("pattern-prefix-base");
		Term tower = PatternUtils.embed(context, contextVariable, 2, baseTerm);
		int[] exponent = {-1};

		Term extractedBase = PatternUtils.towerOfContexts(
				tower, context, contextVariable, exponent);

		assertEquals(2, exponent[0]);
		assertTrue(baseTerm.deepEquals(extractedBase));

		Function inconsistent = new Function(contextSymbol,
				List.of(baseTerm, constant("pattern-prefix-inconsistent")));
		assertSame(inconsistent, PatternUtils.towerOfContexts(
				inconsistent, context, contextVariable, exponent));
		assertEquals(0, exponent[0]);
		assertSame(tower, PatternUtils.towerOfContexts(
				tower, contextVariable, contextVariable, exponent));
		assertEquals(0, exponent[0]);
		assertSame(baseTerm, PatternUtils.towerOfContexts(
				baseTerm, context, contextVariable, exponent));
		assertEquals(0, exponent[0]);
	}

	private static Function constant(String prefix) {
		return new Function(uniqueSymbol(prefix, 0), List.of());
	}

	private static HatFunction hatFunction(
			String prefix, int pumpingExponent, int closingExponent) {
		Variable contextVariable = new Variable();
		Function context = new Function(
				uniqueSymbol(prefix, 1), List.of(contextVariable));
		return new HatFunction(
				HatFunctionSymbol.intern(context, contextVariable),
				constant(prefix + "-base"),
				pumpingExponent, closingExponent);
	}

	private static FunctionSymbol uniqueSymbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}
}
