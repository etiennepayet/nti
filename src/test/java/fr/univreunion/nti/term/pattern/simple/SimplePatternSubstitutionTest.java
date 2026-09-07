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

package fr.univreunion.nti.term.pattern.simple;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternSubstitution;

class SimplePatternSubstitutionTest {

	@Test
	@DisplayName("build independent empty simple pattern substitutions")
	void buildIndependentEmptySimplePatternSubstitutions() {
		SimplePatternSubstitution first = SimplePatternSubstitution.empty();
		SimplePatternSubstitution second = SimplePatternSubstitution.empty();

		assertEquals(1, first.getArity());
		assertTrue(first.getPumping().isEmpty());
		assertTrue(first.getClosing().isEmpty());
		assertTrue(first.getHatFunctionSubstitution().isEmpty());
		assertEquals("{}", first.toString());
		assertNotSame(first, second);
		assertNotSame(first.getPumping(), second.getPumping());
		assertNotSame(first.getClosing(), second.getClosing());
		assertNotSame(first.getHatFunctionSubstitution(),
				second.getHatFunctionSubstitution());
	}

	@Test
	@DisplayName("build multi-arity hats from the union of substitution domains")
	void buildMultiArityHatsFromTheUnionOfSubstitutionDomains() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		Variable closingOnlyVariable = new Variable();
		FunctionSymbol firstContextSymbol =
				uniqueSymbol("simple-pattern-first-context", 1);
		FunctionSymbol secondContextSymbol =
				uniqueSymbol("simple-pattern-second-context", 1);
		Function firstBase = constant("simple-pattern-first-base");
		Function secondBase = constant("simple-pattern-second-base");
		Function closingOnlyImage = constant("simple-pattern-closing-only");
		Substitution firstPumping = new Substitution();
		firstPumping.add(firstVariable,
				new Function(firstContextSymbol, List.of(firstVariable)));
		Substitution secondPumping = new Substitution();
		secondPumping.add(secondVariable,
				new Function(secondContextSymbol, List.of(secondVariable)));
		Substitution closing = new Substitution();
		closing.add(firstVariable, new Function(firstContextSymbol, List.of(
				new Function(firstContextSymbol, List.of(firstBase)))));
		closing.add(secondVariable, secondBase);
		closing.add(closingOnlyVariable, closingOnlyImage);

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(
						List.of(firstPumping, secondPumping, closing));
		Iterator<Substitution> substitutions = patternSubstitution.iterator();
		HatFunction firstHat = assertInstanceOf(HatFunction.class,
				patternSubstitution.getHatFunctionSubstitution().get(firstVariable));
		HatFunction secondHat = assertInstanceOf(HatFunction.class,
				patternSubstitution.getHatFunctionSubstitution().get(secondVariable));

		assertEquals(2, patternSubstitution.getArity());
		assertSame(firstPumping, substitutions.next());
		assertSame(secondPumping, substitutions.next());
		assertSame(closing, substitutions.next());
		assertEquals(List.of(1, 0, 2), firstHat.getExponents());
		assertTrue(firstBase.deepEquals(firstHat.getArgument()));
		assertEquals(List.of(0, 1, 0), secondHat.getExponents());
		assertTrue(secondBase.deepEquals(secondHat.getArgument()));
		assertSame(closingOnlyImage,
				patternSubstitution.getHatFunctionSubstitution()
						.get(closingOnlyVariable));
	}

	@Test
	@DisplayName("recover arity and expose a shallow mutable hat representation")
	void recoverArityAndExposeAShallowMutableHatRepresentation() {
		Variable variable = new Variable();
		Variable plainVariable = new Variable();
		HatFunction hatFunction = hatFunction(
				"simple-pattern-recovery", List.of(2, 1, 3));
		Function plainImage = constant("simple-pattern-recovery-plain");
		Substitution source = new Substitution();
		source.add(variable, hatFunction);
		source.add(plainVariable, plainImage);

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(source);
		Substitution exposedHatSubstitution =
				patternSubstitution.getHatFunctionSubstitution();

		assertEquals(2, patternSubstitution.getArity());
		assertSame(hatFunction, exposedHatSubstitution.get(variable));
		assertSame(plainImage, exposedHatSubstitution.get(plainVariable));
		assertEquals(List.of(2, 1, 3),
				((HatFunction) exposedHatSubstitution.get(variable)).getExponents());
		assertFalse(patternSubstitution.getPumping().isEmpty());
		exposedHatSubstitution.clear();
		assertTrue(patternSubstitution.getHatFunctionSubstitution().isEmpty());
		assertSame(hatFunction, source.get(variable));
		assertSame(plainImage, source.get(plainVariable));
		assertFalse(patternSubstitution.getPumping().isEmpty());
	}

	@Test
	@DisplayName("take ownership of a fresh hat-function substitution")
	void takeOwnershipOfAFreshHatFunctionSubstitution() {
		Variable variable = new Variable();
		Substitution owned = new Substitution();
		owned.add(variable, constant("simple-pattern-owned"));

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuildTakingOwnership(owned);

		assertSame(owned, patternSubstitution.getHatFunctionSubstitution());
		assertSame(owned.get(variable),
				patternSubstitution.getClosing().get(variable));
	}

	@Test
	@DisplayName("compose from left to right and preserve the first domain")
	void composeFromLeftToRightAndPreserveTheFirstDomain() {
		Variable firstDomainVariable = new Variable();
		Variable intermediateVariable = new Variable();
		Variable secondOnlyVariable = new Variable();
		Function composedImage = constant("simple-pattern-composed-image");
		Function shadowedImage = constant("simple-pattern-shadowed-image");
		Function secondOnlyImage = constant("simple-pattern-second-only-image");
		Substitution firstHatSubstitution = new Substitution();
		firstHatSubstitution.add(firstDomainVariable, intermediateVariable);
		Substitution secondHatSubstitution = new Substitution();
		secondHatSubstitution.add(intermediateVariable, composedImage);
		secondHatSubstitution.add(firstDomainVariable, shadowedImage);
		secondHatSubstitution.add(secondOnlyVariable, secondOnlyImage);
		SimplePatternSubstitution first =
				SimplePatternSubstitution.tryBuild(firstHatSubstitution);
		SimplePatternSubstitution second =
				SimplePatternSubstitution.tryBuild(secondHatSubstitution);

		SimplePatternSubstitution composition = first.composeWith(second);
		Substitution composedHatSubstitution =
				composition.getHatFunctionSubstitution();

		assertTrue(composedImage.deepEquals(
				composedHatSubstitution.get(firstDomainVariable)));
		assertFalse(shadowedImage.deepEquals(
				composedHatSubstitution.get(firstDomainVariable)));
		assertSame(composedImage,
				composedHatSubstitution.get(intermediateVariable));
		assertSame(secondOnlyImage,
				composedHatSubstitution.get(secondOnlyVariable));
		assertSame(intermediateVariable,
				first.getHatFunctionSubstitution().get(firstDomainVariable));
		assertSame(shadowedImage,
				second.getHatFunctionSubstitution().get(firstDomainVariable));
	}

	@Test
	@DisplayName("reject a non-simple composition operand")
	void rejectANonSimpleCompositionOperand() {
		assertNull(SimplePatternSubstitution.empty().composeWith(
				new NonSimplePatternSubstitution()));
	}

	@Test
	@DisplayName("propagate a composition that creates a nested hat function")
	void propagateACompositionThatCreatesANestedHatFunction() {
		Variable domainVariable = new Variable();
		Variable intermediateVariable = new Variable();
		HatFunction outerHat = hatFunction(
				"simple-pattern-outer-hat", intermediateVariable, List.of(1, 0));
		HatFunction innerHat = hatFunction(
				"simple-pattern-inner-hat", List.of(1, 0));
		Substitution firstHatSubstitution = new Substitution();
		firstHatSubstitution.add(domainVariable, outerHat);
		Substitution secondHatSubstitution = new Substitution();
		secondHatSubstitution.add(intermediateVariable, innerHat);
		SimplePatternSubstitution first =
				SimplePatternSubstitution.tryBuild(firstHatSubstitution);
		SimplePatternSubstitution second =
				SimplePatternSubstitution.tryBuild(secondHatSubstitution);

		assertNull(first.composeWith(second));
		assertSame(outerHat,
				first.getHatFunctionSubstitution().get(domainVariable));
		assertSame(innerHat,
				second.getHatFunctionSubstitution().get(intermediateVariable));
	}

	@Test
	@DisplayName("deep copy reuses canonical variable copies across representations")
	void deepCopyReusesCanonicalVariableCopiesAcrossRepresentations() {
		Variable domainVariable = new Variable();
		Variable otherVariable = new Variable();
		Variable predefinedOtherCopy = new Variable();
		FunctionSymbol argumentSymbol =
				uniqueSymbol("simple-pattern-copy-argument", 3);
		Function argument = new Function(argumentSymbol, List.of(
				domainVariable, otherVariable, domainVariable));
		HatFunction sourceHat = hatFunction(
				"simple-pattern-copy", argument, List.of(1, 0));
		Substitution sourceHatSubstitution = new Substitution();
		sourceHatSubstitution.add(domainVariable, sourceHat);
		SimplePatternSubstitution source =
				SimplePatternSubstitution.tryBuild(sourceHatSubstitution);
		Map<Term, Term> copies = new HashMap<>();
		copies.put(otherVariable, predefinedOtherCopy);

		SimplePatternSubstitution copy = source.deepCopy(copies);
		Variable copiedDomainVariable =
				copy.getHatFunctionSubstitution().getDomain().iterator().next();
		HatFunction copiedHat = assertInstanceOf(HatFunction.class,
				copy.getHatFunctionSubstitution().get(copiedDomainVariable));
		Function copiedArgument =
				assertInstanceOf(Function.class, copiedHat.getArgument());
		Function copiedClosingImage = assertInstanceOf(Function.class,
				copy.getClosing().get(copiedDomainVariable));

		assertNotSame(domainVariable, copiedDomainVariable);
		assertSame(copiedDomainVariable, copies.get(domainVariable));
		assertNotSame(sourceHat, copiedHat);
		assertSame(sourceHat.getRootSymbol(), copiedHat.getRootSymbol());
		assertSame(copiedDomainVariable, copiedArgument.getChild(0));
		assertSame(predefinedOtherCopy, copiedArgument.getChild(1));
		assertSame(copiedDomainVariable, copiedArgument.getChild(2));
		assertSame(copiedDomainVariable, copiedClosingImage.getChild(0));
		assertSame(predefinedOtherCopy, copiedClosingImage.getChild(1));
		assertSame(copiedDomainVariable, copiedClosingImage.getChild(2));

		copy.getHatFunctionSubstitution().clear();
		copy.getPumping().clear();
		assertFalse(source.getHatFunctionSubstitution().isEmpty());
		assertFalse(source.getPumping().isEmpty());
	}

	@Test
	@DisplayName("reject malformed pumping and closing substitution lists")
	void rejectMalformedPumpingAndClosingSubstitutionLists() {
		assertThrows(NullPointerException.class,
				() -> SimplePatternSubstitution.tryBuild(
						(List<Substitution>) null));
		assertThrows(IllegalArgumentException.class,
				() -> SimplePatternSubstitution.tryBuild(List.of()));
		assertThrows(IllegalArgumentException.class,
				() -> SimplePatternSubstitution.tryBuild(
						List.of(new Substitution())));
	}

	@Test
	@DisplayName("accept identity pumping images and reject non-context images")
	void acceptIdentityPumpingImagesAndRejectNonContextImages() {
		Variable variable = new Variable();
		Variable foreignVariable = new Variable();
		Function closingImage = constant("simple-pattern-identity-closing");
		Substitution identityPumping = new Substitution();
		identityPumping.add(variable, variable);
		Substitution closing = new Substitution();
		closing.add(variable, closingImage);

		SimplePatternSubstitution identityPattern =
				SimplePatternSubstitution.tryBuild(
						List.of(identityPumping, closing));

		assertNotNull(identityPattern);
		assertSame(closingImage,
				identityPattern.getHatFunctionSubstitution().get(variable));
		assertSame(variable, identityPattern.getPumping().get(variable));

		Substitution foreignVariablePumping = new Substitution();
		foreignVariablePumping.add(variable, foreignVariable);
		assertNull(SimplePatternSubstitution.tryBuild(
				List.of(foreignVariablePumping, closing)));

		Substitution groundPumping = new Substitution();
		groundPumping.add(variable,
				constant("simple-pattern-ground-pumping"));
		assertNull(SimplePatternSubstitution.tryBuild(
				List.of(groundPumping, closing)));
	}

	@Test
	@DisplayName("extract the maximal closing prefix and preserve its remainder")
	void extractTheMaximalClosingPrefixAndPreserveItsRemainder() {
		Variable variable = new Variable();
		FunctionSymbol contextSymbol =
				uniqueSymbol("simple-pattern-closing-prefix-context", 1);
		Function base = constant("simple-pattern-closing-prefix-base");
		Function remainder = new Function(
				uniqueSymbol("simple-pattern-closing-prefix-remainder", 1),
				List.of(base));
		Substitution pumping = new Substitution();
		pumping.add(variable,
				new Function(contextSymbol, List.of(variable)));
		Substitution closing = new Substitution();
		closing.add(variable, new Function(contextSymbol, List.of(
				new Function(contextSymbol, List.of(remainder)))));

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(List.of(pumping, closing));
		HatFunction hatFunction = assertInstanceOf(HatFunction.class,
				patternSubstitution.getHatFunctionSubstitution().get(variable));

		assertEquals(List.of(1, 2), hatFunction.getExponents());
		assertSame(remainder, hatFunction.getArgument());
	}

	@Test
	@DisplayName("normalize mixed recovered hat arities in both discovery orders")
	void normalizeMixedRecoveredHatAritiesInBothDiscoveryOrders() {
		assertMixedRecoveredHatArities(true);
		assertMixedRecoveredHatArities(false);
	}

	/** Checks mixed recovery after assigning images in the selected discovery order. */
	private void assertMixedRecoveredHatArities(boolean shortHatFirst) {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		HatFunction shortHat = hatFunction(
				"simple-pattern-short-hat", List.of(2, 3));
		HatFunction longHat = hatFunction(
				"simple-pattern-long-hat", List.of(4, 5, 6, 7));
		Substitution source = new Substitution();
		source.add(firstVariable, shortHat);
		source.add(secondVariable, longHat);
		Iterator<Map.Entry<Variable, Term>> entries = source.iterator();
		Variable firstDiscovered = entries.next().getKey();
		Variable secondDiscovered = entries.next().getKey();
		Variable shortHatVariable = shortHatFirst ?
				firstDiscovered : secondDiscovered;
		Variable longHatVariable = shortHatFirst ?
				secondDiscovered : firstDiscovered;
		source.addReplace(shortHatVariable, shortHat);
		source.addReplace(longHatVariable, longHat);
		assertSame(shortHatFirst ? shortHatVariable : longHatVariable,
				source.iterator().next().getKey());

		SimplePatternSubstitution recovered =
				SimplePatternSubstitution.tryBuild(source);
		List<Substitution> recoveredSubstitutions = new ArrayList<>();
		recovered.forEach(recoveredSubstitutions::add);
		SimplePatternSubstitution normalized =
				SimplePatternSubstitution.tryBuild(recoveredSubstitutions);
		HatFunction normalizedShortHat = assertInstanceOf(HatFunction.class,
				normalized.getHatFunctionSubstitution().get(shortHatVariable));
		HatFunction normalizedLongHat = assertInstanceOf(HatFunction.class,
				normalized.getHatFunctionSubstitution().get(longHatVariable));

		assertEquals(3, recovered.getArity());
		assertEquals(List.of(0, 0, 2, 3),
				normalizedShortHat.getExponents());
		assertEquals(List.of(4, 5, 6, 7),
				normalizedLongHat.getExponents());
		assertSame(shortHat, source.get(shortHatVariable));
		assertSame(longHat, source.get(longHatVariable));
	}

	private static HatFunction hatFunction(
			String prefix, List<Integer> exponents) {
		return hatFunction(prefix, constant(prefix + "-base"), exponents);
	}

	private static HatFunction hatFunction(
			String prefix, Term argument, List<Integer> exponents) {
		Variable contextVariable = new Variable();
		Function context = new Function(
				uniqueSymbol(prefix + "-context", 1), List.of(contextVariable));
		return new HatFunction(
				HatFunctionSymbol.intern(context, contextVariable),
				argument, exponents);
	}

	private static Function constant(String prefix) {
		return new Function(uniqueSymbol(prefix, 0), List.of());
	}

	private static FunctionSymbol uniqueSymbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}

	private static final class NonSimplePatternSubstitution
			extends PatternSubstitution {

		@Override
		public PatternSubstitution composeWith(
				PatternSubstitution otherPatternSubstitution) {
			return null;
		}

		@Override
		public PatternSubstitution deepCopy() {
			return null;
		}

		@Override
		public PatternSubstitution deepCopy(Map<Term, Term> copies) {
			return null;
		}
	}
}
