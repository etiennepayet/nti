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
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternSubstitution;

class SimplePatternTermTest {

	@Test
	@DisplayName("build a starred term with shared base and upsilon")
	void buildAStarredTermWithSharedBaseAndUpsilon() {
		Function baseTerm = new Function(
				uniqueSymbol("simple-pattern-starred", 1),
				List.of(new Variable()));

		SimplePatternTerm patternTerm = SimplePatternTerm.of(baseTerm);

		assertSame(baseTerm, patternTerm.getBaseTerm());
		assertSame(baseTerm, patternTerm.getUpsilon());
		assertTrue(patternTerm.getPatternSubstitution()
				.getHatFunctionSubstitution().isEmpty());
	}

	@Test
	@DisplayName("reject a non-simple pattern substitution")
	void rejectANonSimplePatternSubstitution() {
		assertNull(SimplePatternTerm.tryBuild(
				new Variable(), new NonSimplePatternSubstitution()));
	}

	@Test
	@DisplayName("restrict mappings and extract ground arguments during construction")
	void restrictMappingsAndExtractGroundArgumentsDuringConstruction() {
		Variable usedVariable = new Variable();
		Variable unusedVariable = new Variable();
		Function groundArgument = constant("simple-pattern-ground-argument");
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-construction-base", 2);
		Function sourceBase = new Function(
				baseSymbol, List.of(usedVariable, groundArgument));
		HatFunction usedImage = hatFunction(
				"simple-pattern-used-image", List.of(1, 0));
		Function unusedImage = constant("simple-pattern-unused-image");
		Substitution sourceHatSubstitution = new Substitution();
		sourceHatSubstitution.add(usedVariable, usedImage);
		sourceHatSubstitution.add(unusedVariable, unusedImage);
		SimplePatternSubstitution sourcePatternSubstitution =
				SimplePatternSubstitution.tryBuild(sourceHatSubstitution);

		SimplePatternTerm patternTerm = SimplePatternTerm.tryBuild(
				sourceBase, sourcePatternSubstitution);
		Function normalizedBase = assertInstanceOf(
				Function.class, patternTerm.getBaseTerm());
		Variable groundReplacement = assertInstanceOf(
				Variable.class, normalizedBase.getChild(1));
		Substitution normalizedHatSubstitution = patternTerm
				.getPatternSubstitution().getHatFunctionSubstitution();
		Function upsilon = assertInstanceOf(
				Function.class, patternTerm.getUpsilon());

		assertSame(usedVariable, normalizedBase.getChild(0));
		assertNotSame(usedImage,
				normalizedHatSubstitution.get(usedVariable));
		assertTrue(usedImage.deepEquals(
				normalizedHatSubstitution.get(usedVariable)));
		assertSame(groundArgument,
				normalizedHatSubstitution.get(groundReplacement));
		assertNull(normalizedHatSubstitution.get(unusedVariable));
		assertTrue(usedImage.deepEquals(upsilon.getChild(0)));
		assertTrue(groundArgument.deepEquals(upsilon.getChild(1)));
		assertSame(usedImage, sourceHatSubstitution.get(usedVariable));
		assertSame(unusedImage, sourceHatSubstitution.get(unusedVariable));
		assertSame(groundArgument, sourceBase.getChild(1));
	}

	@Test
	@DisplayName("build from pumping and closing substitutions")
	void buildFromPumpingAndClosingSubstitutions() {
		Variable variable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-three-argument-base", 1);
		FunctionSymbol contextSymbol =
				uniqueSymbol("simple-pattern-three-argument-context", 1);
		Function baseTerm = new Function(baseSymbol, List.of(variable));
		Function closingBase = constant("simple-pattern-three-argument-closing");
		Substitution pumping = new Substitution();
		pumping.add(variable,
				new Function(contextSymbol, List.of(variable)));
		Substitution closing = new Substitution();
		closing.add(variable, closingBase);

		SimplePatternTerm patternTerm =
				SimplePatternTerm.tryBuild(baseTerm, pumping, closing);
		HatFunction upsilonImage = assertInstanceOf(
				HatFunction.class,
				((Function) patternTerm.getUpsilon()).getChild(0));

		assertEquals(List.of(1, 0), upsilonImage.getExponents());
		assertTrue(closingBase.deepEquals(upsilonImage.getArgument()));
	}

	@Test
	@DisplayName("rebuild valid subterms and reject invalid positions")
	void rebuildValidSubtermsAndRejectInvalidPositions() {
		Variable variable = new Variable();
		Function baseTerm = new Function(
				uniqueSymbol("simple-pattern-subterm-base", 1),
				List.of(variable));
		HatFunction image = hatFunction(
				"simple-pattern-subterm-image", List.of(1, 0));
		Substitution hatFunctionSubstitution = new Substitution();
		hatFunctionSubstitution.add(variable, image);
		SimplePatternTerm patternTerm = SimplePatternTerm.tryBuild(
				baseTerm,
				SimplePatternSubstitution.tryBuild(hatFunctionSubstitution));

		SimplePatternTerm root = patternTerm.get(new Position());
		SimplePatternTerm child = patternTerm.get(new Position(0));

		assertNotSame(patternTerm, root);
		assertTrue(patternTerm.getUpsilon().deepEquals(root.getUpsilon()));
		assertSame(variable, child.getBaseTerm());
		assertNotSame(image, child.getPatternSubstitution()
				.getHatFunctionSubstitution().get(variable));
		assertTrue(image.deepEquals(child.getPatternSubstitution()
				.getHatFunctionSubstitution().get(variable)));
		assertTrue(image.deepEquals(child.getUpsilon()));
		assertNull(patternTerm.get(new Position(1)));
	}

	@Test
	@DisplayName("deep copy shares canonical copies between base and upsilon")
	void deepCopySharesCanonicalCopiesBetweenBaseAndUpsilon() {
		Variable variable = new Variable();
		Variable predefinedVariableCopy = new Variable();
		Function baseTerm = new Function(
				uniqueSymbol("simple-pattern-deep-copy", 2),
				List.of(variable, variable));
		SimplePatternTerm source = SimplePatternTerm.of(baseTerm);
		Map<Term, Term> copies = new HashMap<>();
		copies.put(variable, predefinedVariableCopy);

		SimplePatternTerm copy = source.deepCopy(copies);
		Function copiedBase =
				assertInstanceOf(Function.class, copy.getBaseTerm());

		assertNotSame(source, copy);
		assertNotSame(baseTerm, copiedBase);
		assertNotSame(copiedBase, copy.getUpsilon());
		assertTrue(copiedBase.deepEquals(copy.getUpsilon()));
		assertSame(predefinedVariableCopy, copiedBase.getChild(0));
		assertSame(predefinedVariableCopy, copiedBase.getChild(1));
		assertNotSame(source.getPatternSubstitution(),
				copy.getPatternSubstitution());
	}

	@Test
	@DisplayName("return negative weakening indexes when no candidate exists")
	void returnNegativeWeakeningIndexesWhenNoCandidateExists() {
		SimplePatternTerm first = SimplePatternTerm.of(
				constant("simple-pattern-no-weakening"));
		SimplePatternTerm second = SimplePatternTerm.of(first.getBaseTerm());

		SimplePatternTerm.WeakeningIndexes indexes =
				first.computeWeakeningIndexes(second);

		assertEquals(-1, indexes.functionWeakeningIndex());
		assertEquals(-1, indexes.hatWeakeningIndex());
	}

	@Test
	@DisplayName("merge compatible function weakening candidates")
	void mergeCompatibleFunctionWeakeningCandidates() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-function-weakening-base", 2);
		FunctionSymbol contextSymbol =
				uniqueSymbol("simple-pattern-function-weakening-context", 1);
		Function firstArgument =
				constant("simple-pattern-function-first-argument");
		Function secondArgument =
				constant("simple-pattern-function-second-argument");
		HatFunctionSymbol hatSymbol = hatSymbol(contextSymbol);
		SimplePatternTerm patternTerm = patternTerm(
				baseSymbol,
				List.of(firstVariable, secondVariable),
				List.of(
						new HatFunction(hatSymbol, firstArgument, 2, 1),
						new HatFunction(hatSymbol, secondArgument, 2, 1)));
		SimplePatternTerm otherPatternTerm = patternTerm(
				baseSymbol,
				List.of(firstVariable, secondVariable),
				List.of(
						tower(contextSymbol, 5, firstArgument),
						tower(contextSymbol, 5, secondArgument)));
		Term sourceUpsilon = patternTerm.getUpsilon();
		Term otherSourceUpsilon = otherPatternTerm.getUpsilon();

		SimplePatternTerm.WeakeningIndexes indexes =
				patternTerm.computeWeakeningIndexes(otherPatternTerm);

		assertEquals(2, indexes.functionWeakeningIndex());
		assertEquals(-1, indexes.hatWeakeningIndex());
		assertSame(sourceUpsilon, patternTerm.getUpsilon());
		assertSame(otherSourceUpsilon, otherPatternTerm.getUpsilon());
	}

	@Test
	@DisplayName("reject conflicting or indivisible function weakening candidates")
	void rejectConflictingOrIndivisibleFunctionWeakeningCandidates() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-conflicting-weakening-base", 2);
		FunctionSymbol contextSymbol =
				uniqueSymbol("simple-pattern-conflicting-weakening-context", 1);
		Function firstArgument =
				constant("simple-pattern-conflicting-first-argument");
		Function secondArgument =
				constant("simple-pattern-conflicting-second-argument");
		HatFunctionSymbol hatSymbol = hatSymbol(contextSymbol);
		SimplePatternTerm patternTerm = patternTerm(
				baseSymbol,
				List.of(firstVariable, secondVariable),
				List.of(
						new HatFunction(hatSymbol, firstArgument, 2, 1),
						new HatFunction(hatSymbol, secondArgument, 2, 1)));
		SimplePatternTerm conflicting = patternTerm(
				baseSymbol,
				List.of(firstVariable, secondVariable),
				List.of(
						tower(contextSymbol, 5, firstArgument),
						tower(contextSymbol, 3, secondArgument)));
		SimplePatternTerm indivisible = patternTerm(
				baseSymbol,
				List.of(firstVariable, secondVariable),
				List.of(
						tower(contextSymbol, 4, firstArgument),
						tower(contextSymbol, 5, secondArgument)));

		assertNull(patternTerm.computeWeakeningIndexes(conflicting));
		assertNull(patternTerm.computeWeakeningIndexes(indivisible));
	}

	@Test
	@DisplayName("accumulate the maximum rounded hat weakening candidate")
	void accumulateTheMaximumRoundedHatWeakeningCandidate() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-hat-weakening-base", 2);
		FunctionSymbol contextSymbol =
				uniqueSymbol("simple-pattern-hat-weakening-context", 1);
		Function firstArgument =
				constant("simple-pattern-hat-first-argument");
		Function secondArgument =
				constant("simple-pattern-hat-second-argument");
		HatFunctionSymbol hatSymbol = hatSymbol(contextSymbol);
		SimplePatternTerm patternTerm = patternTerm(
				baseSymbol,
				List.of(firstVariable, secondVariable),
				List.of(
						new HatFunction(hatSymbol, firstArgument, 2, 1),
						new HatFunction(hatSymbol, secondArgument, 2, 1)));
		SimplePatternTerm otherPatternTerm = patternTerm(
				baseSymbol,
				List.of(firstVariable, secondVariable),
				List.of(
						new HatFunction(hatSymbol, firstArgument, 2, 4),
						new HatFunction(hatSymbol, secondArgument, 1, 6)));

		SimplePatternTerm.WeakeningIndexes indexes =
				patternTerm.computeWeakeningIndexes(otherPatternTerm);

		assertEquals(-1, indexes.functionWeakeningIndex());
		assertEquals(3, indexes.hatWeakeningIndex());
	}

	@Test
	@DisplayName("ignore hat disagreements with a different context")
	void ignoreHatDisagreementsWithADifferentContext() {
		Variable variable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-foreign-hat-base", 1);
		Function argument = constant("simple-pattern-foreign-hat-argument");
		HatFunction firstHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-first-hat-context", 1)),
				argument, 1, 0);
		HatFunction foreignHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-foreign-hat-context", 1)),
				argument, 1, 4);
		SimplePatternTerm first = patternTerm(
				baseSymbol, List.of(variable), List.of(firstHat));
		SimplePatternTerm second = patternTerm(
				baseSymbol, List.of(variable), List.of(foreignHat));

		SimplePatternTerm.WeakeningIndexes indexes =
				first.computeWeakeningIndexes(second);

		assertEquals(-1, indexes.functionWeakeningIndex());
		assertEquals(-1, indexes.hatWeakeningIndex());
	}

	@Test
	@DisplayName("build both weakening substitutions without modifying the source")
	void buildBothWeakeningSubstitutionsWithoutModifyingTheSource() {
		Variable hatVariable = new Variable();
		Variable plainVariable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-weakening-substitutions-base", 2);
		Function argument =
				constant("simple-pattern-weakening-substitutions-argument");
		Function plainImage =
				constant("simple-pattern-weakening-substitutions-plain");
		HatFunction sourceHat = new HatFunction(
				hatSymbol(uniqueSymbol(
						"simple-pattern-weakening-substitutions-context", 1)),
				argument, 2, 3);
		SimplePatternTerm patternTerm = patternTerm(
				baseSymbol,
				List.of(hatVariable, plainVariable),
				List.of(sourceHat, plainImage));
		HatFunction storedSourceHat = assertInstanceOf(HatFunction.class,
				patternTerm.getPatternSubstitution()
						.getHatFunctionSubstitution().get(hatVariable));

		SimplePatternTerm.WeakeningSubstitutions substitutions =
				patternTerm.buildWeakeningSubstitutions(2);
		HatFunction firstHat = assertInstanceOf(HatFunction.class,
				substitutions.first().get(hatVariable));
		HatFunction secondHat = assertInstanceOf(HatFunction.class,
				substitutions.second().get(hatVariable));

		assertEquals(List.of(2, 7), firstHat.getExponents());
		assertEquals(List.of(2, 2, 7), secondHat.getExponents());
		assertNotSame(storedSourceHat, firstHat);
		assertNotSame(storedSourceHat, secondHat);
		assertSame(storedSourceHat.getRootSymbol(), firstHat.getRootSymbol());
		assertSame(storedSourceHat.getRootSymbol(), secondHat.getRootSymbol());
		assertSame(storedSourceHat.getArgument(), firstHat.getArgument());
		assertSame(storedSourceHat.getArgument(), secondHat.getArgument());
		assertSame(plainImage, substitutions.first().get(plainVariable));
		assertSame(plainImage, substitutions.second().get(plainVariable));
		assertEquals(List.of(2, 3), storedSourceHat.getExponents());
	}

	@Test
	@DisplayName("preserve the offset at zero weakening index")
	void preserveTheOffsetAtZeroWeakeningIndex() {
		Variable variable = new Variable();
		HatFunction sourceHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-zero-weakening-context", 1)),
				constant("simple-pattern-zero-weakening-argument"), 2, 3);
		SimplePatternTerm patternTerm = patternTerm(
				uniqueSymbol("simple-pattern-zero-weakening-base", 1),
				List.of(variable), List.of(sourceHat));

		SimplePatternTerm.WeakeningSubstitutions substitutions =
				patternTerm.buildWeakeningSubstitutions(0);

		assertEquals(List.of(2, 3),
				((HatFunction) substitutions.first().get(variable)).getExponents());
		assertEquals(List.of(2, 2, 3),
				((HatFunction) substitutions.second().get(variable)).getExponents());
	}

	@Test
	@DisplayName("collapse multiple pumping exponents into their sum")
	void collapseMultiplePumpingExponentsIntoTheirSum() {
		Variable variable = new Variable();
		HatFunction sourceHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-multi-weakening-context", 1)),
				constant("simple-pattern-multi-weakening-argument"),
				List.of(1, 2, 3));
		SimplePatternTerm patternTerm = patternTerm(
				uniqueSymbol("simple-pattern-multi-weakening-base", 1),
				List.of(variable), List.of(sourceHat));

		SimplePatternTerm.WeakeningSubstitutions substitutions =
				patternTerm.buildWeakeningSubstitutions(1);

		assertEquals(List.of(3, 6),
				((HatFunction) substitutions.first().get(variable)).getExponents());
		assertEquals(List.of(3, 3, 6),
				((HatFunction) substitutions.second().get(variable)).getExponents());
	}

	@Test
	@DisplayName("reject arithmetic overflow in weakened hat exponents")
	void rejectArithmeticOverflowInWeakenedHatExponents() {
		Variable additionVariable = new Variable();
		HatFunction additionOverflowHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-addition-overflow-context", 1)),
				constant("simple-pattern-addition-overflow-argument"),
				1, 1);
		SimplePatternTerm additionOverflowPattern = patternTerm(
				uniqueSymbol("simple-pattern-addition-overflow-base", 1),
				List.of(additionVariable), List.of(additionOverflowHat));
		Variable multiplicationVariable = new Variable();
		HatFunction multiplicationOverflowHat = new HatFunction(
				hatSymbol(uniqueSymbol(
						"simple-pattern-multiplication-overflow-context", 1)),
				constant("simple-pattern-multiplication-overflow-argument"),
				2, 0);
		SimplePatternTerm multiplicationOverflowPattern = patternTerm(
				uniqueSymbol("simple-pattern-multiplication-overflow-base", 1),
				List.of(multiplicationVariable),
				List.of(multiplicationOverflowHat));

		assertThrows(
				ArithmeticException.class,
				() -> additionOverflowPattern.buildWeakeningSubstitutions(
						Integer.MAX_VALUE));
		assertThrows(
				ArithmeticException.class,
				() -> multiplicationOverflowPattern.buildWeakeningSubstitutions(
						Integer.MAX_VALUE));
		assertEquals(
				List.of(1, 1),
				((HatFunction) additionOverflowPattern.getPatternSubstitution()
						.getHatFunctionSubstitution().get(additionVariable))
						.getExponents());
		assertEquals(
				List.of(2, 0),
				((HatFunction) multiplicationOverflowPattern.getPatternSubstitution()
						.getHatFunctionSubstitution().get(multiplicationVariable))
						.getExponents());
	}

	@Test
	@DisplayName("accept a negative index only while the shifted offset stays natural")
	void acceptANegativeIndexOnlyWhileTheShiftedOffsetStaysNatural() {
		Variable acceptedVariable = new Variable();
		HatFunction acceptedHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-negative-accepted-context", 1)),
				constant("simple-pattern-negative-accepted-argument"), 2, 5);
		SimplePatternTerm acceptedPatternTerm = patternTerm(
				uniqueSymbol("simple-pattern-negative-accepted-base", 1),
				List.of(acceptedVariable), List.of(acceptedHat));
		Variable rejectedVariable = new Variable();
		HatFunction rejectedHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-negative-rejected-context", 1)),
				constant("simple-pattern-negative-rejected-argument"), 2, 1);
		SimplePatternTerm rejectedPatternTerm = patternTerm(
				uniqueSymbol("simple-pattern-negative-rejected-base", 1),
				List.of(rejectedVariable), List.of(rejectedHat));

		SimplePatternTerm.WeakeningSubstitutions accepted =
				acceptedPatternTerm.buildWeakeningSubstitutions(-1);

		assertEquals(List.of(2, 3),
				((HatFunction) accepted.first().get(acceptedVariable)).getExponents());
		assertEquals(List.of(2, 2, 3),
				((HatFunction) accepted.second().get(acceptedVariable)).getExponents());
		assertThrows(IllegalArgumentException.class,
				() -> rejectedPatternTerm.buildWeakeningSubstitutions(-1));
		assertEquals(List.of(2, 1), ((HatFunction) rejectedPatternTerm
				.getPatternSubstitution().getHatFunctionSubstitution()
				.get(rejectedVariable)).getExponents());
	}

	@Test
	@DisplayName("build independent empty weakening substitutions")
	void buildIndependentEmptyWeakeningSubstitutions() {
		SimplePatternTerm.WeakeningSubstitutions substitutions =
				SimplePatternTerm.of(new Variable())
						.buildWeakeningSubstitutions(3);

		assertTrue(substitutions.first().isEmpty());
		assertTrue(substitutions.second().isEmpty());
		assertNotSame(substitutions.first(), substitutions.second());
	}

	@Test
	@DisplayName("classify the pattern term from its upsilon value")
	void classifyThePatternTermFromItsUpsilonValue() {
		Variable variable = new Variable();
		SimplePatternTerm variablePatternTerm = SimplePatternTerm.of(variable);
		SimplePatternTerm functionPatternTerm = SimplePatternTerm.of(
				new Function(uniqueSymbol("simple-pattern-variable-classification", 1),
						List.of(variable)));

		assertTrue(variablePatternTerm.isVariable());
		assertFalse(functionPatternTerm.isVariable());
	}

	@Test
	@DisplayName("iterate over base positions rather than deeper upsilon positions")
	void iterateOverBasePositionsRatherThanDeeperUpsilonPositions() {
		Variable variable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-position-boundary-base", 1);
		Function deepArgument = new Function(
				uniqueSymbol("simple-pattern-position-boundary-argument", 1),
				List.of(constant("simple-pattern-position-boundary-leaf")));
		HatFunction image = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-position-boundary-context", 1)),
				deepArgument, 1, 0);
		SimplePatternTerm patternTerm = patternTerm(
				baseSymbol, List.of(variable), List.of(image));
		Iterator<Position> positions = patternTerm.iterator();

		assertEquals(List.of(List.of(), List.of(0)), positionElements(positions));
		assertTrue(patternTerm.getUpsilon().iterator().hasNext());
	}

	@Test
	@DisplayName("render upsilon and extend the provided variable name map")
	void renderUpsilonAndExtendTheProvidedVariableNameMap() {
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		FunctionSymbol baseSymbol =
				uniqueSymbol("simple-pattern-rendering-base", 2);
		Function baseTerm = new Function(
				baseSymbol, List.of(firstVariable, secondVariable));
		Map<Variable, String> variableNames = new HashMap<>();
		variableNames.put(firstVariable, "X");
		SimplePatternTerm starredPatternTerm = SimplePatternTerm.of(baseTerm);
		Function constantImage = constant("simple-pattern-rendering-image");
		SimplePatternTerm appliedPatternTerm = patternTerm(
				uniqueSymbol("simple-pattern-rendering-applied-base", 1),
				List.of(firstVariable), List.of(constantImage));

		assertEquals(baseSymbol + "(X,_1)",
				starredPatternTerm.toString(variableNames));
		assertEquals("_1", variableNames.get(secondVariable));
		assertEquals(appliedPatternTerm.getUpsilon().toString(),
				appliedPatternTerm.toString(new HashMap<>()));
		assertFalse(appliedPatternTerm.getBaseTerm().deepEquals(
				appliedPatternTerm.getUpsilon()));
	}

	@Test
	@DisplayName("return an empty simple unifier for equal upsilon terms")
	void returnAnEmptySimpleUnifierForEqualUpsilonTerms() {
		Function term = new Function(
				uniqueSymbol("simple-pattern-empty-unifier", 1),
				List.of(new Variable()));
		SimplePatternTerm first = SimplePatternTerm.of(term);
		SimplePatternTerm second = SimplePatternTerm.of(term);

		SimplePatternSubstitution unifier = first.unifyWith(second);

		assertTrue(unifier.getHatFunctionSubstitution().isEmpty());
		assertTrue(unifier.getPumping().isEmpty());
		assertTrue(unifier.getClosing().isEmpty());
	}

	@Test
	@DisplayName("preserve variable-to-function unification direction")
	void preserveVariableToFunctionUnificationDirection() {
		Variable sourceVariable = new Variable();
		Variable targetVariable = new Variable();
		Function target = new Function(
				uniqueSymbol("simple-pattern-directed-unifier", 1),
				List.of(targetVariable));
		SimplePatternTerm sourcePatternTerm =
				SimplePatternTerm.of(sourceVariable);
		SimplePatternTerm targetPatternTerm = SimplePatternTerm.of(target);

		SimplePatternSubstitution unifier =
				sourcePatternTerm.unifyWith(targetPatternTerm);

		Function mappedTarget = assertInstanceOf(Function.class,
				unifier.getHatFunctionSubstitution().get(sourceVariable));
		assertNotSame(target, mappedTarget);
		assertTrue(target.deepEquals(mappedTarget));
		assertSame(targetVariable, mappedTarget.getChild(0));
		assertNull(unifier.getHatFunctionSubstitution().get(targetVariable));
		assertSame(sourceVariable, sourcePatternTerm.getUpsilon());
		assertSame(target, targetPatternTerm.getUpsilon());
		assertSame(targetVariable, target.getChild(0));
	}

	@Test
	@DisplayName("unify a hat function with a compatible context tower")
	void unifyAHatFunctionWithACompatibleContextTower() {
		FunctionSymbol contextSymbol =
				uniqueSymbol("simple-pattern-hat-unifier-context", 1);
		HatFunctionSymbol hatSymbol = hatSymbol(contextSymbol);
		Variable hatArgument = new Variable();
		Variable towerArgument = new Variable();
		HatFunction hat = new HatFunction(hatSymbol, hatArgument, 2, 3);
		Function tower = new Function(contextSymbol, List.of(towerArgument));

		SimplePatternSubstitution unifier = SimplePatternTerm.of(hat)
				.unifyWith(SimplePatternTerm.of(tower));
		HatFunction mappedHat = assertInstanceOf(HatFunction.class,
				unifier.getHatFunctionSubstitution().get(towerArgument));

		assertSame(hatSymbol, mappedHat.getRootSymbol());
		assertSame(hatArgument, mappedHat.getArgument());
		assertEquals(List.of(2, 2), mappedHat.getExponents());
		assertSame(hatArgument, hat.getArgument());
		assertSame(towerArgument, tower.getChild(0));
	}

	@Test
	@DisplayName("reject occurs-check root and hat-context conflicts")
	void rejectOccursCheckRootAndHatContextConflicts() {
		Variable recursiveVariable = new Variable();
		Function recursiveFunction = new Function(
				uniqueSymbol("simple-pattern-occurs-conflict", 1),
				List.of(recursiveVariable));
		assertNull(SimplePatternTerm.of(recursiveVariable)
				.unifyWith(SimplePatternTerm.of(recursiveFunction)));

		assertNull(SimplePatternTerm.of(
				constant("simple-pattern-first-root-conflict")).unifyWith(
						SimplePatternTerm.of(
								constant("simple-pattern-second-root-conflict"))));

		Function argument = constant("simple-pattern-context-conflict-argument");
		HatFunction firstHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-first-context-conflict", 1)),
				argument, 1, 0);
		HatFunction secondHat = new HatFunction(
				hatSymbol(uniqueSymbol("simple-pattern-second-context-conflict", 1)),
				argument, 1, 0);
		assertNull(SimplePatternTerm.of(firstHat)
				.unifyWith(SimplePatternTerm.of(secondHat)));
		assertSame(argument, firstHat.getArgument());
		assertSame(argument, secondHat.getArgument());
	}

	@Test
	@DisplayName("reject a raw unifier whose image is not a simple pattern")
	void rejectARawUnifierWhoseImageIsNotASimplePattern() {
		Variable variable = new Variable();
		HatFunction innerHat = hatFunction(
				"simple-pattern-non-simple-raw-unifier", List.of(1, 0));
		Function containingFunction = new Function(
				uniqueSymbol("simple-pattern-non-simple-raw-container", 1),
				List.of(innerHat));

		assertNull(SimplePatternTerm.of(variable)
				.unifyWith(SimplePatternTerm.of(containingFunction)));
		assertSame(innerHat, containingFunction.getChild(0));
	}

	@Test
	@DisplayName("keep only direct unification for a non-fact rule")
	void keepOnlyDirectUnificationForANonFactRule() {
		Variable queryVariable = new Variable();
		FunctionSymbol predicateSymbol =
				uniqueSymbol("simple-pattern-rule-direct-predicate", 1);
		Function directImage = constant("simple-pattern-rule-direct-image");
		SimplePatternTerm query = SimplePatternTerm.of(
				new Function(predicateSymbol, List.of(queryVariable)));
		SimplePatternTerm left = SimplePatternTerm.of(
				new Function(predicateSymbol, List.of(directImage)));
		SimplePatternTerm right = SimplePatternTerm.of(
				new Function(uniqueSymbol("simple-pattern-rule-direct-right", 1),
						List.of(directImage)));
		PatternRuleLp rule = PatternRuleLp.tryBuild(left, right, 0);
		Term queryUpsilon = query.getUpsilon();
		Term leftUpsilon = left.getUpsilon();

		Collection<PatternSubstitution> unifiers = query.unifyWith(rule);

		assertEquals(1, unifiers.size());
		SimplePatternSubstitution unifier = assertInstanceOf(
				SimplePatternSubstitution.class, unifiers.iterator().next());
		Term mappedImage = unifier
				.getHatFunctionSubstitution().get(queryVariable);
		assertTrue(directImage.deepEquals(mappedImage));
		assertSame(queryUpsilon, query.getUpsilon());
		assertSame(left, rule.getLeft());
		assertSame(leftUpsilon, rule.getLeft().getUpsilon());
		assertSame(right, rule.getRight());
	}

	@Test
	@DisplayName("return an empty collection when direct and weakened unification fail")
	void returnAnEmptyCollectionWhenDirectAndWeakenedUnificationFail() {
		SimplePatternTerm query = SimplePatternTerm.of(
				constant("simple-pattern-rule-query-root"));
		SimplePatternTerm left = SimplePatternTerm.of(
				constant("simple-pattern-rule-left-root"));
		PatternRuleLp fact = PatternRuleLp.tryBuildFact(left, 0);

		Collection<PatternSubstitution> unifiers = query.unifyWith(fact);

		assertTrue(unifiers.isEmpty());
		assertSame(left, fact.getLeft());
		assertNull(fact.getRight());
	}

	@Test
	@DisplayName("retain a direct fact unifier when no weakening index exists")
	void retainADirectFactUnifierWhenNoWeakeningIndexExists() {
		Function leftTerm = constant("simple-pattern-direct-fact");
		SimplePatternTerm query = SimplePatternTerm.of(leftTerm);
		SimplePatternTerm left = SimplePatternTerm.of(leftTerm);
		PatternRuleLp fact = PatternRuleLp.tryBuildFact(left, 0);

		Collection<PatternSubstitution> unifiers = query.unifyWith(fact);

		assertEquals(1, unifiers.size());
		SimplePatternSubstitution unifier = assertInstanceOf(
				SimplePatternSubstitution.class, unifiers.iterator().next());
		assertTrue(unifier
				.getHatFunctionSubstitution().isEmpty());
	}

	@Test
	@DisplayName("add a successful finite weakening after direct failure")
	void addASuccessfulFiniteWeakeningAfterDirectFailure() {
		Variable leftVariable = new Variable();
		FunctionSymbol predicateSymbol =
				uniqueSymbol("simple-pattern-finite-weakening-predicate", 1);
		FunctionSymbol contextSymbol =
				uniqueSymbol("simple-pattern-finite-weakening-context", 1);
		Function base = constant("simple-pattern-finite-weakening-base");
		HatFunction leftImage = new HatFunction(
				hatSymbol(contextSymbol), base, 1, 0);
		SimplePatternTerm left = patternTerm(
				predicateSymbol, List.of(leftVariable), List.of(leftImage));
		SimplePatternTerm query = SimplePatternTerm.of(new Function(
				predicateSymbol, List.of(tower(contextSymbol, 1, base))));
		PatternRuleLp fact = PatternRuleLp.tryBuildFact(left, 0);
		Term leftUpsilon = left.getUpsilon();
		Term queryUpsilon = query.getUpsilon();

		Collection<PatternSubstitution> unifiers = query.unifyWith(fact);

		assertEquals(1, unifiers.size());
		SimplePatternSubstitution unifier = assertInstanceOf(
				SimplePatternSubstitution.class, unifiers.iterator().next());
		assertTrue(unifier
				.getHatFunctionSubstitution().isEmpty());
		assertSame(leftUpsilon, left.getUpsilon());
		assertSame(queryUpsilon, query.getUpsilon());
	}

	@Test
	@DisplayName("discard a direct raw unifier that is not simple")
	void discardADirectRawUnifierThatIsNotSimple() {
		Variable queryVariable = new Variable();
		FunctionSymbol predicateSymbol =
				uniqueSymbol("simple-pattern-rule-non-simple-predicate", 1);
		HatFunction nestedHat = hatFunction(
				"simple-pattern-rule-non-simple-hat", List.of(1, 0));
		Function nestedImage = new Function(
				uniqueSymbol("simple-pattern-rule-non-simple-container", 1),
				List.of(nestedHat));
		SimplePatternTerm query = SimplePatternTerm.of(
				new Function(predicateSymbol, List.of(queryVariable)));
		SimplePatternTerm left = SimplePatternTerm.of(
				new Function(predicateSymbol, List.of(nestedImage)));
		PatternRuleLp fact = PatternRuleLp.tryBuildFact(left, 0);

		Collection<PatternSubstitution> unifiers = query.unifyWith(fact);

		assertTrue(unifiers.isEmpty());
		assertSame(nestedHat, nestedImage.getChild(0));
	}

	private static List<List<Integer>> positionElements(
			Iterator<Position> positions) {
		List<List<Integer>> result = new ArrayList<>();
		while (positions.hasNext()) {
			List<Integer> elements = new ArrayList<>();
			positions.next().forEach(elements::add);
			result.add(elements);
		}
		return result;
	}

	private static SimplePatternTerm patternTerm(
			FunctionSymbol baseSymbol,
			List<Variable> variables,
			List<? extends Term> images) {
		Substitution hatFunctionSubstitution = new Substitution();
		for (int index = 0; index < variables.size(); index++)
			hatFunctionSubstitution.add(variables.get(index), images.get(index));

		return SimplePatternTerm.tryBuild(
				new Function(baseSymbol, variables),
				SimplePatternSubstitution.tryBuild(hatFunctionSubstitution));
	}

	private static HatFunctionSymbol hatSymbol(FunctionSymbol contextSymbol) {
		Variable contextVariable = new Variable();
		return HatFunctionSymbol.intern(
				new Function(contextSymbol, List.of(contextVariable)),
				contextVariable);
	}

	private static Term tower(
			FunctionSymbol contextSymbol, int height, Term argument) {
		Term tower = argument;
		for (int index = 0; index < height; index++)
			tower = new Function(contextSymbol, List.of(tower));
		return tower;
	}

	private static HatFunction hatFunction(
			String prefix, List<Integer> exponents) {
		Variable contextVariable = new Variable();
		Function context = new Function(
				uniqueSymbol(prefix + "-context", 1),
				List.of(contextVariable));
		return new HatFunction(
				HatFunctionSymbol.intern(context, contextVariable),
				constant(prefix + "-base"), exponents);
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
