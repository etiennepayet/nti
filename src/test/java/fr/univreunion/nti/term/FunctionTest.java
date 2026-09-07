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

package fr.univreunion.nti.term;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertEquals;
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

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.SoP;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;

class FunctionTest {

	@Test
	@DisplayName("detect nested hat subterms and terminate on cyclic functions")
	void detectNestedHatSubtermsAndTerminateOnCyclicFunctions() {
		String suffix = UUID.randomUUID().toString();
		Variable hole = new Variable();
		Function context = new Function(
				FunctionSymbol.intern("hat-context-" + suffix, 1), List.of(hole));
		HatFunction hat = new HatFunction(
				HatFunctionSymbol.intern(context, hole), new Variable(), List.of(1, 0));
		Function containing = new Function(
				FunctionSymbol.intern("hat-holder-" + suffix, 1), List.of(hat));
		Variable cycle = new Variable();
		Function cyclic = new Function(
				FunctionSymbol.intern("hat-cycle-" + suffix, 1), List.of(cycle));
		cycle.union(cyclic);

		assertTrue(containing.containsHatSubterm());
		assertFalse(cyclic.containsHatSubterm());
	}

	@Test
	@DisplayName("complete one shared renaming in both variant directions")
	void completeSharedVariantRenaming() {
		String suffix = UUID.randomUUID().toString();
		Variable firstSourceVariable = new Variable();
		Variable secondSourceVariable = new Variable();
		Variable firstTargetVariable = new Variable();
		Variable secondTargetVariable = new Variable();
		FunctionSymbol symbol =
				FunctionSymbol.intern("variant-shared-" + suffix, 2);
		Function source = new Function(
				symbol, List.of(firstSourceVariable, secondSourceVariable));
		Function target = new Function(
				symbol, List.of(firstTargetVariable, secondTargetVariable));
		Substitution renaming = new Substitution();

		assertTrue(source.isVariantOf(target, renaming));
		assertSame(firstTargetVariable, renaming.get(firstSourceVariable));
		assertSame(secondTargetVariable, renaming.get(secondSourceVariable));
		assertSame(firstSourceVariable, renaming.get(firstTargetVariable));
		assertSame(secondSourceVariable, renaming.get(secondTargetVariable));
		assertTrue(source.isVariantOf(target));
		assertTrue(target.isVariantOf(source));
	}

	@Test
	@DisplayName("retain partial renaming when the first variant direction fails")
	void retainPartialRenamingAfterFirstDirectionFailure() {
		String suffix = UUID.randomUUID().toString();
		Variable repeatedSourceVariable = new Variable();
		Variable firstTargetVariable = new Variable();
		Variable secondTargetVariable = new Variable();
		FunctionSymbol symbol =
				FunctionSymbol.intern("variant-first-failure-" + suffix, 2);
		Function source = new Function(
				symbol,
				List.of(repeatedSourceVariable, repeatedSourceVariable));
		Function target = new Function(
				symbol, List.of(firstTargetVariable, secondTargetVariable));
		Substitution renaming = new Substitution();

		assertFalse(source.isVariantOf(target, renaming));
		assertSame(firstTargetVariable, renaming.get(repeatedSourceVariable));
		assertNull(renaming.get(firstTargetVariable));
		assertNull(renaming.get(secondTargetVariable));
	}

	@Test
	@DisplayName("retain both-direction updates when reverse variant matching fails")
	void retainRenamingAfterReverseDirectionFailure() {
		String suffix = UUID.randomUUID().toString();
		Variable firstSourceVariable = new Variable();
		Variable secondSourceVariable = new Variable();
		Variable repeatedTargetVariable = new Variable();
		FunctionSymbol symbol =
				FunctionSymbol.intern("variant-reverse-failure-" + suffix, 2);
		Function source = new Function(
				symbol, List.of(firstSourceVariable, secondSourceVariable));
		Function target = new Function(
				symbol,
				List.of(repeatedTargetVariable, repeatedTargetVariable));
		Substitution renaming = new Substitution();

		assertFalse(source.isVariantOf(target, renaming));
		assertSame(repeatedTargetVariable, renaming.get(firstSourceVariable));
		assertSame(repeatedTargetVariable, renaming.get(secondSourceVariable));
		assertSame(firstSourceVariable, renaming.get(repeatedTargetVariable));
	}

	@Test
	@DisplayName("tau-match ordinary arguments and ignore mapped target arguments")
	void tauMatchFilteredAndOrdinaryArguments() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol predicateSymbol =
				FunctionSymbol.intern("tau-predicate-" + suffix, 3);
		Function requiredConstant = new Function(
				FunctionSymbol.intern("tau-required-" + suffix, 0),
				List.of());
		SoP tau = tauWithFirstTwoArgumentsUnmapped(
				predicateSymbol, requiredConstant);
		Variable firstPatternVariable = new Variable();
		Variable secondPatternVariable = new Variable();
		Function source = new Function(
				predicateSymbol,
				List.of(
						firstPatternVariable,
						secondPatternVariable,
						requiredConstant));
		Function firstTarget = new Function(
				FunctionSymbol.intern("tau-first-target-" + suffix, 0),
				List.of());
		Function secondTarget = new Function(
				FunctionSymbol.intern("tau-second-target-" + suffix, 0),
				List.of());
		Function ignoredTarget = new Function(
				FunctionSymbol.intern("tau-ignored-target-" + suffix, 0),
				List.of());
		Function target = new Function(
				predicateSymbol,
				List.of(firstTarget, secondTarget, ignoredTarget));
		Substitution matcher = new Substitution();

		assertTrue(Function.tauMoreGeneral(source, target, tau, matcher));
		assertSame(firstTarget, matcher.get(firstPatternVariable));
		assertSame(secondTarget, matcher.get(secondPatternVariable));
		assertSame(ignoredTarget, target.getChild(2));
	}

	@Test
	@DisplayName("retain ordinary tau bindings when a later mapped check fails")
	void retainPartialTauMatcherOnMappedFailure() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol predicateSymbol =
				FunctionSymbol.intern("tau-failure-predicate-" + suffix, 3);
		Function requiredConstant = new Function(
				FunctionSymbol.intern("tau-failure-required-" + suffix, 0),
				List.of());
		SoP tau = tauWithFirstTwoArgumentsUnmapped(
				predicateSymbol, requiredConstant);
		Variable firstPatternVariable = new Variable();
		Variable secondPatternVariable = new Variable();
		Function incompatibleSourceArgument = new Function(
				FunctionSymbol.intern("tau-incompatible-source-" + suffix, 0),
				List.of());
		Function source = new Function(
				predicateSymbol,
				List.of(
						firstPatternVariable,
						secondPatternVariable,
						incompatibleSourceArgument));
		Function firstTarget = new Function(
				FunctionSymbol.intern("tau-failure-first-" + suffix, 0),
				List.of());
		Function secondTarget = new Function(
				FunctionSymbol.intern("tau-failure-second-" + suffix, 0),
				List.of());
		Function target = new Function(
				predicateSymbol,
				List.of(firstTarget, secondTarget, requiredConstant));
		Substitution matcher = new Substitution();

		assertFalse(Function.tauMoreGeneral(source, target, tau, matcher));
		assertSame(firstTarget, matcher.get(firstPatternVariable));
		assertSame(secondTarget, matcher.get(secondPatternVariable));

		Variable untouchedVariable = new Variable();
		Function differentRootSource = new Function(
				FunctionSymbol.intern("tau-other-root-" + suffix, 1),
				List.of(untouchedVariable));
		assertFalse(Function.tauMoreGeneral(
				differentRootSource, target, tau, matcher));
		assertNull(matcher.get(untouchedVariable));
	}

	private static SoP tauWithFirstTwoArgumentsUnmapped(
			FunctionSymbol predicateSymbol,
			Term requiredThirdArgument) {

		Variable repeatedVariable = new Variable();
		Function atom = new Function(
				predicateSymbol,
				List.of(
						repeatedVariable,
						repeatedVariable,
						requiredThirdArgument));
		return new SoP(List.of(new BinaryRuleLp(atom, atom, 0)));
	}

	@Test
	@DisplayName("complete a matcher in left-to-right argument order")
	void completeMatcherInArgumentOrder() {
		String suffix = UUID.randomUUID().toString();
		Variable firstPatternVariable = new Variable();
		Variable secondPatternVariable = new Variable();
		FunctionSymbol nestedSymbol =
				FunctionSymbol.intern("matcher-nested-" + suffix, 1);
		FunctionSymbol outerSymbol =
				FunctionSymbol.intern("matcher-outer-" + suffix, 3);
		Function pattern = new Function(
				outerSymbol,
				List.of(
						firstPatternVariable,
						new Function(nestedSymbol, List.of(secondPatternVariable)),
						firstPatternVariable));
		Function firstTarget = new Function(
				FunctionSymbol.intern("matcher-first-target-" + suffix, 0),
				List.of());
		Function secondTarget = new Function(
				FunctionSymbol.intern("matcher-second-target-" + suffix, 0),
				List.of());
		Function target = new Function(
				outerSymbol,
				List.of(
						firstTarget,
						new Function(nestedSymbol, List.of(secondTarget)),
						firstTarget));
		Substitution matcher = new Substitution();

		assertTrue(pattern.isMoreGeneralThan(target, matcher));
		assertSame(firstTarget, matcher.get(firstPatternVariable));
		assertSame(secondTarget, matcher.get(secondPatternVariable));
		assertTrue(pattern.isMoreGeneralThan(target));
		assertFalse(target.isMoreGeneralThan(pattern));
	}

	@Test
	@DisplayName("retain earlier matcher bindings when a later argument fails")
	void retainPartialMatcherOnFailure() {
		String suffix = UUID.randomUUID().toString();
		Variable repeatedVariable = new Variable();
		Variable middleVariable = new Variable();
		FunctionSymbol outerSymbol =
				FunctionSymbol.intern("partial-matcher-" + suffix, 3);
		Function pattern = new Function(
				outerSymbol,
				List.of(repeatedVariable, middleVariable, repeatedVariable));
		Function firstTarget = new Function(
				FunctionSymbol.intern("partial-first-" + suffix, 0),
				List.of());
		Function middleTarget = new Function(
				FunctionSymbol.intern("partial-middle-" + suffix, 0),
				List.of());
		Function conflictingTarget = new Function(
				FunctionSymbol.intern("partial-conflict-" + suffix, 0),
				List.of());
		Function target = new Function(
				outerSymbol,
				List.of(firstTarget, middleTarget, conflictingTarget));
		Substitution matcher = new Substitution();

		assertFalse(pattern.isMoreGeneralThan(target, matcher));
		assertSame(firstTarget, matcher.get(repeatedVariable));
		assertSame(middleTarget, matcher.get(middleVariable));
	}

	@Test
	@DisplayName("fail before mutation for incompatible roots or matcher bindings")
	void failMatchingWithIncompatibleRootsOrBindings() {
		String suffix = UUID.randomUUID().toString();
		Variable patternVariable = new Variable();
		FunctionSymbol patternSymbol =
				FunctionSymbol.intern("matcher-pattern-root-" + suffix, 1);
		Function pattern = new Function(patternSymbol, List.of(patternVariable));
		Function existingTarget = new Function(
				FunctionSymbol.intern("matcher-existing-" + suffix, 0),
				List.of());
		Function conflictingTarget = new Function(
				FunctionSymbol.intern("matcher-conflicting-" + suffix, 0),
				List.of());
		Substitution matcher = new Substitution();
		matcher.add(patternVariable, existingTarget);

		assertFalse(pattern.isMoreGeneralThan(
				new Function(patternSymbol, List.of(conflictingTarget)), matcher));
		assertSame(existingTarget, matcher.get(patternVariable));

		Variable untouchedVariable = new Variable();
		Function differentRootPattern =
				new Function(patternSymbol, List.of(untouchedVariable));
		assertFalse(differentRootPattern.isMoreGeneralThan(
				new Function(
						FunctionSymbol.intern("matcher-other-root-" + suffix, 1),
						List.of(conflictingTarget)),
				matcher));
		assertNull(matcher.get(untouchedVariable));
	}

	@Test
	@DisplayName("collect disagreement positions in prefix argument order")
	void collectDisagreementPositionsInOrder() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol outerSymbol =
				FunctionSymbol.intern("dpos-outer-" + suffix, 3);
		FunctionSymbol nestedSymbol =
				FunctionSymbol.intern("dpos-nested-" + suffix, 1);
		FunctionSymbol firstConstantSymbol =
				FunctionSymbol.intern("dpos-first-constant-" + suffix, 0);
		FunctionSymbol secondConstantSymbol =
				FunctionSymbol.intern("dpos-second-constant-" + suffix, 0);
		Function first = new Function(
				outerSymbol,
				List.of(
						new Function(nestedSymbol, List.of(
								new Function(firstConstantSymbol, List.of()))),
						new Variable(),
						new Function(firstConstantSymbol, List.of())));
		Function second = new Function(
				outerSymbol,
				List.of(
						new Function(nestedSymbol, List.of(
								new Function(secondConstantSymbol, List.of()))),
						new Variable(),
						new Variable()));

		assertEquals(
				List.of("[0, 0]", "[2]"),
				positionLabels(first.dpos(second, false).iterator()));
		assertEquals(
				List.of("[0, 0]", "[1]", "[2]"),
				positionLabels(first.dpos(second, true).iterator()));
	}

	@Test
	@DisplayName("stop disagreement collection at a different root")
	void stopDisagreementCollectionAtDifferentRoot() {
		String suffix = UUID.randomUUID().toString();
		Function first = new Function(
				FunctionSymbol.intern("dpos-first-root-" + suffix, 1),
				List.of(new Variable()));
		Function second = new Function(
				FunctionSymbol.intern("dpos-second-root-" + suffix, 1),
				List.of(new Function(
						FunctionSymbol.intern("dpos-deeper-" + suffix, 0),
						List.of())));

		assertEquals(
				List.of("root"),
				positionLabels(first.dpos(second, true).iterator()));
		assertEquals(
				List.of("root"),
				positionLabels(second.dpos(first, false).iterator()));
	}

	@Test
	@DisplayName("resolve union-find schemas before collecting disagreements")
	void resolveSchemasBeforeCollectingDisagreements() {
		String suffix = UUID.randomUUID().toString();
		Variable unifiedVariable = new Variable();
		Function schema = new Function(
				FunctionSymbol.intern("dpos-schema-" + suffix, 1),
				List.of(new Variable()));
		unifiedVariable.union(schema);
		FunctionSymbol holderSymbol =
				FunctionSymbol.intern("dpos-holder-" + suffix, 1);
		Function withVariable =
				new Function(holderSymbol, List.of(unifiedVariable));
		Function withCompatibleSchema = new Function(
				holderSymbol,
				List.of(new Function(schema.getRootSymbol(), List.of(new Variable()))));

		assertTrue(withVariable.dpos(withCompatibleSchema, false).isEmpty());
		assertEquals(
				List.of("[0, 0]"),
				positionLabels(
						withVariable.dpos(withCompatibleSchema, true).iterator()));
	}

	@Test
	@DisplayName("treat variables as structural wildcards in both directions")
	void treatVariablesAsStructuralWildcards() {
		String suffix = UUID.randomUUID().toString();
		Variable variable = new Variable();
		Function function = new Function(
				FunctionSymbol.intern("structure-function-" + suffix, 1),
				List.of(new Function(
						FunctionSymbol.intern("structure-constant-" + suffix, 0),
						List.of())));

		assertTrue(function.hasSameStructureAs(variable));
		assertTrue(variable.hasSameStructureAs(function));
		assertTrue(function.hasSameStructureAs(function));
		assertThrows(NullPointerException.class,
				() -> function.hasSameStructureAs(null));
	}

	@Test
	@DisplayName("compare function roots and argument structures recursively")
	void compareFunctionStructuresRecursively() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol outerSymbol =
				FunctionSymbol.intern("structure-outer-" + suffix, 2);
		FunctionSymbol nestedSymbol =
				FunctionSymbol.intern("structure-nested-" + suffix, 1);
		Function first = new Function(
				outerSymbol,
				List.of(
						new Function(nestedSymbol, List.of(new Variable())),
						new Variable()));
		Function compatible = new Function(
				outerSymbol,
				List.of(
						new Function(nestedSymbol, List.of(new Function(
								FunctionSymbol.intern("structure-leaf-" + suffix, 0),
								List.of()))),
						new Function(
								FunctionSymbol.intern("structure-any-" + suffix, 0),
								List.of())));
		Function differentNestedRoot = new Function(
				outerSymbol,
				List.of(
						new Function(
								FunctionSymbol.intern("structure-other-nested-" + suffix, 1),
								List.of(new Variable())),
						new Variable()));

		assertTrue(first.hasSameStructureAs(compatible));
		assertTrue(compatible.hasSameStructureAs(first));
		assertFalse(first.hasSameStructureAs(differentNestedRoot));
		assertFalse(first.hasSameStructureAs(new Function(
				FunctionSymbol.intern("structure-other-outer-" + suffix, 2),
				List.of(new Variable(), new Variable()))));
	}

	@Test
	@DisplayName("compare the function schema of a unified variable")
	void compareUnifiedVariableSchema() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol schemaSymbol =
				FunctionSymbol.intern("structure-schema-" + suffix, 1);
		Variable unifiedVariable = new Variable();
		Function schema = new Function(schemaSymbol, List.of(new Variable()));
		unifiedVariable.union(schema);
		Function compatible = new Function(schemaSymbol, List.of(new Function(
				FunctionSymbol.intern("structure-schema-leaf-" + suffix, 0),
				List.of())));
		Function incompatible = new Function(
				FunctionSymbol.intern("structure-incompatible-" + suffix, 1),
				List.of(new Variable()));

		assertTrue(unifiedVariable.hasSameStructureAs(compatible));
		assertTrue(compatible.hasSameStructureAs(unifiedVariable));
		assertFalse(unifiedVariable.hasSameStructureAs(incompatible));
	}

	@Test
	@DisplayName("compare functions structurally with variable identity")
	void compareFunctionsStructurally() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol outerSymbol =
				FunctionSymbol.intern("equality-outer-" + suffix, 2);
		FunctionSymbol constantSymbol =
				FunctionSymbol.intern("equality-constant-" + suffix, 0);
		Variable sharedVariable = new Variable();
		Function first = new Function(
				outerSymbol,
				List.of(sharedVariable, new Function(constantSymbol, List.of())));
		Function equal = new Function(
				outerSymbol,
				List.of(sharedVariable, new Function(constantSymbol, List.of())));
		Function differentVariable = new Function(
				outerSymbol,
				List.of(new Variable(), new Function(constantSymbol, List.of())));
		Function reordered = new Function(
				outerSymbol,
				List.of(new Function(constantSymbol, List.of()), sharedVariable));

		assertTrue(first.deepEquals(first));
		assertTrue(first.deepEquals(equal));
		assertTrue(first.deepEquals(equal));
		assertFalse(first.deepEquals(differentVariable));
		assertFalse(first.deepEquals(reordered));
		assertFalse(first.deepEquals(new Function(
				FunctionSymbol.intern("equality-other-" + suffix, 2),
				List.of(sharedVariable, new Function(constantSymbol, List.of())))));
	}

	@Test
	@DisplayName("compare arguments through their union-find representatives")
	void compareUnifiedArgumentsStructurally() {
		String suffix = UUID.randomUUID().toString();
		Variable unifiedVariable = new Variable();
		Function schema = new Function(
				FunctionSymbol.intern("equality-schema-" + suffix, 0),
				List.of());
		unifiedVariable.union(schema);
		FunctionSymbol holderSymbol =
				FunctionSymbol.intern("equality-holder-" + suffix, 1);
		Function withVariable =
				new Function(holderSymbol, List.of(unifiedVariable));
		Function withSchema = new Function(holderSymbol, List.of(schema));

		assertTrue(withVariable.deepEquals(withSchema));
		assertTrue(withSchema.deepEquals(withVariable));
	}

	@Test
	@DisplayName("find exact and schema-reachable subterms without mutation")
	void findContainedSubterms() {
		String suffix = UUID.randomUUID().toString();
		Variable schemaArgument = new Variable();
		Function schema = new Function(
				FunctionSymbol.intern("containment-schema-" + suffix, 1),
				List.of(schemaArgument));
		Variable storedVariable = new Variable();
		storedVariable.union(schema);
		Variable directVariable = new Variable();
		Function outer = new Function(
				FunctionSymbol.intern("containment-outer-" + suffix, 2),
				List.of(storedVariable, directVariable));

		assertTrue(outer.contains(outer));
		assertTrue(outer.contains(schema));
		assertTrue(outer.contains(schemaArgument));
		assertTrue(outer.contains(directVariable));
		assertFalse(outer.contains(storedVariable));
		assertFalse(outer.contains(new Variable()));
		assertSame(storedVariable, outer.getChild(0));
	}

	@Test
	@DisplayName("compute depth and maximum arity across function arguments")
	void computeDepthAndMaximumArity() {
		String suffix = UUID.randomUUID().toString();
		Function constant = new Function(
				FunctionSymbol.intern("structural-constant-" + suffix, 0),
				List.of());
		Function binary = new Function(
				FunctionSymbol.intern("structural-binary-" + suffix, 2),
				List.of(new Variable(), constant));
		Function outer = new Function(
				FunctionSymbol.intern("structural-outer-" + suffix, 1),
				List.of(binary));

		assertEquals(0, constant.depth());
		assertEquals(2, outer.depth());
		assertEquals(0, constant.maxArity());
		assertEquals(2, outer.maxArity());
	}

	@Test
	@DisplayName("collect distinct symbols and variables while counting every occurrence")
	void collectSymbolsAndVariableOccurrences() {
		String suffix = UUID.randomUUID().toString();
		Variable repeatedVariable = new Variable();
		Variable otherVariable = new Variable();
		FunctionSymbol nestedSymbol =
				FunctionSymbol.intern("collection-nested-" + suffix, 1);
		Function firstNested = new Function(nestedSymbol, List.of(repeatedVariable));
		Function secondNested = new Function(nestedSymbol, List.of(otherVariable));
		FunctionSymbol outerSymbol =
				FunctionSymbol.intern("collection-outer-" + suffix, 3);
		Function outer = new Function(
				outerSymbol,
				List.of(firstNested, repeatedVariable, secondNested));
		Map<Variable, Integer> occurrences = new HashMap<>();

		assertEquals(Set.of(repeatedVariable, otherVariable), outer.getVariables());
		assertEquals(Set.of(outerSymbol, nestedSymbol), outer.getFunSymbols());
		outer.getVariableOccurrences(occurrences);
		assertEquals(Map.of(repeatedVariable, 2, otherVariable, 1), occurrences);
		assertFalse(outer.isGround());
	}

	@Test
	@DisplayName("follow variable schemas in structural queries")
	void followVariableSchemasInStructuralQueries() {
		String suffix = UUID.randomUUID().toString();
		Variable unifiedVariable = new Variable();
		FunctionSymbol schemaSymbol =
				FunctionSymbol.intern("structural-schema-" + suffix, 1);
		FunctionSymbol constantSymbol =
				FunctionSymbol.intern("schema-constant-" + suffix, 0);
		Function schema = new Function(
				schemaSymbol,
				List.of(new Function(constantSymbol, List.of())));
		unifiedVariable.union(schema);
		FunctionSymbol outerSymbol =
				FunctionSymbol.intern("structural-holder-" + suffix, 1);
		Function outer = new Function(outerSymbol, List.of(unifiedVariable));

		assertTrue(outer.isGround());
		assertTrue(outer.getVariables().isEmpty());
		assertEquals(2, outer.depth());
		assertEquals(
				Set.of(outerSymbol, schemaSymbol, constantSymbol),
				outer.getFunSymbols());
	}

	@Test
	@DisplayName("look up root, direct and nested positions without mutation")
	void lookUpValidPositions() {
		String suffix = UUID.randomUUID().toString();
		Variable nestedArgument = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern("lookup-nested-" + suffix, 1),
				List.of(nestedArgument));
		Variable directArgument = new Variable();
		Function function = new Function(
				FunctionSymbol.intern("lookup-outer-" + suffix, 2),
				List.of(nested, directArgument));

		assertSame(function, function.get(new Position()));
		assertSame(nested, function.get(0));
		assertSame(nested, function.get(new Position(0)));
		assertSame(nestedArgument,
				function.get(new Position(0).addLast(0)));
		assertSame(directArgument, function.get(new Position(1)));
		assertSame(nested, function.getChild(0));
	}

	@Test
	@DisplayName("distinguish deep and shallow lookup through a variable schema")
	void distinguishDeepAndShallowLookup() {
		String suffix = UUID.randomUUID().toString();
		Variable storedVariable = new Variable();
		Variable schemaArgument = new Variable();
		Function variableSchema = new Function(
				FunctionSymbol.intern("lookup-schema-" + suffix, 1),
				List.of(schemaArgument));
		storedVariable.union(variableSchema);
		Function outer = new Function(
				FunctionSymbol.intern("lookup-holder-" + suffix, 1),
				List.of(storedVariable));

		Position argumentPosition = new Position(0);
		Position nestedPosition = argumentPosition.addLast(0);

		assertSame(variableSchema, outer.get(argumentPosition));
		assertSame(storedVariable, outer.get(argumentPosition, true));
		assertSame(schemaArgument, outer.get(nestedPosition));
		assertNull(outer.get(nestedPosition, true));
		assertSame(storedVariable, outer.getChild(0));
	}

	@Test
	@DisplayName("return null for invalid lookup positions")
	void rejectInvalidLookupPositions() {
		String suffix = UUID.randomUUID().toString();
		Variable variable = new Variable();
		Function function = new Function(
				FunctionSymbol.intern("lookup-invalid-" + suffix, 1),
				List.of(variable));

		assertNull(function.get(-1));
		assertNull(function.get(1));
		assertNull(function.get(new Position(-1)));
		assertNull(function.get(new Position(1)));
		assertNull(function.get(new Position(0).addLast(0)));
		assertNull(function.get(new Position(0).addLast(0), true));
		assertSame(variable, function.getChild(0));
	}

	@Test
	@DisplayName("iterate positions root-first and in argument order")
	void iteratePositionsInPrefixOrder() {
		String suffix = UUID.randomUUID().toString();
		Function nested = new Function(
				FunctionSymbol.intern("position-nested-" + suffix, 1),
				List.of(new Variable()));
		Function function = new Function(
				FunctionSymbol.intern("position-outer-" + suffix, 2),
				List.of(nested, new Variable()));

		assertEquals(
				List.of("root", "[0]", "[0, 0]", "[1]"),
				positionLabels(function.iterator()));
		assertEquals(
				List.of("root", "[0]", "[0, 0]", "[1]"),
				positionLabels(function.shallowIterator()));
	}

	@Test
	@DisplayName("visit subterms directly in prefix order and preserve occurrences")
	void visitSubtermsInPrefixOrder() {
		String suffix = UUID.randomUUID().toString();
		Variable shared = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern("subterm-nested-" + suffix, 1),
				List.of(shared));
		Function function = new Function(
				FunctionSymbol.intern("subterm-outer-" + suffix, 2),
				List.of(nested, shared));
		List<Term> subterms = new ArrayList<>();

		function.forEachSubterm(subterms::add);

		assertEquals(4, subterms.size());
		assertSame(function, subterms.get(0));
		assertSame(nested, subterms.get(1));
		assertSame(shared, subterms.get(2));
		assertSame(shared, subterms.get(3));
		assertThrows(NullPointerException.class,
				() -> function.forEachSubterm(null));
	}

	@Test
	@DisplayName("keep iterator state stable and reject operations after exhaustion")
	void exhaustPositionIterator() {
		String suffix = UUID.randomUUID().toString();
		Function constant = new Function(
				FunctionSymbol.intern("position-constant-" + suffix, 0),
				List.of());
		Iterator<Position> positions = constant.iterator();

		assertTrue(positions.hasNext());
		assertTrue(positions.hasNext());
		assertTrue(positions.next().isEmpty());
		assertFalse(positions.hasNext());
		assertFalse(positions.hasNext());
		assertThrows(NoSuchElementException.class, positions::next);
		assertThrows(NoSuchElementException.class, positions::next);
		assertThrows(UnsupportedOperationException.class, positions::remove);
	}

	private static List<String> positionLabels(Iterator<Position> positions) {
		List<String> labels = new ArrayList<>();
		while (positions.hasNext()) {
			Position position = positions.next();
			labels.add(position.isEmpty() ? "root" : position.toString());
		}
		return labels;
	}

	@Test
	@DisplayName("return the replacement itself at the root position")
	void replaceAtRootPosition() {
		String suffix = UUID.randomUUID().toString();
		Variable originalArgument = new Variable();
		Function original = new Function(
				FunctionSymbol.intern("root-replaced-" + suffix, 1),
				List.of(originalArgument));
		Function replacement = new Function(
				FunctionSymbol.intern("root-replacement-" + suffix, 0),
				List.of());

		Term result = original.replace(new Position(), replacement);

		assertSame(replacement, result);
		assertSame(originalArgument, original.getChild(0));
	}

	@Test
	@DisplayName("replace a nested subterm and shallow-copy every unaffected branch")
	void replaceNestedSubterm() {
		String suffix = UUID.randomUUID().toString();
		Variable retainedVariable = new Variable();
		Variable replacedVariable = new Variable();
		Variable siblingVariable = new Variable();
		Function retainedBranch = new Function(
				FunctionSymbol.intern("retained-branch-" + suffix, 1),
				List.of(retainedVariable));
		Function nestedBranch = new Function(
				FunctionSymbol.intern("nested-branch-" + suffix, 2),
				List.of(replacedVariable, siblingVariable));
		Function original = new Function(
				FunctionSymbol.intern("replace-outer-" + suffix, 2),
				List.of(retainedBranch, nestedBranch));
		Function replacement = new Function(
				FunctionSymbol.intern("nested-replacement-" + suffix, 0),
				List.of());
		Position position = new Position(1).addLast(0);

		Function result = (Function) original.replace(position, replacement);
		Function copiedRetainedBranch = (Function) result.getChild(0);
		Function copiedNestedBranch = (Function) result.getChild(1);

		assertNotSame(original, result);
		assertNotSame(retainedBranch, copiedRetainedBranch);
		assertSame(retainedVariable, copiedRetainedBranch.getChild(0));
		assertNotSame(nestedBranch, copiedNestedBranch);
		assertSame(replacement, copiedNestedBranch.getChild(0));
		assertSame(siblingVariable, copiedNestedBranch.getChild(1));
		assertSame(replacedVariable, nestedBranch.getChild(0));
	}

	@Test
	@DisplayName("reject negative, excessive and below-variable replacement positions")
	void rejectInvalidReplacementPositions() {
		String suffix = UUID.randomUUID().toString();
		Variable variable = new Variable();
		Function original = new Function(
				FunctionSymbol.intern("invalid-position-" + suffix, 1),
				List.of(variable));
		Term replacement = new Variable();

		assertThrows(IndexOutOfBoundsException.class,
				() -> original.replace(new Position(-1), replacement));
		assertThrows(IndexOutOfBoundsException.class,
				() -> original.replace(new Position(1), replacement));
		assertThrows(IndexOutOfBoundsException.class,
				() -> original.replace(new Position(0).addLast(0), replacement));
		assertSame(variable, original.getChild(0));
	}

	@Test
	@DisplayName("shallow-copy function structure while retaining variables")
	void shallowCopyFunctionStructure() {
		String suffix = UUID.randomUUID().toString();
		Variable variable = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern("nested-" + suffix, 1),
				List.of(variable));
		Function original = new Function(
				FunctionSymbol.intern("outer-" + suffix, 2),
				List.of(nested, variable));

		Function copy = (Function) original.shallowCopy();

		assertNotSame(original, copy);
		assertSame(original.getRootSymbol(), copy.getRootSymbol());
		assertNotSame(nested, copy.getChild(0));
		assertSame(variable, ((Function) copy.getChild(0)).getChild(0));
		assertSame(variable, copy.getChild(1));
		assertTrue(original.deepEquals(copy));
	}

	@Test
	@DisplayName("deep-copy variables once and retain their occurrence sharing")
	void deepCopyFunctionVariables() {
		String suffix = UUID.randomUUID().toString();
		Variable repeatedVariable = new Variable();
		Function original = new Function(
				FunctionSymbol.intern("deep-" + suffix, 2),
				List.of(repeatedVariable, repeatedVariable));
		Map<Term, Term> copies = new HashMap<>();

		Function copy = (Function) original.deepCopy(copies);

		assertNotSame(original, copy);
		assertSame(original.getRootSymbol(), copy.getRootSymbol());
		assertNotSame(repeatedVariable, copy.getChild(0));
		assertSame(copy.getChild(0), copy.getChild(1));
		assertSame(copy.getChild(0), copies.get(repeatedVariable));
	}

	@Test
	@DisplayName("deep-copy only selected variables")
	void deepCopySelectedVariables() {
		String suffix = UUID.randomUUID().toString();
		Variable selectedVariable = new Variable();
		Variable retainedVariable = new Variable();
		Function original = new Function(
				FunctionSymbol.intern("selective-" + suffix, 2),
				List.of(selectedVariable, retainedVariable));

		Function copy = (Function) original.deepCopy(List.of(selectedVariable));

		assertNotSame(selectedVariable, copy.getChild(0));
		assertSame(retainedVariable, copy.getChild(1));
	}

	@Test
	@DisplayName("apply a substitution without modifying its source or mapped terms")
	void applySubstitutionWithoutMutation() {
		String suffix = UUID.randomUUID().toString();
		Variable mappedVariable = new Variable();
		Variable retainedVariable = new Variable();
		Variable replacementVariable = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern("nested-apply-" + suffix, 1),
				List.of(retainedVariable));
		Function original = new Function(
				FunctionSymbol.intern("apply-" + suffix, 2),
				List.of(mappedVariable, nested));
		Function replacement = new Function(
				FunctionSymbol.intern("replacement-" + suffix, 1),
				List.of(replacementVariable));
		Substitution substitution = new Substitution();
		substitution.add(mappedVariable, replacement);

		Function result = (Function) original.apply(substitution);

		assertNotSame(original, result);
		assertNotSame(replacement, result.getChild(0));
		assertSame(replacement.getRootSymbol(), result.getChild(0).getRootSymbol());
		assertSame(replacementVariable, ((Function) result.getChild(0)).getChild(0));
		assertNotSame(nested, result.getChild(1));
		assertSame(retainedVariable, ((Function) result.getChild(1)).getChild(0));
		assertSame(mappedVariable, original.getChild(0));
		assertSame(nested, original.getChild(1));
	}

	@Test
	@DisplayName("apply a substitution in place while shallow-copying replacements")
	void applySubstitutionInPlace() {
		String suffix = UUID.randomUUID().toString();
		Variable directVariable = new Variable();
		Variable nestedVariable = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern("nested-in-place-" + suffix, 1),
				List.of(nestedVariable));
		Function original = new Function(
				FunctionSymbol.intern("in-place-" + suffix, 2),
				List.of(directVariable, nested));
		Function replacement = new Function(
				FunctionSymbol.intern("in-place-replacement-" + suffix, 0),
				List.of());
		Substitution substitution = new Substitution();
		substitution.add(directVariable, replacement);
		substitution.add(nestedVariable, replacement);

		original.applyInPlace(substitution);

		assertNotSame(replacement, original.getChild(0));
		assertSame(replacement.getRootSymbol(), original.getChild(0).getRootSymbol());
		assertSame(nested, original.getChild(1));
		assertNotSame(replacement, nested.getChild(0));
		assertNotSame(original.getChild(0), nested.getChild(0));
		assertSame(replacement.getRootSymbol(), nested.getChild(0).getRootSymbol());
	}

	@Test
	@DisplayName("replace every variable with the same replacement reference")
	void replaceVariablesWithoutMutation() {
		String suffix = UUID.randomUUID().toString();
		Variable firstVariable = new Variable();
		Variable secondVariable = new Variable();
		Function nested = new Function(
				FunctionSymbol.intern("nested-replace-" + suffix, 1),
				List.of(secondVariable));
		Function original = new Function(
				FunctionSymbol.intern("replace-" + suffix, 2),
				List.of(firstVariable, nested));
		Function replacement = new Function(
				FunctionSymbol.intern("shared-replacement-" + suffix, 0),
				List.of());

		Function result = (Function) original.replaceVariables(replacement);

		assertNotSame(original, result);
		assertSame(replacement, result.getChild(0));
		assertNotSame(nested, result.getChild(1));
		assertSame(replacement, ((Function) result.getChild(1)).getChild(0));
		assertSame(firstVariable, original.getChild(0));
		assertSame(secondVariable, nested.getChild(0));
	}

	@Test
	@DisplayName("increment a matching hat function when applying a unary function")
	void incrementMatchingHatFunctionOnApplication() {
		String suffix = UUID.randomUUID().toString();
		Variable contextVariable = new Variable();
		FunctionSymbol unarySymbol =
				FunctionSymbol.intern("matching-unary-" + suffix, 1);
		Function context = new Function(unarySymbol, List.of(contextVariable));
		HatFunctionSymbol hatSymbol =
				HatFunctionSymbol.intern(context, contextVariable);
		Variable hatArgument = new Variable();
		HatFunction mappedHatFunction =
				new HatFunction(hatSymbol, hatArgument, List.of(2, 3));
		Variable mappedVariable = new Variable();
		Function original = new Function(unarySymbol, List.of(mappedVariable));
		Substitution substitution = new Substitution();
		substitution.add(mappedVariable, mappedHatFunction);

		HatFunction result = (HatFunction) original.apply(substitution);

		assertNotSame(mappedHatFunction, result);
		assertSame(hatSymbol, result.getRootSymbol());
		assertSame(hatArgument, result.getArgument());
		assertTrue(result.equalExponents(
				new HatFunction(hatSymbol, hatArgument, List.of(2, 4))));
		assertTrue(mappedHatFunction.equalExponents(
				new HatFunction(hatSymbol, hatArgument, List.of(2, 3))));
	}

	@Test
	@DisplayName("reject closing-exponent overflow in the unary hat optimization")
	void rejectClosingExponentOverflowInTheUnaryHatOptimization() {
		String suffix = UUID.randomUUID().toString();
		Variable contextVariable = new Variable();
		FunctionSymbol unarySymbol =
				FunctionSymbol.intern("matching-unary-overflow-" + suffix, 1);
		Function context = new Function(unarySymbol, List.of(contextVariable));
		HatFunctionSymbol hatSymbol =
				HatFunctionSymbol.intern(context, contextVariable);
		Variable hatArgument = new Variable();
		HatFunction mappedHatFunction = new HatFunction(
				hatSymbol, hatArgument, 2, Integer.MAX_VALUE);
		Variable mappedVariable = new Variable();
		Function original = new Function(unarySymbol, List.of(mappedVariable));
		Substitution substitution = new Substitution();
		substitution.add(mappedVariable, mappedHatFunction);

		assertThrows(ArithmeticException.class, () -> original.apply(substitution));
		assertEquals(
				List.of(2, Integer.MAX_VALUE), mappedHatFunction.getExponents());
		assertSame(hatArgument, mappedHatFunction.getArgument());
	}

	@Test
	@DisplayName("retain a unary function when the applied hat context does not match")
	void retainUnaryFunctionForNonMatchingHatContext() {
		String suffix = UUID.randomUUID().toString();
		Variable contextVariable = new Variable();
		FunctionSymbol contextSymbol =
				FunctionSymbol.intern("hat-context-" + suffix, 1);
		Function context = new Function(contextSymbol, List.of(contextVariable));
		HatFunctionSymbol hatSymbol =
				HatFunctionSymbol.intern(context, contextVariable);
		Variable hatArgument = new Variable();
		HatFunction mappedHatFunction =
				new HatFunction(hatSymbol, hatArgument, List.of(5, 7));
		Variable mappedVariable = new Variable();
		FunctionSymbol otherUnarySymbol =
				FunctionSymbol.intern("other-unary-" + suffix, 1);
		Function original = new Function(otherUnarySymbol, List.of(mappedVariable));
		Substitution substitution = new Substitution();
		substitution.add(mappedVariable, mappedHatFunction);

		Function result = (Function) original.apply(substitution);
		HatFunction appliedArgument = (HatFunction) result.getChild(0);

		assertSame(otherUnarySymbol, result.getRootSymbol());
		assertNotSame(mappedHatFunction, appliedArgument);
		assertSame(hatSymbol, appliedArgument.getRootSymbol());
		assertTrue(appliedArgument.equalExponents(mappedHatFunction));
		assertTrue(mappedHatFunction.equalExponents(
				new HatFunction(hatSymbol, hatArgument, List.of(5, 7))));
	}

	@Test
	@DisplayName("replace only the root symbol when converting a function to a tuple")
	void convertFunctionToTuple() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol symbol = FunctionSymbol.intern("function-" + suffix, 2);
		Term firstArgument = new Variable();
		Term secondArgument = new Function(
				FunctionSymbol.intern("constant-" + suffix, 0), List.of());
		Function function = new Function(
				symbol, List.of(firstArgument, secondArgument));

		Function tuple = (Function) function.toTuple();

		assertNotSame(function, tuple);
		assertSame(symbol.toTupleSymbol(), tuple.getRootSymbol());
		assertSame(firstArgument, tuple.getChild(0));
		assertSame(secondArgument, tuple.getChild(1));
		assertTrue(tuple.getRootSymbol().isTupleSymbol());
	}

	@Test
	@DisplayName("leave a function unchanged when its root already has the requested kind")
	void keepFunctionsWithAlreadyConvertedRoots() {
		String suffix = UUID.randomUUID().toString();
		Function function = new Function(
				FunctionSymbol.intern("function-" + suffix, 0), List.of());
		Function tuple = new Function(
				FunctionSymbol.intern("tuple-" + suffix, 0).toTupleSymbol(),
				List.of());

		assertSame(function, function.toFunction());
		assertSame(tuple, tuple.toTuple());
	}

	@Test
	@DisplayName("round-trip root conversion while retaining argument references and order")
	void roundTripRootConversion() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol symbol = FunctionSymbol.intern("round-trip-" + suffix, 2);
		Term firstArgument = new Variable();
		Term secondArgument = new Variable();
		Function original = new Function(
				symbol, List.of(firstArgument, secondArgument));

		Function tuple = (Function) original.toTuple();
		Function restored = (Function) tuple.toFunction();

		assertNotSame(original, restored);
		assertSame(symbol, restored.getRootSymbol());
		assertSame(firstArgument, restored.getChild(0));
		assertSame(secondArgument, restored.getChild(1));
		assertFalse(restored.getRootSymbol().isTupleSymbol());
		assertTrue(original.deepEquals(restored));
	}
}
