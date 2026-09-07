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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.ReadOnlyTermUnifier;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class ReadOnlyTermUnifierTest {

	@Test
	@DisplayName("agree with destructive connectability and reset local state")
	void agreeWithDestructiveConnectabilityAndResetLocalState() {
		FunctionSymbol defined = FunctionSymbol.intern(
				"read-only-unifier-defined", 1);
		FunctionSymbol outer = FunctionSymbol.intern(
				"read-only-unifier-outer", 2);
		FunctionSymbol constructor = FunctionSymbol.intern(
				"read-only-unifier-constructor", 1);
		Variable ruleVariable = new Variable();
		Trs trs = new Trs("", List.of(new RuleTrs(
				new Function(defined, List.of(ruleVariable)),
				ruleVariable)), "FULL");
		Variable repeated = new Variable();
		Variable targetVariable = new Variable();
		Function constant = new Function(FunctionSymbol.intern(
				"read-only-unifier-constant", 0), List.of());
		List<Term> sources = List.of(
				new Variable(),
				new Function(outer, List.of(
						new Function(defined, List.of(repeated)), repeated)),
				new Function(outer, List.of(repeated, repeated)));
		List<Term> targets = List.of(
				constant,
				new Function(outer, List.of(constant, targetVariable)),
				new Function(outer, List.of(
						new Function(constructor, List.of(targetVariable)),
						targetVariable)),
				new Function(constructor, List.of(constant)));

		for (Term source : sources) {
			ReadOnlyTermUnifier unifier = new ReadOnlyTermUnifier(
					source.buildConnectabilityPattern(trs));
			ReadOnlyTermUnifier uncheckedUnifier =
					ReadOnlyTermUnifier.forFreshLinearSource(
							source.buildConnectabilityPattern(trs));
			for (Term target : targets)
				for (ReadOnlyTermUnifier candidateUnifier : List.of(
						unifier, uncheckedUnifier))
					assertEquals(
							source.isConnectableTo(target, trs),
							candidateUnifier.isUnifiableWith(target));
		}
	}

	@Test
	@DisplayName("handle repeated variables, occurs checks and reusable state")
	void handleRepeatedVariablesOccursChecksAndReusableState() {
		FunctionSymbol pair = FunctionSymbol.intern(
				"read-only-unifier-pair", 2);
		FunctionSymbol unary = FunctionSymbol.intern(
				"read-only-unifier-unary", 1);
		Function firstConstant = new Function(FunctionSymbol.intern(
				"read-only-unifier-first", 0), List.of());
		Function secondConstant = new Function(FunctionSymbol.intern(
				"read-only-unifier-second", 0), List.of());
		Variable repeated = new Variable();
		Term repeatedSource = new Function(
				pair, List.of(repeated, repeated));
		Term compatibleTarget = new Function(
				pair, List.of(firstConstant, firstConstant));
		Term incompatibleTarget = new Function(
				pair, List.of(firstConstant, secondConstant));
		ReadOnlyTermUnifier reusable =
				new ReadOnlyTermUnifier(repeatedSource);

		assertTrue(reusable.isUnifiableWith(compatibleTarget));
		assertFalse(reusable.isUnifiableWith(incompatibleTarget));
		assertTrue(reusable.isUnifiableWith(compatibleTarget));
		assertEquals(
				destructiveUnifiability(repeatedSource, incompatibleTarget),
				reusable.isUnifiableWith(incompatibleTarget));

		Variable cyclic = new Variable();
		Term containingTerm = new Function(unary, List.of(cyclic));
		assertFalse(new ReadOnlyTermUnifier(cyclic)
				.isUnifiableWith(containingTerm));
		assertEquals(
				destructiveUnifiability(cyclic, containingTerm),
				new ReadOnlyTermUnifier(cyclic)
						.isUnifiableWith(containingTerm));

		Variable firstCycleVariable = new Variable();
		Variable secondCycleVariable = new Variable();
		Term nonlinearSource = new Function(pair, List.of(
				firstCycleVariable,
				new Function(unary, List.of(firstCycleVariable))));
		Term disjointNonlinearTarget = new Function(pair, List.of(
				new Function(unary, List.of(secondCycleVariable)),
				secondCycleVariable));
		assertFalse(new ReadOnlyTermUnifier(nonlinearSource)
				.isUnifiableWith(disjointNonlinearTarget));
		assertFalse(destructiveUnifiability(
				nonlinearSource, disjointNonlinearTarget));
	}

	@Test
	@DisplayName("omit occurs checks for fresh linear connectability patterns")
	void omitOccursChecksForFreshLinearConnectabilityPatterns() {
		FunctionSymbol unary = FunctionSymbol.intern(
				"read-only-unifier-exhaustive-unary", 1);
		FunctionSymbol pair = FunctionSymbol.intern(
				"read-only-unifier-exhaustive-pair", 2);
		Function firstConstant = new Function(FunctionSymbol.intern(
				"read-only-unifier-exhaustive-first", 0), List.of());
		Function secondConstant = new Function(FunctionSymbol.intern(
				"read-only-unifier-exhaustive-second", 0), List.of());
		List<Term> smallTerms = smallTerms(
				2, unary, pair, firstConstant, secondConstant,
				new Variable(), new Variable());
		Trs emptyTrs = new Trs("", List.of(), "FULL");

		for (Term sourceTemplate : smallTerms) {
			Term linearSource =
					sourceTemplate.buildConnectabilityPattern(emptyTrs);
			Map<Variable, Integer> occurrences = new HashMap<>();
			linearSource.getVariableOccurrences(occurrences);
			assertTrue(occurrences.values().stream()
					.allMatch(count -> count == 1));

			ReadOnlyTermUnifier unifier =
					ReadOnlyTermUnifier.forFreshLinearSource(linearSource);
			for (Term target : smallTerms)
				assertEquals(
						destructiveUnifiability(linearSource, target),
						unifier.isUnifiableWith(target),
						() -> linearSource + " and " + target);
		}
	}

	@Test
	@DisplayName("discard stale bindings after growing the identity table")
	void discardStaleBindingsAfterGrowingIdentityTable() {
		int distinctVariableCount = 40;
		int arity = distinctVariableCount + 1;
		FunctionSymbol tuple = FunctionSymbol.intern(
				"read-only-unifier-wide", arity);
		Function firstConstant = new Function(FunctionSymbol.intern(
				"read-only-unifier-wide-first", 0), List.of());
		Function secondConstant = new Function(FunctionSymbol.intern(
				"read-only-unifier-wide-second", 0), List.of());
		List<Term> variables = new ArrayList<>(arity);
		List<Term> compatibleArguments = new ArrayList<>(arity);
		List<Term> incompatibleArguments = new ArrayList<>(arity);
		for (int argumentIndex = 0;
				argumentIndex < distinctVariableCount;
				argumentIndex++) {
			variables.add(new Variable());
			compatibleArguments.add(firstConstant);
			incompatibleArguments.add(firstConstant);
		}
		variables.add(variables.get(distinctVariableCount - 1));
		compatibleArguments.add(firstConstant);
		incompatibleArguments.add(secondConstant);

		ReadOnlyTermUnifier reusable = new ReadOnlyTermUnifier(
				new Function(tuple, variables));

		assertTrue(reusable.isUnifiableWith(
				new Function(tuple, compatibleArguments)));
		assertFalse(reusable.isUnifiableWith(
				new Function(tuple, incompatibleArguments)));
		assertTrue(reusable.isUnifiableWith(
				new Function(tuple, compatibleArguments)));
	}

	@Test
	@DisplayName("reset a grown occurs queue after an early cycle rejection")
	void resetGrownOccursQueueAfterEarlyCycleRejection() {
		int arity = 41;
		FunctionSymbol wide = FunctionSymbol.intern(
				"read-only-unifier-wide-cycle", arity);
		Function constant = new Function(FunctionSymbol.intern(
				"read-only-unifier-cycle-constant", 0), List.of());
		Variable cyclic = new Variable();
		List<Term> cyclicArguments = new ArrayList<>(arity);
		cyclicArguments.add(cyclic);
		for (int argumentIndex = 1;
				argumentIndex < arity;
				argumentIndex++)
			cyclicArguments.add(constant);
		ReadOnlyTermUnifier reusable = new ReadOnlyTermUnifier(cyclic);

		assertFalse(reusable.isUnifiableWith(
				new Function(wide, cyclicArguments)));
		assertTrue(reusable.isUnifiableWith(constant));
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
