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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.lp.binaryunfolding;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.SoP;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class LoopingPairTest {

	@Test
	void prependsCompatibleRuleWithoutChangingOriginalPair() {
		Function constant = function("looping-pair-order-constant");
		BinaryRuleLp originalRule = rule(
				function("looping-pair-order-link", constant),
				function("looping-pair-order-link", constant));
		LoopingPair originalPair = loopingPair(originalRule);
		String originalRendering = originalPair.toString();

		BinaryRuleLp prependedRule = rule(
				function("looping-pair-order-head", constant),
				function("looping-pair-order-link", constant));
		LoopingPair extendedPair = originalPair.add(prependedRule);

		assertNotSame(originalPair, extendedPair);
		assertEquals(originalRendering, originalPair.toString());
		assertTrue(extendedPair.toString().contains(
				"binseq = <" + prependedRule + ", " + originalRule + ">"));
	}

	@Test
	void rejectsIncompatibleRuleWithoutAllocatingAnotherPair() {
		Variable originalVariable = new Variable();
		BinaryRuleLp originalRule = rule(
				function("looping-pair-rejection-head", originalVariable),
				function("looping-pair-rejection-head", originalVariable));
		LoopingPair originalPair = loopingPair(originalRule);

		Variable incompatibleVariable = new Variable();
		BinaryRuleLp incompatibleRule = rule(
				function("looping-pair-rejection-candidate", incompatibleVariable),
				function("looping-pair-rejection-other", incompatibleVariable));

		assertSame(originalPair, originalPair.add(incompatibleRule));
	}

	@Test
	void usesIncrementallyUpdatedTauForPrependedRule() {
		Variable originalVariable = new Variable();
		BinaryRuleLp originalRule = rule(
				function("looping-pair-tau-link", originalVariable),
				function("looping-pair-tau-link", originalVariable));
		LoopingPair originalPair = loopingPair(originalRule);

		Variable prependedVariable = new Variable();
		BinaryRuleLp prependedRule = rule(
				function("looping-pair-tau-head", prependedVariable),
				function("looping-pair-tau-link", prependedVariable));
		LoopingPair extendedPair = originalPair.add(prependedRule);
		Mode selectedArgument = new Mode(
				prependedRule.getHeadPredicateSymbol(),
				List.of(0));

		Function nonTerminatingQuery =
				extendedPair.provesNonTerminationOf(selectedArgument);

		assertNotNull(nonTerminatingQuery);
		assertEquals("looping-pair-tau-head(a)",
				nonTerminatingQuery.toString());
	}

	@Test
	void acceptsModeArgumentCoveredByGroundHeadArgument() {
		Function groundArgument = function("looping-pair-ground-argument");
		Function head = function("looping-pair-ground-head", groundArgument);
		BinaryRuleLp rule = rule(
				head,
				function("looping-pair-ground-body", groundArgument));
		LoopingPair pair = new LoopingPair(
				List.of(rule),
				new SoP(List.of()));
		Mode selectedArgument = new Mode(
				rule.getHeadPredicateSymbol(),
				List.of(0));

		Function nonTerminatingQuery =
				pair.provesNonTerminationOf(selectedArgument);

		assertNotNull(nonTerminatingQuery);
		assertNotSame(head, nonTerminatingQuery);
		assertEquals(
				"looping-pair-ground-head(looping-pair-ground-argument)",
				nonTerminatingQuery.toString());
	}

	@Test
	void rejectsModeArgumentCoveredByNeitherTauNorGroundness() {
		Variable variable = new Variable();
		BinaryRuleLp rule = rule(
				function("looping-pair-uncovered-head", variable),
				function("looping-pair-uncovered-body", variable));
		LoopingPair pair = new LoopingPair(
				List.of(rule),
				new SoP(List.of()));
		Mode selectedArgument = new Mode(
				rule.getHeadPredicateSymbol(),
				List.of(0));

		assertNull(pair.provesNonTerminationOf(selectedArgument));
	}

	@Test
	void rejectsModeWithDifferentPredicateSymbol() {
		Variable variable = new Variable();
		BinaryRuleLp rule = rule(
				function("looping-pair-mode-head", variable),
				function("looping-pair-mode-head", variable));
		LoopingPair pair = loopingPair(rule);
		Mode otherMode = new Mode(
				FunctionSymbol.intern("looping-pair-other-mode", 1),
				List.of(0));

		assertNull(pair.provesNonTerminationOf(otherMode));
	}

	@Test
	void rejectsEveryModeWhenBinarySequenceIsEmpty() {
		LoopingPair pair = new LoopingPair(List.of(), new SoP(List.of()));
		Mode mode = new Mode(
				FunctionSymbol.intern("looping-pair-empty-mode", 0),
				List.of());

		assertNull(pair.provesNonTerminationOf(mode));
	}

	private static LoopingPair loopingPair(BinaryRuleLp rule) {
		List<BinaryRuleLp> binarySequence = List.of(rule);
		return new LoopingPair(binarySequence, new SoP(binarySequence));
	}

	private static BinaryRuleLp rule(Function head, Function body) {
		return new BinaryRuleLp(head, body, 0);
	}

	private static Function function(String name, Term... arguments) {
		return new Function(
				FunctionSymbol.intern(name, arguments.length),
				List.of(arguments));
	}
}
