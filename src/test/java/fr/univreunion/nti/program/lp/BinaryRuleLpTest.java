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

package fr.univreunion.nti.program.lp;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertIterableEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class BinaryRuleLpTest {

	@Test
	void exposesPredicatesAndGroundHeadArguments() {
		Variable variable = new Variable();
		Function constant = function("binary-rule-ground-constant");
		BinaryRuleLp rule = rule(
				function("binary-rule-head", variable, constant),
				function("binary-rule-body", variable));

		assertSame(rule.getHead().getRootSymbol(),
				rule.getHeadPredicateSymbol());
		assertSame(rule.getBody(0).getRootSymbol(),
				rule.getBodyPredicateSymbol());
		assertFalse(rule.isGroundHeadArgument(0));
		assertTrue(rule.isGroundHeadArgument(1));
	}

	@Test
	void detectsTauUnitLoopsAndPluggableRules() {
		Variable firstVariable = new Variable();
		BinaryRuleLp firstRule = rule(
				function("tau-loop-predicate", firstVariable),
				function("tau-link-predicate", firstVariable));

		Variable secondVariable = new Variable();
		BinaryRuleLp secondRule = rule(
				function("tau-link-predicate", secondVariable),
				function("tau-tail-predicate", secondVariable));

		Variable loopVariable = new Variable();
		BinaryRuleLp unitLoop = rule(
				function("tau-unit-predicate", loopVariable),
				function("tau-unit-predicate", loopVariable));

		SoP tau = new SoP(List.of(firstRule, secondRule, unitLoop));

		assertTrue(firstRule.isTauPluggableInto(secondRule, tau));
		assertFalse(secondRule.isTauPluggableInto(firstRule, tau));
		assertTrue(unitLoop.isTauUnitLoop(tau));
		assertFalse(firstRule.isTauUnitLoop(tau));
	}

	@Test
	void findsHeadArgumentsViolatingDn1() {
		Variable sharedVariable = new Variable();
		Variable independentVariable = new Variable();
		BinaryRuleLp rule = rule(
				function(
						"dn1-head",
						sharedVariable,
						function("dn1-wrapper", sharedVariable),
						independentVariable),
				function("dn1-body"));

		assertIterableEquals(
				List.of(0, 1),
				rule.findDN1ViolatingHeadArgumentIndexes());
	}

	@Test
	void computesValuesRequiredByDn2() {
		Function firstConstant = function("dn2-first-constant");
		Function secondConstant = function("dn2-second-constant");
		Function incompatibleConstant = function("dn2-incompatible-constant");
		BinaryRuleLp seedRule = rule(
				function("dn2-head", firstConstant, secondConstant),
				function("dn2-seed-body"));
		SoP tau = new SoP(List.of(seedRule));

		BinaryRuleLp compatibleRule = rule(
				function(
						"dn2-head",
						new Variable(),
						incompatibleConstant),
				function("dn2-compatible-body"));

		Term[] requiredValues = compatibleRule.computeDN2RequiredValues(tau);

		assertSame(firstConstant, requiredValues[0]);
		assertNull(requiredValues[1]);
	}

	@Test
	void findsBodyArgumentsViolatingDn3() {
		Function requiredConstant = function("dn3-required-constant");
		BinaryRuleLp seedRule = rule(
				function("dn3-body-predicate", requiredConstant),
				function("dn3-seed-body"));
		SoP tau = new SoP(List.of(seedRule));

		BinaryRuleLp rule = rule(
				function("dn3-head"),
				function(
						"dn3-body-predicate",
						new Variable()));

		assertIterableEquals(
				List.of(0),
				rule.findDN3ViolatingBodyArgumentIndexes(tau));

		BinaryRuleLp compliantRule = rule(
				function("dn3-compliant-head"),
				function("dn3-body-predicate", requiredConstant));
		assertTrue(
				compliantRule.findDN3ViolatingBodyArgumentIndexes(tau).isEmpty());
	}

	@Test
	void findsHeadArgumentsViolatingDn4() {
		Variable seedVariable = new Variable();
		BinaryRuleLp seedRule = rule(
				function("dn4-head", seedVariable),
				function("dn4-seed-body", seedVariable));
		SoP tau = new SoP(List.of(seedRule));

		Variable sharedVariable = new Variable();
		BinaryRuleLp rule = rule(
				function("dn4-head", sharedVariable),
				function("dn4-unmapped-body", sharedVariable));

		assertIterableEquals(
				List.of(0),
				rule.findDN4ViolatingHeadArgumentIndexes(tau));

		BinaryRuleLp compliantRule = rule(
				function("dn4-head", new Variable()),
				function("dn4-unmapped-body", new Variable()));
		assertTrue(
				compliantRule.findDN4ViolatingHeadArgumentIndexes(tau).isEmpty());
	}

	@Test
	void preservesOneDn4ViolationForEachConflictingBodyArgument() {
		Variable seedVariable = new Variable();
		BinaryRuleLp seedRule = rule(
				function("dn4-multiple-head", seedVariable),
				function("dn4-multiple-seed-body", seedVariable));
		SoP tau = new SoP(List.of(seedRule));

		Variable firstSharedVariable = new Variable();
		Variable secondSharedVariable = new Variable();
		BinaryRuleLp rule = rule(
				function(
					"dn4-multiple-head",
					function(
						"dn4-multiple-wrapper",
						firstSharedVariable,
						secondSharedVariable)),
				function(
					"dn4-multiple-unmapped-body",
					firstSharedVariable,
					new Variable(),
					secondSharedVariable));

		assertIterableEquals(
				List.of(0, 0),
				rule.findDN4ViolatingHeadArgumentIndexes(tau));
	}

	@Test
	void findsDn4ViolationsWhenFewerBodyVariableSetsAreStored() {
		BinaryRuleLp seedRule = rule(
				function(
						"dn4-stored-body-head",
						new Variable(),
						new Variable()),
				function("dn4-stored-body-seed-body"));
		SoP tau = new SoP(List.of(seedRule));

		Variable firstSharedVariable = new Variable();
		Variable secondSharedVariable = new Variable();
		BinaryRuleLp rule = rule(
				function(
						"dn4-stored-body-head",
						firstSharedVariable,
						secondSharedVariable),
				function(
						"dn4-stored-body-unmapped-body",
						function(
								"dn4-stored-body-wrapper",
								firstSharedVariable,
								secondSharedVariable)));

		assertIterableEquals(
				List.of(0, 1),
				rule.findDN4ViolatingHeadArgumentIndexes(tau));
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
