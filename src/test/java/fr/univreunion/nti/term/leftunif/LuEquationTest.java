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

package fr.univreunion.nti.term.leftunif;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class LuEquationTest {

	@AfterEach
	void resetEquationTime() {
		LuEquation.resetTime();
	}

	@Test
	@DisplayName("orient equations and increment global time on construction")
	void orientEquationsAndIncrementTime() {
		LuEquation.resetTime();
		String suffix = UUID.randomUUID().toString();
		Variable variable = new Variable();
		Function function = new Function(
				FunctionSymbol.intern("lu-orientation-" + suffix, 0),
				List.of());

		LuEquation variableFunctionEquation =
				new LuEquation(function, variable);

		assertSame(variable, variableFunctionEquation.getLeft());
		assertSame(function, variableFunctionEquation.getRight());
		assertEquals(1, LuEquation.getCurrentTime());

		LuVariable lowerPower = new LuVariable(variable, 1);
		LuVariable higherPower = new LuVariable(variable, 3);
		LuEquation poweredVariableEquation =
				new LuEquation(lowerPower, higherPower);

		assertSame(higherPower, poweredVariableEquation.getLeft());
		assertSame(lowerPower, poweredVariableEquation.getRight());
		assertEquals(2, LuEquation.getCurrentTime());
	}

	@Test
	@DisplayName("cancel identical and equivalent variable equations")
	void cancelVariableEquations() {
		Variable variable = new Variable();
		LuEquation identicalEquation = new LuEquation(variable, variable);
		LuEquation equivalentEquation =
				new LuEquation(variable, new LuVariable(variable, 0));
		Variable otherVariable = new Variable();
		LuEquation retainedEquation =
				new LuEquation(variable, otherVariable);

		assertEquals(List.of(), identicalEquation.distributeAndCancel());
		assertEquals(List.of(), equivalentEquation.distributeAndCancel());
		assertEquals(List.of(retainedEquation),
				retainedEquation.distributeAndCancel());
	}

	@Test
	@DisplayName("decompose equal-root functions in argument order")
	void decomposeEqualRootFunctionsInOrder() {
		LuEquation.resetTime();
		String suffix = UUID.randomUUID().toString();
		Variable firstLeft = new Variable();
		Variable secondLeft = new Variable();
		Variable firstRight = new Variable();
		Variable secondRight = new Variable();
		FunctionSymbol symbol =
				FunctionSymbol.intern("lu-decomposition-" + suffix, 2);
		LuEquation equation = new LuEquation(
				new Function(symbol, List.of(firstLeft, secondLeft)),
				new Function(symbol, List.of(firstRight, secondRight)));

		List<LuEquation> decomposed = equation.distributeAndCancel();

		assertEquals(2, decomposed.size());
		assertConnects(decomposed.get(0), firstLeft, firstRight);
		assertConnects(decomposed.get(1), secondLeft, secondRight);
		assertEquals(3, LuEquation.getCurrentTime());
	}

	@Test
	@DisplayName("reject root conflicts and variables contained in function terms")
	void rejectRootConflictsAndOccursCheck() {
		LuEquation.resetTime();
		String suffix = UUID.randomUUID().toString();
		Function firstConstant = new Function(
				FunctionSymbol.intern("lu-first-root-" + suffix, 0),
				List.of());
		Function secondConstant = new Function(
				FunctionSymbol.intern("lu-second-root-" + suffix, 0),
				List.of());
		LuEquation rootConflict =
				new LuEquation(firstConstant, secondConstant);

		assertNull(rootConflict.distributeAndCancel());
		assertEquals(1, LuEquation.getCurrentTime());

		Variable variable = new Variable();
		Function containingFunction = new Function(
				FunctionSymbol.intern("lu-containing-" + suffix, 1),
				List.of(variable));
		LuEquation occursCheck =
				new LuEquation(variable, containingFunction);

		assertNull(occursCheck.distributeAndCancel());
		assertEquals(2, LuEquation.getCurrentTime());
	}

	@Test
	@DisplayName("reduce function sides in place and increment time once")
	void reduceFunctionSidesInPlaceAndIncrementTimeOnce() {
		LuEquation.resetTime();
		String suffix = UUID.randomUUID().toString();
		Variable reducibleVariable = new Variable();
		Variable retainedVariable = new Variable();
		Function replacement = new Function(
				FunctionSymbol.intern("lu-replacement-" + suffix, 0),
				List.of());
		LuEquation rule = new LuEquation(reducibleVariable, replacement);
		Function functionSide = new Function(
				FunctionSymbol.intern("lu-reduced-function-" + suffix, 2),
				List.of(reducibleVariable, reducibleVariable));
		LuEquation equation = new LuEquation(retainedVariable, functionSide);

		equation.reduceWith(rule);

		assertSame(retainedVariable, equation.getLeft());
		assertSame(functionSide, equation.getRight());
		assertNotSame(replacement, functionSide.getChild(0));
		assertNotSame(replacement, functionSide.getChild(1));
		assertNotSame(functionSide.getChild(0), functionSide.getChild(1));
		assertTrue(functionSide.getChild(0).deepEquals(replacement));
		assertTrue(functionSide.getChild(1).deepEquals(replacement));
		assertEquals(3, LuEquation.getCurrentTime());
	}

	@Test
	@DisplayName("leave irreducible equations and global time unchanged")
	void leaveIrreducibleEquationsAndTimeUnchanged() {
		LuEquation.resetTime();
		String suffix = UUID.randomUUID().toString();
		Variable ruleVariable = new Variable();
		Function replacement = new Function(
				FunctionSymbol.intern("lu-unused-replacement-" + suffix, 0),
				List.of());
		LuEquation rule = new LuEquation(ruleVariable, replacement);
		Variable retainedVariable = new Variable();
		Function retainedFunction = new Function(
				FunctionSymbol.intern("lu-irreducible-" + suffix, 0),
				List.of());
		LuEquation equation = new LuEquation(retainedVariable, retainedFunction);
		int timeBeforeReduction = LuEquation.getCurrentTime();

		equation.reduceWith(rule);

		assertSame(retainedVariable, equation.getLeft());
		assertSame(retainedFunction, equation.getRight());
		assertEquals(timeBeforeReduction, LuEquation.getCurrentTime());
	}

	@Test
	@DisplayName("reorient an equation after reducing one of its variable sides")
	void reorientAfterReducingVariableSide() {
		LuEquation.resetTime();
		String suffix = UUID.randomUUID().toString();
		Variable reducibleVariable = new Variable();
		Function replacement = new Function(
				FunctionSymbol.intern("lu-reorientation-result-" + suffix, 0),
				List.of());
		LuEquation rule = new LuEquation(reducibleVariable, replacement);
		Variable retainedVariable = new Variable();
		LuEquation equation = new LuEquation(reducibleVariable, retainedVariable);

		equation.reduceWith(rule);

		assertSame(retainedVariable, equation.getLeft());
		assertTrue(equation.getRight().deepEquals(replacement));
		assertEquals(3, LuEquation.getCurrentTime());
	}

	private static void assertConnects(
			LuEquation equation,
			Term first,
			Term second) {

		boolean direct = equation.getLeft() == first &&
				equation.getRight() == second;
		boolean reverse = equation.getLeft() == second &&
				equation.getRight() == first;
		assertTrue(direct || reverse);
	}
}
