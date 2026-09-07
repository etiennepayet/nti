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

package fr.univreunion.nti.term.leftunif;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class LuVariableTest {

	@Test
	@DisplayName("compare variables by embedded identity and rho power")
	void compareByEmbeddedIdentityAndRhoPower() {
		Variable embeddedVariable = new Variable();
		Variable otherVariable = new Variable();
		LuVariable zeroPower = new LuVariable(embeddedVariable, 0);
		LuVariable positivePower = new LuVariable(embeddedVariable, 2);

		assertTrue(zeroPower.sameAs(embeddedVariable));
		assertTrue(embeddedVariable.sameAs(zeroPower));
		assertTrue(positivePower.sameAs(
				new LuVariable(embeddedVariable, 2)));
		assertFalse(positivePower.sameAs(embeddedVariable));
		assertFalse(positivePower.sameAs(
				new LuVariable(embeddedVariable, 1)));
		assertFalse(positivePower.sameAs(new LuVariable(otherVariable, 2)));
	}

	@Test
	@DisplayName("contain only lower powers of the same embedded variable")
	void containLowerPowersOfSameEmbeddedVariable() {
		Variable embeddedVariable = new Variable();
		Variable otherVariable = new Variable();
		LuVariable variable = new LuVariable(embeddedVariable, 2);

		assertTrue(variable.contains(variable));
		assertTrue(variable.contains(embeddedVariable));
		assertTrue(variable.contains(new LuVariable(embeddedVariable, 0)));
		assertTrue(variable.contains(new LuVariable(embeddedVariable, 1)));
		assertTrue(variable.contains(new LuVariable(embeddedVariable, 2)));
		assertFalse(variable.contains(new LuVariable(embeddedVariable, 3)));
		assertFalse(variable.contains(otherVariable));
		assertFalse(variable.contains(new LuVariable(otherVariable, 1)));
	}

	@Test
	@DisplayName("copy and distribute without modifying the source variable")
	void copyAndDistributeWithoutModifyingSource() {
		Variable embeddedVariable = new Variable();
		LuVariable source = new LuVariable(embeddedVariable, 2);

		Term copiedTerm = source.shallowCopy();
		Term distributedTerm = source.distribute(3);

		LuVariable copy = (LuVariable) copiedTerm;
		LuVariable distributed = (LuVariable) distributedTerm;
		assertNotSame(source, copy);
		assertSame(embeddedVariable, copy.getVariable());
		assertEquals(2, copy.getRho());
		assertNotSame(source, distributed);
		assertSame(embeddedVariable, distributed.getVariable());
		assertEquals(5, distributed.getRho());
		assertSame(embeddedVariable, source.getVariable());
		assertEquals(2, source.getRho());
	}

	@Test
	@DisplayName("reduce matching powers and distribute the remaining rho")
	void reduceMatchingPowersAndDistributeRemainingRho() {
		String suffix = UUID.randomUUID().toString();
		Variable embeddedVariable = new Variable();
		Variable replacementVariable = new Variable();
		Function replacement = new Function(
				FunctionSymbol.intern("lu-variable-replacement-" + suffix, 1),
				List.of(replacementVariable));
		LuEquation rule = new LuEquation(
				new LuVariable(embeddedVariable, 1), replacement);
		LuVariable source = new LuVariable(embeddedVariable, 3);

		Term reduced = source.reduceWithLeftUnificationRule(rule);

		assertTrue(source.hasChanged());
		Function reducedFunction = (Function) reduced;
		LuVariable reducedArgument =
				(LuVariable) reducedFunction.getChild(0);
		assertSame(replacementVariable, reducedArgument.getVariable());
		assertEquals(2, reducedArgument.getRho());
		assertSame(embeddedVariable, source.getVariable());
		assertEquals(3, source.getRho());
	}

	@Test
	@DisplayName("leave lower powers and other embedded variables irreducible")
	void leaveNonMatchingVariablesIrreducible() {
		String suffix = UUID.randomUUID().toString();
		Variable embeddedVariable = new Variable();
		Variable otherVariable = new Variable();
		LuVariable lowerPower = new LuVariable(embeddedVariable, 1);
		LuVariable otherEmbeddedVariable = new LuVariable(otherVariable, 3);
		LuEquation rule = new LuEquation(
				new LuVariable(embeddedVariable, 2),
				new Function(FunctionSymbol.intern(
						"lu-variable-irreducible-" + suffix, 0), List.of()));

		assertSame(lowerPower,
				lowerPower.reduceWithLeftUnificationRule(rule));
		assertFalse(lowerPower.hasChanged());
		assertSame(otherEmbeddedVariable,
				otherEmbeddedVariable.reduceWithLeftUnificationRule(rule));
		assertFalse(otherEmbeddedVariable.hasChanged());
	}

	@Test
	@DisplayName("apply rho and complete a partial substitution chain")
	void applyAndCompletePartialRhoChain() {
		Variable first = new Variable();
		Variable second = new Variable();
		Substitution rho = new Substitution();
		rho.addReplace(first, second);
		LuVariable source = new LuVariable(first, 3);

		Term result = source.applyAndCompleteRho(rho);

		Variable third = (Variable) rho.get(second);
		Variable fourth = (Variable) rho.get(third);
		assertSame(fourth, result);
		assertSame(second, rho.get(first));
		assertSame(third, rho.get(second));
		assertSame(fourth, rho.get(third));
		assertSame(first, source.getVariable());
		assertEquals(3, source.getRho());
	}

	@Test
	@DisplayName("apply complete rho chains or retain their unresolved suffix")
	void applyCompleteOrPartialRhoChain() {
		Variable first = new Variable();
		Variable second = new Variable();
		Variable third = new Variable();
		Variable fourth = new Variable();
		Substitution completeRho = new Substitution();
		completeRho.addReplace(first, second);
		completeRho.addReplace(second, third);
		completeRho.addReplace(third, fourth);
		LuVariable completeSource = new LuVariable(first, 3);

		assertSame(fourth, completeSource.applyRho(completeRho));
		assertSame(first, completeSource.getVariable());
		assertEquals(3, completeSource.getRho());

		Substitution partialRho = new Substitution();
		partialRho.addReplace(first, second);
		LuVariable partialSource = new LuVariable(first, 3);

		assertSame(partialSource, partialSource.applyRho(partialRho));
		assertSame(second, partialSource.getVariable());
		assertEquals(2, partialSource.getRho());
	}

	@Test
	@DisplayName("complete rho up to the right-hand term")
	void completeRhoUpToRightHandTerm() {
		Variable first = new Variable();
		Variable second = new Variable();
		Variable right = new Variable();
		Substitution rho = new Substitution();
		rho.addReplace(first, second);
		LuVariable source = new LuVariable(first, 3);

		source.completeRho(rho, right);

		Variable third = (Variable) rho.get(second);
		assertSame(second, rho.get(first));
		assertSame(third, rho.get(second));
		assertSame(right, rho.get(third));
	}
}
