/*
 * Copyright 2025 Etienne Payet <etienne.payet at univ-reunion.fr>
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

package fr.univreunion.nti.test;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;

class TestSimplePatternSubstitution {

	@Test
	@DisplayName("build simple pattern substitution from pumping and closing substitutions")
	void buildFromPumpingAndClosingSubstitutions() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		Substitution pumping = parser.parseSubstitution("{X->s(X),Y->Y}", variables);
		Substitution closing = parser.parseSubstitution("{X->s(s(0)),Y->f(0)}", variables);

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(List.of(pumping, closing));

		assertNotNull(patternSubstitution);
		assertEquals(1, patternSubstitution.getArity());
		assertImageEquals(
				hatFunction(parser, variables, "s(X)", "X", "0", 1, 2),
				patternSubstitution.getHatFunctionSubstitution(),
				variables.get("X"));
		assertImageEquals(
				parser.parseTerm("f(0)", variables),
				patternSubstitution.getHatFunctionSubstitution(),
				variables.get("Y"));
	}

	@Test
	@DisplayName("recover pumping and closing substitutions from hat-function substitution")
	void recoverPumpingAndClosingSubstitutionsFromHatFunctionSubstitution()
			throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		Variable x = variable(parser, variables, "X");
		Variable y = variable(parser, variables, "Y");
		Substitution theta = new Substitution();
		theta.add(x, hatFunction(parser, variables, "s(X)", "X", "0", 1, 2));
		theta.add(y, parser.parseTerm("f(0)", variables));

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(theta);

		assertNotNull(patternSubstitution);
		assertEquals(1, patternSubstitution.getArity());
		assertImageEquals(parser.parseTerm("s(X)", variables), patternSubstitution.getPumping(), x);
		assertImageEquals(parser.parseTerm("s(s(0))", variables), patternSubstitution.getClosing(), x);
		assertImageEquals(parser.parseTerm("f(0)", variables), patternSubstitution.getClosing(), y);
	}

	@Test
	@DisplayName("recover substitutions from plain substitution without hat functions")
	void recoverPlainSubstitutionWithoutHatFunctions() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		Variable x = variable(parser, variables, "X");
		Substitution theta = new Substitution();
		theta.add(x, parser.parseTerm("f(Y)", variables));

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(theta);

		assertNotNull(patternSubstitution);
		assertEquals(1, patternSubstitution.getArity());
		assertTrue(patternSubstitution.getPumping().isEmpty());
		assertImageEquals(parser.parseTerm("f(Y)", variables), patternSubstitution.getClosing(), x);
		assertImageEquals(
				parser.parseTerm("f(Y)", variables),
				patternSubstitution.getHatFunctionSubstitution(),
				x);
	}

	@Test
	@DisplayName("reject hat-function substitution with nested hat function")
	void rejectNestedHatFunctionImage() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		Variable x = variable(parser, variables, "X");
		Term innerHatFunction = hatFunction(parser, variables, "s(X)", "X", "0", 1, 0);
		Substitution theta = new Substitution();
		theta.add(x, hatFunction(parser, variables, "s(X)", "X", innerHatFunction, 1, 0));

		assertNull(SimplePatternSubstitution.tryBuild(theta));
	}

	@Test
	@DisplayName("reject pumping substitutions with incompatible contexts")
	void rejectIncompatiblePumpingContexts() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		Substitution firstPumping = parser.parseSubstitution("{X->s(X)}", variables);
		Substitution secondPumping = parser.parseSubstitution("{X->h(X)}", variables);
		Substitution closing = parser.parseSubstitution("{X->0}", variables);

		assertNull(SimplePatternSubstitution.tryBuild(
				List.of(firstPumping, secondPumping, closing)));
	}

	private static Variable variable(
			ParserString parser,
			Map<String, Variable> variables,
			String name) throws IOException {

		parser.parseTerm(name, variables);
		return variables.get(name);
	}

	private static HatFunction hatFunction(
			ParserString parser,
			Map<String, Variable> variables,
			String contextText,
			String contextVariableName,
			String argumentText,
			int... exponents) throws IOException {

		return hatFunction(
				parser,
				variables,
				contextText,
				contextVariableName,
				parser.parseTerm(argumentText, variables),
				exponents);
	}

	private static HatFunction hatFunction(
			ParserString parser,
			Map<String, Variable> variables,
			String contextText,
			String contextVariableName,
			Term argument,
			int... exponents) throws IOException {

		Term context = parser.parseTerm(contextText, variables);
		Variable contextVariable = variables.get(contextVariableName);
		HatFunctionSymbol hatSymbol = HatFunctionSymbol.intern(context, contextVariable);

		return new HatFunction(hatSymbol, argument, exponentList(exponents));
	}

	private static List<Integer> exponentList(int... exponents) {
		List<Integer> exponentList = new ArrayList<>();
		for (int exponent : exponents)
			exponentList.add(exponent);

		return exponentList;
	}

	private static void assertImageEquals(
			Term expectedImage,
			Substitution substitution,
			Variable variable) {

		Term actualImage = substitution.getOrDefault(variable, variable);
		assertTrue(expectedImage.deepEquals(actualImage),
				"Expected image " + expectedImage + " but got " + actualImage);
	}
}
