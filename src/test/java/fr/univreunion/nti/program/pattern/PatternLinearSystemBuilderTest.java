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

package fr.univreunion.nti.program.pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;

class PatternLinearSystemBuilderTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void rejectsDifferentContexts() throws IOException {
		Variable variable = variable("X");
		Substitution left = substitution(variable, hatFunction("s(H)", "H", "0", 1, 0));
		Substitution right = substitution(variable, hatFunction("t(H)", "H", "0", 1, 0));

		assertNull(PatternLinearSystemBuilder.tryBuild(left, right));
	}

	@Test
	void rejectsNonGroundEmbeddedTerms() throws IOException {
		Variable variable = variable("X");
		Substitution left = substitution(variable, hatFunction("s(H)", "H", variable, 1, 0));
		Substitution right = substitution(variable, hatFunction("s(H)", "H", variable, 1, 0));

		assertNull(PatternLinearSystemBuilder.tryBuild(left, right));
	}

	@Test
	void rejectsDifferentGroundEmbeddedTerms() throws IOException {
		Variable variable = variable("X");
		Substitution left = substitution(variable, hatFunction("s(H)", "H", "0", 1, 0));
		Substitution right = substitution(variable, hatFunction("s(H)", "H", "s(0)", 1, 0));

		assertNull(PatternLinearSystemBuilder.tryBuild(left, right));
	}

	@Test
	void omitsMappingsWithoutHatFunctions() throws IOException {
		Variable variable = variable("X");
		Term groundTerm = parser.parseTerm("0", variables);

		LinearSystem system = PatternLinearSystemBuilder.tryBuild(
				substitution(variable, groundTerm),
				substitution(variable, groundTerm));

		assertNotNull(system);
		assertEquals("n = 0, m = 0\n", system.toString());
		assertTrue(system.solve());
	}

	@Test
	void preservesExponentOrderAndPadsMissingCoefficients() throws IOException {
		Variable variable = variable("X");
		Substitution left = substitution(variable, hatFunction("s(H)", "H", "0", 1, 2));
		Substitution right = substitution(variable, hatFunction("s(H)", "H", "0", 3, 4, 5));

		LinearSystem system = PatternLinearSystemBuilder.tryBuild(left, right);

		assertNotNull(system);
		assertEquals("n = 1, m = 2\n0 1 = 3 4 3 \n", system.toString());
	}

	private Variable variable(String name) throws IOException {
		parser.parseTerm(name, variables);
		return variables.get(name);
	}

	private Substitution substitution(Variable variable, Term image) {
		Substitution substitution = new Substitution();
		substitution.addReplace(variable, image);
		return substitution;
	}

	private HatFunction hatFunction(
			String contextText,
			String contextVariableName,
			String argumentText,
			int... exponents) throws IOException {

		return hatFunction(
				contextText,
				contextVariableName,
				parser.parseTerm(argumentText, variables),
				exponents);
	}

	private HatFunction hatFunction(
			String contextText,
			String contextVariableName,
			Term argument,
			int... exponents) throws IOException {

		Term context = parser.parseTerm(contextText, variables);
		Variable contextVariable = variables.get(contextVariableName);
		HatFunctionSymbol symbol = HatFunctionSymbol.intern(context, contextVariable);
		List<Integer> exponentList = new ArrayList<>();
		for (int exponent : exponents)
			exponentList.add(exponent);

		return new HatFunction(symbol, argument, exponentList);
	}
}
