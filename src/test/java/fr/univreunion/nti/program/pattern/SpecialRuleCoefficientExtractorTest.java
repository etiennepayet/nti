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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

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

class SpecialRuleCoefficientExtractorTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void extractsVariableAndGroundCoefficients() throws IOException {
		Substitution left = substitution(
				"X", hatFunction("s(H)", "H", "U", 1, 1),
				"Y", hatFunction("s(H)", "H", "0", 1, 0));
		Substitution right = substitution(
				"X", hatFunction("s(H)", "H", "U", 2, 1),
				"Y", hatFunction("s(H)", "H", "0", 1, 1));

		assertEquals(
				new SpecialRuleCoefficients(1, 2, 0, 1, 1, 1, 1),
				SpecialRuleCoefficientExtractor.extract(left, right));
	}

	@Test
	void extractsVariableOnlyCoefficients() throws IOException {
		Substitution left = substitution(
				"X", hatFunction("s(H)", "H", "U", 1, 1));
		Substitution right = substitution(
				"X", hatFunction("s(H)", "H", "U", 2, 1));

		assertEquals(
				new SpecialRuleCoefficients(1, 2, -1, -1, 1, 1, 0),
				SpecialRuleCoefficientExtractor.extract(left, right));
	}

	@Test
	void extractsGroundOnlyCoefficients() throws IOException {
		Substitution left = substitution(
				"X", hatFunction("s(H)", "H", "0", 1, 0));
		Substitution right = substitution(
				"X", hatFunction("s(H)", "H", "0", 1, 2));

		assertEquals(
				new SpecialRuleCoefficients(-1, -1, 0, 2, -1, -1, 2),
				SpecialRuleCoefficientExtractor.extract(left, right));
	}

	@Test
	void rejectsDifferentContexts() throws IOException {
		assertRejected(
				hatFunction("s(H)", "H", "U", 1, 0),
				hatFunction("t(H)", "H", "U", 1, 0));
	}

	@Test
	void rejectsWhenLeftEmbeddedTermIsNotMoreGeneral() throws IOException {
		assertRejected(
				hatFunction("s(H)", "H", "0", 1, 0),
				hatFunction("s(H)", "H", "U", 1, 0));
	}

	@Test
	void rejectsDecreasingVariableExponent() throws IOException {
		assertRejected(
				hatFunction("s(H)", "H", "U", 2, 0),
				hatFunction("s(H)", "H", "U", 1, 0));
	}

	@Test
	void rejectsIncompatibleGroundExponents() throws IOException {
		assertRejected(
				hatFunction("s(H)", "H", "0", 1, 1),
				hatFunction("s(H)", "H", "0", 2, 0));
	}

	@Test
	void rejectsDifferentContextsForSameEmbeddedVariable() throws IOException {
		Substitution left = substitution(
				"X", hatFunction("s(H)", "H", "U", 1, 0),
				"Y", hatFunction("t(H)", "H", "U", 1, 0));
		Substitution right = substitution(
				"X", hatFunction("s(H)", "H", "U", 1, 0),
				"Y", hatFunction("t(H)", "H", "U", 1, 0));

		assertNull(SpecialRuleCoefficientExtractor.extract(left, right));
	}

	private void assertRejected(Term leftImage, Term rightImage) throws IOException {
		assertNull(SpecialRuleCoefficientExtractor.extract(
				substitution("X", leftImage),
				substitution("X", rightImage)));
	}

	private Substitution substitution(String variableName, Term image) throws IOException {
		Substitution substitution = new Substitution();
		substitution.addReplace(variable(variableName), image);
		return substitution;
	}

	private Substitution substitution(
			String firstVariableName,
			Term firstImage,
			String secondVariableName,
			Term secondImage) throws IOException {

		Substitution substitution = substitution(firstVariableName, firstImage);
		substitution.addReplace(variable(secondVariableName), secondImage);
		return substitution;
	}

	private Variable variable(String name) throws IOException {
		parser.parseTerm(name, variables);
		return variables.get(name);
	}

	private HatFunction hatFunction(
			String contextText,
			String contextVariableName,
			String argumentText,
			int... exponents) throws IOException {

		Term context = parser.parseTerm(contextText, variables);
		Variable contextVariable = variables.get(contextVariableName);
		Term argument = parser.parseTerm(argumentText, variables);
		HatFunctionSymbol symbol = HatFunctionSymbol.intern(context, contextVariable);
		List<Integer> exponentList = new ArrayList<>();
		for (int exponent : exponents)
			exponentList.add(exponent);

		return new HatFunction(symbol, argument, exponentList);
	}
}
