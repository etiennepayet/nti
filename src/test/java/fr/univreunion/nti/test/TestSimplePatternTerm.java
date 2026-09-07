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
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class TestSimplePatternTerm {

	@Test
	@DisplayName("compute weakening index from ordinary function disagreement")
	void computeFunctionWeakeningIndexFromOrdinaryFunctionDisagreement()
			throws IOException {

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		SimplePatternTerm left = parsePatternTerm(
				parser,
				variables,
				"gt(X,Y){X->s(X),Y->s(Y)}{X->s(X),Y->0}");
		SimplePatternTerm patternTerm = parsePatternTerm(
				parser,
				variables,
				"gt(X1,Y1){X1->s(X1)}{X1->s(0),Y1->0}");

		SimplePatternTerm.WeakeningIndexes weakeningIndexes =
				left.computeWeakeningIndexes(patternTerm);

		assertNotNull(weakeningIndexes);
		assertEquals(0, weakeningIndexes.functionWeakeningIndex());
		assertEquals(-1, weakeningIndexes.hatWeakeningIndex());
	}

	@Test
	@DisplayName("compute hat weakening index and build weakened substitutions")
	void computeHatWeakeningIndexAndBuildSubstitutions() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		SimplePatternTerm left = parsePatternTerm(
				parser,
				variables,
				"add(X,Y,Z){Y->s(Y),Z->s(Z)}{X->X2,Y->0,Z->X2}");
		SimplePatternTerm patternTerm = parsePatternTerm(
				parser,
				variables,
				"add(X,Y,Z){X->s(X),Y->s(Y)}{X->s(X1),Y->s(X1)}");

		SimplePatternTerm.WeakeningIndexes weakeningIndexes =
				left.computeWeakeningIndexes(patternTerm);

		assertNotNull(weakeningIndexes);
		assertEquals(-1, weakeningIndexes.functionWeakeningIndex());
		assertEquals(1, weakeningIndexes.hatWeakeningIndex());

		SimplePatternTerm.WeakeningSubstitutions weakeningSubstitutions =
				left.buildWeakeningSubstitutions(
						weakeningIndexes.hatWeakeningIndex());
		Map<Variable, String> variableNames = reverse(variables);

		assertEquals(
				"add(X2,hat[s(□)]^[1, 1](0),hat[s(□)]^[1, 1](X2))",
				applyToBaseTerm(left, weakeningSubstitutions.first(), variableNames));
		assertEquals(
				"add(X2,hat[s(□)]^[1, 1, 1](0),hat[s(□)]^[1, 1, 1](X2))",
				applyToBaseTerm(left, weakeningSubstitutions.second(), variableNames));
	}

	@Test
	@DisplayName("unify fact keeps weakened unifiers in generated order")
	void unifyFactKeepsWeakenedUnifiersInGeneratedOrder() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();

		SimplePatternTerm patternTerm = parsePatternTerm(
				parser,
				variables,
				"add(X,Y,Z){X->s(X),Y->s(Y)}{X->s(X1),Y->s(X1)}");
		SimplePatternTerm factLeft = parsePatternTerm(
				parser,
				variables,
				"add(X,Y,Z){Y->s(Y),Z->s(Z)}{X->X2,Y->0,Z->X2}");
		PatternRuleLp fact = PatternRuleLp.tryBuildFact(factLeft, 0);

		Collection<PatternSubstitution> unifiers =
				patternTerm.unifyWith(fact);

		List<SimplePatternSubstitution> orderedUnifiers =
				unifiers.stream()
						.map(SimplePatternSubstitution.class::cast)
						.toList();
		assertEquals(2, orderedUnifiers.size());

		Map<Variable, String> variableNames = reverse(variables);
		assertImageEquals("0", orderedUnifiers.get(0), variables.get("X1"), variableNames);
		assertImageEquals(
				"hat[s(□)]^[1, 1](0)",
				orderedUnifiers.get(0),
				variables.get("X2"),
				variableNames);
		assertImageEquals(
				"hat[s(□)]^[2, 2](0)",
				orderedUnifiers.get(0),
				variables.get("Z"),
				variableNames);

		assertImageEquals(
				"hat[s(□)]^[1, 0, 0](0)",
				orderedUnifiers.get(1),
				variables.get("X1"),
				variableNames);
		assertImageEquals(
				"hat[s(□)]^[1, 1, 1](0)",
				orderedUnifiers.get(1),
				variables.get("X2"),
				variableNames);
		assertImageEquals(
				"hat[s(□)]^[2, 2, 2](0)",
				orderedUnifiers.get(1),
				variables.get("Z"),
				variableNames);
	}

	private static SimplePatternTerm parsePatternTerm(
			ParserString parser,
			Map<String, Variable> variables,
			String input) throws IOException {

		return parser.parseSimplePatternTerm(input, variables);
	}

	private static String applyToBaseTerm(
			SimplePatternTerm patternTerm,
			Substitution substitution,
			Map<Variable, String> variableNames) {

		return patternTerm.getBaseTerm().apply(substitution).toString(
				variableNames, false);
	}

	private static void assertImageEquals(
			String expectedImage,
			SimplePatternSubstitution patternSubstitution,
			Variable variable,
			Map<Variable, String> variableNames) {

		Term actualImage =
				patternSubstitution.getHatFunctionSubstitution().getOrDefault(
						variable, variable);
		assertEquals(expectedImage, actualImage.toString(variableNames, false));
	}

	private static Map<Variable, String> reverse(Map<String, Variable> variables) {
		Map<Variable, String> result = new HashMap<>();
		for (Map.Entry<String, Variable> entry : variables.entrySet())
			result.put(entry.getValue(), entry.getKey());

		return result;
	}
}
