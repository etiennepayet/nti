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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class PatternNonTerminationAnalyzerTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void rejectsFactWithoutRightSide() throws IOException {
		SimplePatternTerm left =
				SimplePatternTerm.of(parser.parseTerm("p(X)", variables));

		PatternNonTerminationAnalysis analysis =
				PatternNonTerminationAnalyzer.analyze(left, null);

		assertNull(analysis.nonTerminatingTerm());
		assertEquals(-1, analysis.alpha());
	}

	@Test
	void succeedsDirectlyWithSpecialRuleCoefficients() throws IOException {
		Variable variable = variable("X");
		SimplePatternTerm left = patternTerm(
				variable, hatFunction("s(H)", "H", "0", 1, 0));
		SimplePatternTerm right = patternTerm(
				variable, hatFunction("s(H)", "H", "0", 1, 2));
		assertNotNull(SpecialRuleCoefficientExtractor.extract(
				left.getPatternSubstitution().getHatFunctionSubstitution(),
				right.getPatternSubstitution().getHatFunctionSubstitution()));

		PatternNonTerminationAnalysis analysis =
				PatternNonTerminationAnalyzer.analyze(left, right);

		assertNotNull(analysis.nonTerminatingTerm());
		assertEquals(0, analysis.alpha());
		assertEquals("p(0)", analysis.nonTerminatingTerm().toString());
	}

	@Test
	void succeedsThroughLinearSystemFallback() throws IOException {
		Variable x = variable("X");
		Variable y = variable("Y");
		Substitution leftSubstitution = new Substitution();
		leftSubstitution.addReplace(
				x, hatFunction("s(H)", "H", "0", 0, 1, 0));
		leftSubstitution.addReplace(
				y, hatFunction("s(H)", "H", "0", 2, 0, 0));
		Substitution rightSubstitution = new Substitution(leftSubstitution);
		Function base = (Function) parser.parseTerm("p(X,Y)", variables);
		SimplePatternTerm left = patternTerm(base, leftSubstitution);
		SimplePatternTerm right = patternTerm(base, rightSubstitution);
		assertNull(SpecialRuleCoefficientExtractor.extract(
				left.getPatternSubstitution().getHatFunctionSubstitution(),
				right.getPatternSubstitution().getHatFunctionSubstitution()));
		assertNotNull(PatternLinearSystemBuilder.tryBuild(
				left.getPatternSubstitution().getHatFunctionSubstitution(),
				right.getPatternSubstitution().getHatFunctionSubstitution()));

		PatternNonTerminationAnalysis analysis =
				PatternNonTerminationAnalyzer.analyze(left, right);

		assertNotNull(analysis.nonTerminatingTerm());
		assertEquals(0, analysis.alpha());
		assertEquals("p(0,0)", analysis.nonTerminatingTerm().toString());
	}

	@Test
	void succeedsAfterRefactoringAndBuildsOriginalLeftWitness() throws IOException {
		SimplePatternTerm left =
				SimplePatternTerm.of(parser.parseTerm("p(X)", variables));
		SimplePatternTerm right =
				SimplePatternTerm.of(parser.parseTerm("p(s(X))", variables));

		PatternNonTerminationAnalysis analysis =
				PatternNonTerminationAnalyzer.analyze(left, right);

		assertNotNull(analysis.nonTerminatingTerm());
		assertEquals(0, analysis.alpha());
		assertEquals("p(0)", analysis.nonTerminatingTerm().toString());
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

	private void assertRejected(Term leftImage, Term rightImage) throws IOException {
		Variable variable = variable("X");
		PatternNonTerminationAnalysis analysis = PatternNonTerminationAnalyzer.analyze(
				patternTerm(variable, leftImage),
				patternTerm(variable, rightImage));

		assertNull(analysis.nonTerminatingTerm());
		assertEquals(-1, analysis.alpha());
	}

	private SimplePatternTerm patternTerm(Variable variable, Term image) throws IOException {
		Function base = (Function) parser.parseTerm("p(X)", variables);
		Substitution substitution = new Substitution();
		substitution.addReplace(variable, image);
		return patternTerm(base, substitution);
	}

	private SimplePatternTerm patternTerm(Function base, Substitution substitution) {
		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(substitution);
		return SimplePatternTerm.tryBuild(base, patternSubstitution);
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
