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
import java.util.HashMap;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class TestPatternRuleLp {

	@Test
	@DisplayName("reject missing left-hand side or negative iteration")
	void rejectMissingLeftHandSideOrNegativeIteration() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		SimplePatternTerm patternTerm = parser.parseSimplePatternTerm(
				"p(X){}{}",
				variables);

		assertNull(PatternRuleLp.tryBuild(null, patternTerm, 0));
		assertNull(PatternRuleLp.tryBuild(patternTerm, patternTerm, -1));
		assertNull(PatternRuleLp.tryBuildFact(null, 0));
		assertNull(PatternRuleLp.tryBuildFact(patternTerm, -1));
	}

	@Test
	@DisplayName("reject non-simple pattern substitutions")
	void rejectNonSimplePatternSubstitutions() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		Function atom = (Function) parser.parseTerm("p(X)", variables);
		PatternSubstitution nonSimpleSubstitution =
				new NonSimplePatternSubstitution();

		assertNull(PatternRuleLp.tryBuild(
				atom,
				nonSimpleSubstitution,
				atom,
				SimplePatternSubstitution.empty(),
				0));
		assertNull(PatternRuleLp.tryBuild(
				atom,
				SimplePatternSubstitution.empty(),
				atom,
				nonSimpleSubstitution,
				0));
		assertNull(PatternRuleLp.tryBuildFact(
				atom,
				nonSimpleSubstitution,
				0));
	}

	@Test
	@DisplayName("format regular pattern rule")
	void formatRegularPatternRule() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		SimplePatternTerm left = parser.parseSimplePatternTerm(
				"p(X){}{}",
				variables);
		SimplePatternTerm right = parser.parseSimplePatternTerm(
				"q(X){}{}",
				variables);
		PatternRuleLp patternRule = PatternRuleLp.tryBuild(left, right, 0);

		assertEquals(-1, patternRule.getAlpha());
		assertNull(patternRule.getNonTerminatingTerm());
		assertEquals(
				"p(X) :- q(X)",
				patternRule.toString(reverse(variables)));
	}

	@Test
	@DisplayName("format pattern fact")
	void formatPatternFact() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		SimplePatternTerm left = parser.parseSimplePatternTerm(
				"p(X){}{}",
				variables);
		PatternRuleLp patternRule = PatternRuleLp.tryBuildFact(left, 0);

		assertEquals(-1, patternRule.getAlpha());
		assertNull(patternRule.getNonTerminatingTerm());
		assertEquals(
				"p(X) :- e*",
				patternRule.toString(reverse(variables)));
	}

	@Test
	@DisplayName("format special pattern rule")
	void formatSpecialPatternRule() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		SimplePatternTerm left = parser.parseSimplePatternTerm(
				"while(X,Y){X->s(X),Y->s(Y)}{X->s(X1),Y->0}",
				variables);
		SimplePatternTerm right = parser.parseSimplePatternTerm(
				"while(s(X),s(Y)){X->s(X),Y->s(Y)}{X->s(X1),Y->0}",
				variables);
		PatternRuleLp patternRule = PatternRuleLp.tryBuild(left, right, 0);

		assertEquals(0, patternRule.getAlpha());
		assertEquals("while(s(0),0)", patternRule.getNonTerminatingTerm().toString());
		assertEquals(
				"Pattern rule R = while(hat[s(□)]^[1, 1](X1),hat[s(□)]^[1, 0](0))" +
				" :- while(hat[s(□)]^[1, 2](X1),hat[s(□)]^[1, 1](0))" +
				" (R is special with 𝛼(R) = 0 and p(𝛼(R))𝛳 = while(s(0),0)" +
				" where 𝛳 maps all variables to the constant 0, see Def. 14 + Thm. 5 of [Payet, ICLP'25])",
				patternRule.toString(reverse(variables)));
	}

	@Test
	@DisplayName("compute positive alpha and corresponding nonterminating term")
	void computePositiveAlphaAndNonTerminatingTerm() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		SimplePatternTerm left = parser.parseSimplePatternTerm(
				"while(X,Y){X->s(X),Y->s(Y)}{X->s(X1),Y->0}",
				variables);
		SimplePatternTerm right = parser.parseSimplePatternTerm(
				"while(Z,s(Y)){Z->s(s(Z)),Y->s(Y)}{Z->s(X1),Y->0}",
				variables);
		PatternRuleLp patternRule = PatternRuleLp.tryBuild(left, right, 0);

		assertEquals(1, patternRule.getAlpha());
		assertEquals("while(s(s(0)),s(0))", patternRule.getNonTerminatingTerm().toString());
	}

	private static final class NonSimplePatternSubstitution
			extends PatternSubstitution {

		@Override
		public PatternSubstitution composeWith(
				PatternSubstitution otherPatternSubstitution) {

			return null;
		}

		@Override
		public PatternSubstitution deepCopy() {
			return this;
		}

		@Override
		public PatternSubstitution deepCopy(Map<Term, Term> copies) {
			return this;
		}

		@Override
		public String toString(Map<Variable, String> variables) {
			return "{}{}";
		}
	}

	private static Map<Variable, String> reverse(Map<String, Variable> variables) {
		Map<Variable, String> result = new HashMap<>();
		for (Map.Entry<String, Variable> entry : variables.entrySet())
			result.put(entry.getValue(), entry.getKey());

		return result;
	}
}
