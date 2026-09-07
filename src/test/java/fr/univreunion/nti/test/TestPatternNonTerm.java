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

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;
import java.util.logging.Logger;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class TestPatternNonTerm {

	@Test
	@DisplayName("test simple pattern term")
	void testSimplePatternTerm() {

		Logger logger = Logger.getLogger("TestPatternNonTerm");

		logger.info("===== test simple pattern term =====");

		try {
			ParserString parser = new ParserString();
			Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

			// The pattern terms in string format.
			LinkedList<String> patternTermTexts = new LinkedList<>();
			patternTermTexts.add("while(s(X),s(Y)){X->s(X),Y->s(Y)}{X->s(X),Y->0}");
			patternTermTexts.add("while(s(s(X)),s(s(Y))){X->s(s(X)),Y->s(Y)}{X->s(X),Y->0}");
			patternTermTexts.add("f(g(s(X),h(h(Y))),s(X),h(h(h(Y)))){X->s(X),Y->h(h(Y))}{X->s(X1),Y->h(0)}");
			patternTermTexts.add("while(X,Y){X->s(X),Y->s(Y)}{X->s(X1),Y->0}");
			patternTermTexts.add("while(Z,s(Y)){Z->s(s(Z)),Y->s(Y)}{Z->s(X1),Y->0}");

			// The pattern terms constructed from the strings.
			LinkedList<SimplePatternTerm> patternTerms = new LinkedList<>();
			for (String patternTermText : patternTermTexts)
				patternTerms.add(parser.parseSimplePatternTerm(patternTermText, variables));

			// The string corresponding to each variable (for display purposes).
			Map<Variable, String> variableNames = reverse(variables);
			for (SimplePatternTerm patternTerm : patternTerms) {
				logger.info("theta = " +
						patternTerm.getPatternSubstitution().getHatFunctionSubstitution().toString(variableNames));
				logger.info("base = " + patternTerm.getBaseTerm().toString(variableNames, false));
				logger.info("upsilon = " + patternTerm.getUpsilon().toString(variableNames, false));
			}
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern nontermination 1")
	void testPatternNonTerm1() {
		// This is Ex. 7 of [Payet, LOPSTR'25].

		Logger logger = Logger.getLogger("TestPatternNonTerm");

		try {
			String left = "while(s(X),s(Y)){X->s(X),Y->s(Y)}{X->s(X),Y->0}";
			String right = "while(s(s(X)),s(s(Y))){X->s(s(X)),Y->s(Y)}{X->s(X),Y->0}";

			checkNonTerm(left, right, logger, "===== test pattern nontermination 1 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern nontermination 2")
	void testPatternNonTerm2() {

		Logger logger = Logger.getLogger("TestPatternNonTerm");

		try {
			String left = "while(X,Y){X->s(X),Y->s(Y)}{X->s(X1),Y->0}";
			String right = "while(Z,s(Y)){Z->s(s(Z)),Y->s(Y)}{Z->s(X1),Y->0}";

			checkNonTerm(left, right, logger, "===== test pattern nontermination 2 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern nontermination 3")
	void testPatternNonTerm3() {
		// This is while.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternNonTerm");

		try {
			String left = "while(X,Y){X->s(X),Y->s(Y)}{X->s(X1),Y->0}";
			String right = "while(s(X),s(Y)){X->s(X),Y->s(Y)}{X->s(X1),Y->0}";

			checkNonTerm(left, right, logger, "===== test pattern nontermination 3 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern nontermination 4")
	void testPatternNonTerm4() {
		// This one is for testing the form (NT1).

		Logger logger = Logger.getLogger("TestPatternNonTerm");

		try {
			String left = "while(X,s(Y)){X->s(X),Y->s(Y)}{X->s(s(X)),Y->s(Y)}";
			String right = "while(s(X),Y){X->s(s(X)),Y->s(s(Y))}{Y->s(Z)}";

			checkNonTerm(left, right, logger, "===== test pattern nontermination 4 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern nontermination 5")
	void testPatternNonTerm5() {
		// This one is for testing the form (NT1).

		Logger logger = Logger.getLogger("TestPatternNonTerm");

		try {
			String left = "while(X,s(Y)){X->s(X),Y->s(Y)}{X->s(s(X)),Y->s(Y)}";
			String right = "while(s(s(X)),s(Y)){X->s(X),Y->s(Y)}{X->Z,Y->s(Y)}";

			checkNonTerm(left, right, logger, "===== test pattern nontermination 5 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern nontermination 6")
	void testPatternNonTerm6() {

		Logger logger = Logger.getLogger("TestPatternNonTerm");

		try {
			String left  = "while(true,X,Y){X->s(X)}{X->s(X),Y->s(Y)}{X->s(0),Y->0}";
			String right = "while(true,X,Y){X->s(X)}{X->s(X),Y->s(Y)}{X->s(s(s(0))),Y->s(0)}";

			checkNonTerm(left, right, logger, "===== test pattern nontermination 6 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	/**
	 * Checks whether the rule <code>(left, right)</code>
	 * is a nontermination witness.
	 *
	 * @param left the left-hand side of the rule
	 * @param right the right-hand side of the rule
	 * @param logger a logger to display messages
	 * @param introductoryMessage an introductory message to display
	 * @throws Exception
	 */
	void checkNonTerm(String left, String right, Logger logger, String introductoryMessage) throws Exception {

		logger.info(introductoryMessage);

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		SimplePatternTerm leftPattern = parser.parseSimplePatternTerm(left, variables);
		SimplePatternTerm rightPattern = parser.parseSimplePatternTerm(right, variables);

		PatternRuleTrs rule = PatternRuleTrs.tryBuild(leftPattern, rightPattern, 0);

		// The string corresponding to each variable (for display purposes).
		Map<Variable, String> variableNames = reverse(variables);

		Function nonterm = rule.getNonTerminatingTerm();
		assertNotNull(nonterm, "Aborting test: 'nonterm' is null");

		logger.info("Rule: " + rule.toString(variableNames));
		logger.info("Computed alpha: " + rule.getAlpha());
		logger.info("Computed nonterminating term: " + nonterm.toString(variableNames, false));
	}

	/**
	 * Reverses the provided collection of mappings.
	 *
	 * @param variables a map to reverse
	 * @return the result of reversing <code>variables</code>
	 */
	Map<Variable, String> reverse(Map<String, Variable> variables) {
		Map<Variable, String> result = new HashMap<>();
		for (Map.Entry<String, Variable> entry : variables.entrySet())
			result.put(entry.getValue(), entry.getKey());
		return result;
	}
}
