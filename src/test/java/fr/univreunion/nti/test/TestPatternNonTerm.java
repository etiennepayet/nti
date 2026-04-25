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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
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
import fr.univreunion.nti.program.trs.nonloop.iclp25.PatternRuleTrsIclp25;
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
			LinkedList<String> s = new LinkedList<>();
			s.add("while(s(X),s(Y)){X->s(X),Y->s(Y)}{X->s(X),Y->0}");
			s.add("while(s(s(X)),s(s(Y))){X->s(s(X)),Y->s(Y)}{X->s(X),Y->0}");
			s.add("f(g(s(X),h(h(Y))),s(X),h(h(h(Y)))){X->s(X),Y->h(h(Y))}{X->s(X1),Y->h(0)}");
			s.add("while(X,Y){X->s(X),Y->s(Y)}{X->s(X1),Y->0}");
			s.add("while(Z,s(Y)){Z->s(s(Z)),Y->s(Y)}{Z->s(X1),Y->0}");

			// The pattern terms constructed from the strings.
			LinkedList<SimplePatternTerm> l = new LinkedList<>();
			for (String p_string : s) 
				l.add(parser.parseSimplePatternTerm(p_string, variables));

			// The string corresponding to each variable (for display purposes).
			Map<Variable, String> variables_reversed = reverse(variables);
			for(SimplePatternTerm p : l) {
				logger.info("theta = " + p.getPatternSubs().getTheta().toString(variables_reversed));
				logger.info("base = " + p.getBaseTerm().toString(variables_reversed, false));
				logger.info("upsilon = " + p.getUpsilon().toString(variables_reversed, false));
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
	 * @throws Exception
	 */
	void checkNonTerm(String left, String right, Logger logger, String msg) throws Exception {
		
		logger.info(msg);
		
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		SimplePatternTerm p = parser.parseSimplePatternTerm(left, variables);
		SimplePatternTerm q = parser.parseSimplePatternTerm(right, variables);

		PatternRuleTrsIclp25 r = PatternRuleTrsIclp25.getInstance(p, q, 0);

		// The string corresponding to each variable (for display purposes).
		Map<Variable, String> variables_reversed = reverse(variables);

		Function nonterm = r.getNonTerminatingTerm();
		assertTrue(nonterm != null, "Aborting test: 'nonterm' is null");

		logger.info("Computed alpha: " + r.getAlpha());
		logger.info("Computed nonterminating term: " + nonterm.toString(variables_reversed, false));
	}
	 
	/**
	 * Reverses the provided collection of mappings.
	 * 
	 * @param m a map to reverse
	 * @return the result of reversing <code>m</code>
	 */
	Map<Variable, String> reverse(Map<String, Variable> m) {
		Map<Variable, String> result = new HashMap<>();
		for (Map.Entry<String, Variable> e : m.entrySet())
			result.put(e.getValue(), e.getKey());
		return result;
	}
}
