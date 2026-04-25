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

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.logging.Logger;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.lp.Lp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.lp.nonloop.PatternRuleLp;
import fr.univreunion.nti.term.Variable;

class TestPatternUnfoldingLp {
	
	@Test
	@DisplayName("test pattern unfolding 1")
	void testPatternUnfold01() {
		// This is the running example of ICLP'25.
		
		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("while(X,Y) :- gt(X,Y), add(X,Y,Z), while(Z,s(Y)).");
			rules.add("gt(s(X),0).");
			rules.add("gt(s(X),s(Y)) :- gt(X,Y).");
			rules.add("add(X,0,X).");
			rules.add("add(X,s(Y),s(Z)) :- add(X,Y,Z).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 1 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 2")
	void testPatternUnfold02() {

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("while(X,Y) :- gt(X,Y), add(X,s(0),Z), while(Z,s(Y)).");
			rules.add("gt(s(X),0).");
			rules.add("gt(s(X),s(Y)) :- gt(X,Y).");
			rules.add("add(X,0,X).");
			rules.add("add(X,s(Y),s(Z)) :- add(X,Y,Z).");

			unfoldLP(rules, logger, "===== test pattern unfolding 2 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 3")
	void testPatternUnfold03() {
		// This is while-add-4.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("while(X,Y) :- gt(X,Y), add(X,X,Z), while(Z,s(Y)).");
			rules.add("gt(s(X),0).");
			rules.add("gt(s(X),s(Y)) :- gt(X,Y).");
			rules.add("add(X,0,X).");
			rules.add("add(X,s(Y),s(Z)) :- add(X,Y,Z).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 3 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 4")
	void testPatternUnfold04() {
		// This is while-dbl-2.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("while(X,Y) :- gt(X,Y), dbl(X,Z), while(Z,s(Y)).");
			rules.add("gt(s(X),0).");
			rules.add("gt(s(X),s(Y)) :- gt(X,Y).");
			rules.add("dbl(0,0).");
			rules.add("dbl(s(X),s(s(Y))) :- dbl(X,Y).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 4 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 5")
	void testPatternUnfold05() {
		// This is while-times-1.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("while(X,Y) :- gt(X,Y), times(X,s(s(0)),Z), while(Z,s(Y)).");
			rules.add("gt(s(X),0).");
			rules.add("gt(s(X),s(Y)) :- gt(X,Y).");
			rules.add("times(0,X,0).");
			rules.add("times(s(X),Y,Z) :- times(X,Y,A), add(Y,A,Z).");
			rules.add("add(X,0,X).");
			rules.add("add(X,s(Y),s(Z)) :- add(X,Y,Z).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 5 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 6")
	void testPatternUnfold06() {
		// This is int-add-1.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("p(X) :- int(X),add(s(0),X,Y),p(Y).");
			rules.add("int(0).");
			rules.add("int(s(N)) :- int(N).");
			rules.add("add(X,0,X).");
			rules.add("add(X,s(Y),s(Z)) :- add(X,Y,Z).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 6 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 7")
	void testPatternUnfold07() {
		// This is toOne.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("p(X) :- toOne(X,Y),eq(Y,s(0)),p(s(X)).");
			rules.add("toOne(s(0),s(0)).");
			rules.add("toOne(s(s(X)),Y) :- toOne(s(X),Y).");
			rules.add("eq(0,0).");
			rules.add("eq(s(X),s(Y)) :- eq(X,Y).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 7 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 8")
	void testPatternUnfold08() {
		// This is while-minus-1.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("while(X) :- minus(X,X,Y),eq(Y,0),add1(X,Z),while(Z).");
			rules.add("add1(X,s(X)).");
			rules.add("toOne(s(s(X)), Y) :- toOne(s(X),Y).");
			rules.add("eq(0,0).");
			rules.add("eq(s(X),s(Y)) :- eq(X,Y).");
			rules.add("minus(X,0,X).");
			rules.add("minus(0,X,0).");
			rules.add("minus(s(X),s(Y),Z) :- minus(X,Y,Z).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 8 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 9")
	void testPatternUnfold09() {
		// This is a part of while-times-1.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			
			rules.add("add(X,s(Y),s(Z)) :- add(X,Y,Z).");
			rules.add("add(X,0,X).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 9 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 10")
	void testPatternUnfold10() {
		// This is a part of emmes-nonloop-ex1_2.pl.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			
			rules.add("add(s(X),Y,Z) :- add(X,s(Y),Z).");
			rules.add("add(0,X,X).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 10 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 11")
	void testPatternUnfold11() {
		// This is list-append-1.pl in TC25.

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			// rules.add("p(X) :- list(X),append(cons(a, nil), X, Y), p(Y).");
			// rules.add("list(nil).");
			// rules.add("list(cons(X,L)) :- list(L).");
			rules.add("append(cons(X,Xs),Ys,cons(X,Zs)) :- append(Xs,Ys,Zs).");
			rules.add("append(nil,Ys,Ys).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 11 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 12")
	void testPatternUnfold12() {

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("f(0,0).");
			rules.add("f(s(X),Y) :- f(X,Y).");
			rules.add("f(X,s(Y)) :- f(X,Y).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 12 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test pattern unfolding 13")
	void testPatternUnfold13() {

		Logger logger = Logger.getLogger("TestPatternUnfoldLp");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("g(X,Y) :- swap(X,Y),g(s(X),s(Y)).");
			rules.add("swap(0,X).");
			rules.add("swap(s(X),Y) :- swap(X,s(Y)).");
			
			unfoldLP(rules, logger, "===== test pattern unfolding 13 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	/**
	 * Unfolds the first rule of the provided list
	 * using all the rules of the list.
	 * 
	 * @param rules_string a list of rules, in
	 * String format
	 * @param logger a logger to display messages
	 * @param msg an introductory message to display
	 * @throws Exception
	 */
	void unfoldLP(List<String> rules_string, Logger logger, String msg) throws Exception {

		logger.info(msg);
		
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		// We build the LP program.
		LinkedList<RuleLp> rules = new LinkedList<>();
		for (String r : rules_string)
			rules.add(parser.parseLpRule(r, variables));
		Lp prog = new Lp("", rules, new LinkedList<Mode>());

		// The string corresponding to each variable (for display purposes).
		Map<Variable, String> variables_reversed = reverse(variables);

		// We compute the correct pattern rules (Prop. 2 of [Payet, ICLP'25]).
		Collection<PatternRuleLp> correct = prog.getCorrectPatternRules();
		assertTrue(correct != null, "Aborting test: 'correct' is null");
		logger.info("Computed correct pattern rules:");
		for (PatternRuleLp r : correct)
			logger.info(r.toString(variables_reversed));

		// We unfold the first rule of the program.
		RuleLp r1 = rules.getFirst();
		Collection<PatternRuleLp> x = new LinkedList<>(correct);
		Collection<PatternRuleLp> patunf1 = r1.unfoldPattern(x, 1);
		assertTrue(patunf1 != null, "Aborting test: 'patunf1' is null");
		logger.info("Computed unfolded rules:");
		for (PatternRuleLp r : patunf1)
			logger.info(r.toString());
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
