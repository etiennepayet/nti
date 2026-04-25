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

import fr.univreunion.nti.Options;
import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.nonloop.iclp25.CorrectPatternRuleTrsProducer;
import fr.univreunion.nti.program.trs.nonloop.iclp25.PatternRuleTrsIclp25;
import fr.univreunion.nti.term.Variable;

class TestPatternUnfoldingTrs {

	@Test
	@DisplayName("test pattern unfolding 1")
	void testPatternUnfold1() {
		// This is the running example of WST'25.

		Logger logger = Logger.getLogger("TestPatternUnfoldTrs");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("while(true,X,Y) -> while(gt(X,Y), add(X,Y), s(Y))");
			rules.add("gt(s(X),0) -> true");
			rules.add("gt(0,Y) -> false");
			rules.add("gt(s(X),s(Y)) -> gt(X,Y)");
			rules.add("add(X,0) -> X");
			rules.add("add(X,s(Y)) -> s(add(X,Y))");

			unfoldTrs(rules, logger, "===== test pattern unfolding 1 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unfolding 2")
	void testPatternUnfold2() {
		// This is AProVE_10/ex2.ari.

		Logger logger = Logger.getLogger("TestPatternUnfoldTrs");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("g(tt,X) -> g(h(f(X,X)),s(X))");
			rules.add("h(f(0,Y)) -> tt");
			rules.add("f(s(X),Y) -> f(X,s(Y))");

			unfoldTrs(rules, logger, "===== test pattern unfolding 2 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern unfolding 3")
	void testPatternUnfold3() {
		// This is AProVE_10/ex3.ari.

		Logger logger = Logger.getLogger("TestPatternUnfoldTrs");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("g(tt,X,Y) -> g(f(X,Y),s(X),s(Y))");
			rules.add("f(0,0) -> tt");
			rules.add("f(s(X),Y) -> f(X,Y)");
			rules.add("f(X,s(Y)) -> f(X,Y)");

			unfoldTrs(rules, logger, "===== test pattern unfolding 3 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern unfolding 4")
	void testPatternUnfold4() {
		// This is EEG_IJCAR_12/enger-nonloop-toOne.ari.

		Logger logger = Logger.getLogger("TestPatternUnfoldTrs");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("f(tt,X) -> f(eq(toOne(X),s(0)),s(X))");
			rules.add("eq(0,0) -> tt");
			rules.add("eq(s(X),s(Y)) -> eq(X,Y)");
			rules.add("toOne(s(0)) -> s(0)");
			rules.add("toOne(s(s(X))) -> toOne(s(X))");

			unfoldTrs(rules, logger, "===== test pattern unfolding 4 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern unfolding 5")
	void testPatternUnfold5() {
		// This is EEG_IJCAR_12/emmes-nonloop-ex1_2.ari.

		Logger logger = Logger.getLogger("TestPatternUnfoldTrs");

		try {
			LinkedList<String> rules = new LinkedList<>();
			// rules.add("f(true,X,Y) -> f(gt(X,Y),plus2(X),plus1(Y))");
			// rules.add("gt(s(X),0) -> true");
			// rules.add("gt(0,X) -> false");
			// rules.add("gt(s(X),s(Y)) -> gt(X,Y)");
			rules.add("plus1(X) -> plus(X,s(0))");
			rules.add("plus2(X) -> plus(X,s(s(0)))");
			rules.add("plus(0,X) -> X");
			rules.add("plus(s(X),Y) -> plus(X,s(Y))");

			unfoldTrs(rules, logger, "===== test pattern unfolding 5 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unfolding 6")
	void testPatternUnfold6() {
		// This is EEG_IJCAR_12/emmes-nonloop-ex3_2.ari.

		Logger logger = Logger.getLogger("TestPatternUnfoldTrs");

		try {
			LinkedList<String> rules = new LinkedList<>();
			rules.add("f(true,X) -> f(gt(X,0),double(X))");
			rules.add("gt(s(X),0) -> true");
			rules.add("gt(0,X) -> false");
			rules.add("gt(s(X),s(Y)) -> gt(X,Y)");
			rules.add("double(X) -> plus(X,X)");
			rules.add("plus(0,X) -> X");
			rules.add("plus(s(X),Y) -> plus(X,s(Y))");

			unfoldTrs(rules, logger, "===== test pattern unfolding 6 =====");
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unfolding 7")
	void testPatternUnfold7() {
		// This is EEG_IJCAR_12/emmes-nonloop-ex3_2.ari.

		Logger logger = Logger.getLogger("TestPatternUnfoldTrs");
		
		logger.info("===== test pattern unfolding 7 =====");

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		try {			
			// The next pattern rule should occur at
			// iteration 3 of the unfolding operator:
			// f(true, s^{1,0}(0)) -> f(gt(s^{1,0}(0), 0), s^{2,0}(0))
			PatternRuleTrsIclp25 r1 = parser.parsePatternRuleTrs(
					"f(X,Y){Y->s(Y)}{X->true,Y->0} -> f(gt(X,0),Y){X->s(X),Y->s(s(Y))}{X->0,Y->0}",
					variables);

			// The next pattern rule should be produced by an
			// enhanced version of Prop.9 of [Payet, WST'25].
			// gt(s^{1,1}(X), s^{1,0}(0)) -> true:
			PatternRuleTrsIclp25 r2 = parser.parsePatternRuleTrs(
					"gt(X,Y){X->s(X),Y->s(Y)}{X->s(X),Y->0} -> true{}{}",
					variables);
			
			LinkedList<PatternRuleTrsIclp25> unfolders = new LinkedList<>();
			unfolders.add(r2);
						
			for (PatternRuleTrsIclp25 u : r1.unfold(null, unfolders, 0, new Proof()))
				logger.info(u.toString());
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
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
	void unfoldTrs(List<String> rules_string, Logger logger, String msg) throws Exception {

		logger.info(msg);

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		// We build the TRS.
		LinkedList<RuleTrs> rules = new LinkedList<>();
		for (String r : rules_string)
			rules.add(parser.parseTrsRule(r, variables));
		Trs trs = new Trs("", rules, "FULL");

		Options.getInstance(new String[] {"-v"});

		// The string corresponding to each variable (for display purposes).
		Map<Variable, String> variables_reversed = reverse(variables);

		// We compute the correct pattern rules (Prop. 9 of [Payet, WST'25]).
		Collection<PatternRuleTrsIclp25> correct = trs.getCorrectPatternRulesIclp25();
		assertTrue(correct != null, "Aborting test: 'correct' is null");
		logger.info("Computed correct pattern rules:");
		for (PatternRuleTrsIclp25 r : correct)
			logger.info(r.toString(variables_reversed));

		// We unfold the first rule of the TRS.
		PatternRuleTrsIclp25 r1 =
				CorrectPatternRuleTrsProducer.getCorrectPatternRules2(rules.getFirst());
		Collection<PatternRuleTrsIclp25> patunf1 = r1.unfold(null, correct, 1, new Proof());
		assertTrue(patunf1 != null, "Aborting test: 'patunf1' is null");
		logger.info("Computed unfolded rules -- iteration 1:");
		for (PatternRuleTrsIclp25 r : patunf1)
			logger.info(r.toString());

		// Then, we unfold the produced unfolded rules.
		Collection<PatternRuleTrsIclp25> patunf2 = new LinkedList<>();
		for (PatternRuleTrsIclp25 r : patunf1)
			patunf2.addAll(r.unfold(null, correct, 2, new Proof()));
		logger.info("Computed unfolded rules -- iteration 2:");
		for (PatternRuleTrsIclp25 r : patunf2)
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
