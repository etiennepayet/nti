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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.logging.Logger;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.PatternRule;
import fr.univreunion.nti.program.lp.nonloop.PatternRuleLp;
import fr.univreunion.nti.program.trs.nonloop.iclp25.PatternRuleTrsIclp25;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A class for testing recurrent pairs.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
class TestPatternUnification {
	
	@Test
	@DisplayName("test pattern unification 1")
	void testPatternUnif01() {

		Logger logger = Logger.getLogger("TestPatternUnification1");

		try {
			LinkedList<String> s1 = new LinkedList<>();
			s1.add("gt(X,Y){}{}");
			s1.add("add(X,Y,Z){}{}");
			s1.add("while(Z,s(Y)){}{}");
			//
			LinkedList<String> s2 = new LinkedList<>();
			s2.add("gt(X1,Y1){X1->s(X1),Y1->s(Y1)}{X1->s(X1),Y1->0}");
			s2.add("add(X2,Y2,Z2){Y2->s(Y2),Z2->s(Z2)}{Y2->0,Z2->X2}");
			s2.add("while(X3,Y3){}{}");

			// The unification algorithm should succeed here.
			unifySequences(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unification 2")
	void testPatternUnif02() {

		Logger logger = Logger.getLogger("TestPatternUnification2");

		try {
			LinkedList<String> s1 = new LinkedList<>();
			s1.add("p(X){}{}");
			s1.add("p(s(X)){}{}");
			//
			LinkedList<String> s2 = new LinkedList<>();
			s2.add("p(s(X1)){}{}");
			s2.add("p(s(s(s(X2)))){}{}");

			// The unification algorithm should succeed here.
			unifySequences(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unification 3")
	void testPatternUnif03() {
		// This is Ex. 13 of [Payet, LOPSTR'25].
		// The unifier is {x->s^2(x)}^n{x->y}.

		Logger logger = Logger.getLogger("TestPatternUnification3");

		try {
			LinkedList<String> s1 = new LinkedList<>();
			s1.add("p(X){X->s(X)}{}");
			//
			LinkedList<String> s2 = new LinkedList<>();
			s2.add("p(X){X->s(s(s(X)))}{X->Y}");

			// The unification algorithm should succeed here.
			unifySequences(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern unification 4")
	void testPatternUnif04() {
		// The unifier is {x->s(x)}^n{x->x_1}.

		Logger logger = Logger.getLogger("TestPatternUnification4");

		try {
			LinkedList<String> s1 = new LinkedList<>();
			s1.add("p(X){X->s(X)}{X->s(X)}");
			//
			LinkedList<String> s2 = new LinkedList<>();
			s2.add("p(s(X)){X->s(s(X))}{X->X1}");

			// The unification algorithm should succeed here.
			unifySequences(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern unification 5")
	void testPatternUnif05() {
		// The unifier is {x->s(x)}^n{x->x_1,y_1->s^2(y)}.

		Logger logger = Logger.getLogger("TestPatternUnification5");

		try {
			LinkedList<String> s1 = new LinkedList<>();
			s1.add("dbl(X,Y){X->s(X)}{X->s(X1),Y->Y1}");
			//
			LinkedList<String> s2 = new LinkedList<>();
			s2.add("dbl(s(X),s(s(Y))){}{}");

			// The unification algorithm should succeed here.
			unifySequences(s1, s2, true, logger);			
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test pattern unification 6")
	void testPatternUnif06() {
		// Test of method SimplePatternSubstitution SimplePatternTerm.unifyWith(PatternRuleLp).
		// Here, the fact r is weakened to dbl(s^{1,1}(0),s^{2,2}(0)).
		// Then, the unifier is {z->s^2(z)}^n{x1->0,z->s^2(0)}.

		Logger logger = Logger.getLogger("TestPatternUnification6");

		try {
			String s1 = "dbl(X,Z){X->s(X)}{X->s(X1)}";
			String s2 = "dbl(X,Y){X->s(X),Y->s(s(Y))}{X->0,Y->0}";

			// The unification algorithm should succeed here.
			unifyFact(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unification 7")
	void testPatternUnif07() {
		// Test of method SimplePatternSubstitution SimplePatternTerm.unifyWith(PatternRuleLp).
		// Here, the fact r is weakened to add(x,s^2(0),s^2(x)).
		// The unifier is {}^n{z->s^2(x)}.

		Logger logger = Logger.getLogger("TestPatternUnification7");

		try {
			String s1 = "add(X,s(s(0)),Z){}{}";
			String s2 = "add(X,Y,Z){Y->s(Y),Z->s(Z)}{Y->0,Z->X}";

			// The unification algorithm should succeed here.
			unifyFact(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unification 8")
	void testPatternUnif08() {
		// Test of method SimplePatternSubstitution SimplePatternTerm.unifyWith(PatternRuleLp).
		// Here, the fact r is weakened to add(s^{2,4}(0),s^{3,6}(0),s^{1,2}(x)).
		// The unifier is {x->s(x),z->s(z)}^n{x->s^2(0),z->s^4(0)}.

		Logger logger = Logger.getLogger("TestPatternUnification8");

		try {
			String s1 = "add(X,Y,Z){X->s(X),Y->s(s(Y)),Z->s(Z)}{X->s(s(X)),Y->s(s(s(s(X))))}";
			String s2 = "add(X,Y,Z){X->s(s(X)),Y->s(s(s(Y))),Z->s(Z)}{X->0,Y->0,Z->X}";

			// The unification algorithm should succeed here.
			unifyFact(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	@Test
	@DisplayName("test pattern unification 9")
	void testPatternUnif09() {
		// Test of method SimplePatternSubstitution SimplePatternTerm.unifyWith(PatternRuleLp).
		// Here, the fact r is weakened to:
		// 1) add(x2,s^{1,1}(0),s^{1,1}(x2))
		// 2) add(x2,s^{1,1,1}(0),s^{1,1,1}(x2)).
		// The unifiers are:
		// 1) {x1->0,x2->s^{1,1}(0),z->s^{2,2}(0)} i.e.,
		// {x2->s(x2),z->s^2(z)}^n{x1->0,x2->s(0),z->s^2(0)}
		// 2) {x1->s^{1,0,0}(0),x2->s^{1,1,1}(0),z->s^{2,2,2}(0)} i.e.,
		// {x1->s(x1),x2->s(x2),z->s^2(z)}^n{x2->s(x2),z->s^2(z)}^m{x1->0,x2->s(0),z->s^2(0)}.

		Logger logger = Logger.getLogger("TestPatternUnification9");

		try {
			String s1 = "add(X,Y,Z){X->s(X),Y->s(Y)}{X->s(X1),Y->s(X1)}";
			String s2 = "add(X,Y,Z){Y->s(Y),Z->s(Z)}{X->X2,Y->0,Z->X2}";

			// The unification algorithm should succeed here.
			unifyFact(s1, s2, true, logger);
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}
	
	@Test
	@DisplayName("test pattern unification 10")
	void testPatternUnif10() {

		Logger logger = Logger.getLogger("TestPatternUnification10");
		
		if (logger.isLoggable(java.util.logging.Level.INFO))
			logger.info("===== " + logger.getName() + " =====");

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		try {
			// gt(s^{1,0}(0),0):
			SimplePatternTerm left = parser.parseSimplePatternTerm("gt(X1,Y1){X1->s(X1)}{X1->0,Y1->0}", variables);
			// true:
			SimplePatternTerm right = parser.parseSimplePatternTerm("true{}{}", variables);
			//
			PatternRuleTrsIclp25 r = PatternRuleTrsIclp25.getInstance(left, right, 0);
			
			// gt(s^{1,1}(X),s^{1,0}(0)):
			SimplePatternTerm p = parser.parseSimplePatternTerm("gt(X,Y){X->s(X),Y->s(Y)}{X->s(X),Y->0}", variables);			
			
			Map<Variable, String> strings = new HashMap<>();
			StringBuffer s = new StringBuffer("Weakened rules wrt p = " + p.toString(strings) + " :");
			for (PatternRule w : r.weaken(r.getLeft(), p)) {
				s.append("\n");
				s.append(w.toString(strings));
				if (w.getLeft().unifyWith(p) != null) s.append(" -- unifies");
				else s.append(" -- does not unify");
			}
			if (logger.isLoggable(java.util.logging.Level.INFO))
				logger.info(s.toString());
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}
	
	@Test
	@DisplayName("test pattern unification 11")
	void testPatternUnif11() {

		Logger logger = Logger.getLogger("TestPatternUnification11");
		
		if (logger.isLoggable(java.util.logging.Level.INFO))
			logger.info("===== " + logger.getName() + " =====");

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		try {
			// gt(s^{1,1}(X),s^{1,0}(0)):
			SimplePatternTerm left = parser.parseSimplePatternTerm("gt(X,Y){X->s(X),Y->s(Y)}{X->s(X),Y->0}", variables);
			// true:
			SimplePatternTerm right = parser.parseSimplePatternTerm("true{}{}", variables);
			//
			PatternRuleTrsIclp25 r = PatternRuleTrsIclp25.getInstance(left, right, 0);
			
			// gt(s^{1,1}(0),0):
			SimplePatternTerm p = parser.parseSimplePatternTerm("gt(X1,Y1){X1->s(X1)}{X1->s(0),Y1->0}", variables);					
			
			Map<Variable, String> strings = new HashMap<>();
			StringBuffer s = new StringBuffer("Weakened rules wrt p = " + p.toString(strings) + " :");
			for (PatternRule w : r.weaken(r.getLeft(), p)) {
				s.append("\n");
				s.append(w.toString(strings));
				if (w.getLeft().unifyWith(p) != null) s.append(" -- unifies");
				else s.append(" -- does not unify");
			}
			if (logger.isLoggable(java.util.logging.Level.INFO))
				logger.info(s.toString());
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}

	/**
	 * Applies the unification algorithm of [Payet, LOPSTR'25] to
	 * the provided sequences of pattern terms given as strings.
	 * 
	 * The provided boolean <code>expectedResult</code> indicates
	 * whether the given sequences should unify or not.  
	 * 
	 * @param s1 a sequence of pattern terms given as strings
	 * @param s2 a sequence of pattern terms given as strings
	 * @param expectedResult the expected unification result
	 * @param logger a logger to display messages
	 * @throws Exception
	 */
	void unifySequences(LinkedList<String> s1, LinkedList<String> s2,
			boolean expectedResult, Logger logger) throws Exception {

		if (logger.isLoggable(java.util.logging.Level.INFO))
			logger.info("===== " + logger.getName() + " =====");

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.
		SimplePatternSubstitution theta = null; // The mgu that we compute incrementally.

		Iterator<String> it1 = s1.iterator();
		Iterator<String> it2 = s2.iterator();
		while (it1.hasNext() && it2.hasNext()) {
			// We read the next pattern terms from s1 and s2.
			SimplePatternTerm p = parser.parseSimplePatternTerm(it1.next(), variables);
			SimplePatternTerm q = parser.parseSimplePatternTerm(it2.next(), variables);
			// We add the previously computed mgu to p.
			Substitution sigma = (theta == null ? p.getPumping() : p.getPumping().composeWith(theta.getPumping()));
			Substitution mu    = (theta == null ? p.getClosing() : p.getClosing().composeWith(theta.getClosing()));
			p = SimplePatternTerm.getInstance(p.getBaseTerm(), sigma, mu);

			SimplePatternSubstitution mgu = p.unifyWith(q);
			assertTrue(
					(expectedResult ? mgu != null : mgu == null),
					"Aborting test: p.unifyWith(q) returns " +
							(expectedResult ? "null!" : "non null!"));

			if (mgu == null) { theta = null; break; }

			theta = (theta == null ? mgu : theta.composeWith(mgu));
		}

		if (logger.isLoggable(java.util.logging.Level.INFO)) {
			logger.info("mgu = " + (theta == null ? "null" : theta.toString(reverse(variables))));
		}
	}

	/**
	 * Test of method
	 * <code>SimplePatternSubstitution SimplePatternTerm.unifyWith(PatternRuleLp)</code>.
	 * 
	 * The provided boolean <code>expectedResult</code> indicates
	 * whether the given sequences should unify or not.  
	 * 
	 * @param s1 a pattern term given as a string
	 * @param s2 a pattern term given as a string
	 * @param expectedResult the expected unification result
	 * @param logger a logger to display messages
	 * @throws Exception
	 */
	void unifyFact(String s1, String s2,
			boolean expectedResult, Logger logger) throws Exception {

		if (logger.isLoggable(java.util.logging.Level.INFO))
			logger.info("===== " + logger.getName() + " =====");
		
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		SimplePatternTerm p = parser.parseSimplePatternTerm(s1, variables);
		SimplePatternTerm q = parser.parseSimplePatternTerm(s2, variables);

		PatternRuleLp r = PatternRuleLp.getInstance(q, 0);

		Collection<SimplePatternSubstitution> mgus = p.unifyWith(r);

		assertTrue(
				(expectedResult ? !mgus.isEmpty() : mgus.isEmpty()),
				"Aborting test: p.unifyWith(r) returns " +
						(expectedResult ? "empty!" : "non empty!"));

		if (logger.isLoggable(java.util.logging.Level.INFO)) {
			Map<Variable, String> reversed = reverse(variables);
			for (SimplePatternSubstitution mgu : mgus)
				logger.info("mgu = " + mgu.toString(reversed));
		}
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
