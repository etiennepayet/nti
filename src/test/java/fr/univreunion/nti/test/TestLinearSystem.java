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
import java.util.Map;
import java.util.logging.Logger;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.LinearSystem;
import fr.univreunion.nti.program.lp.nonloop.PatternRuleLp;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class TestLinearSystem {

	@Test
	@DisplayName("test linear system 1")
	void testLinearSystem1() {
		int n = 2;
		int p = 2;
		int[][] a = new int[][] { new int[] {1, 1}, new int[] {0, 1} };
		int[][] b = new int[][] { new int[] {2, 2, 1}, new int[] {0, 1, 1} };

		LinearSystem sys = new LinearSystem(n, p, a, b);

		assertTrue(sys.solveGauss(), "Aborting test: could not solve the system");

		Logger logger = Logger.getLogger("TestLinearSystem1");
		logger.info("\n" + sys.toString());
	}

	@Test
	@DisplayName("test linear system 2")
	void testLinearSystem2() {
		int n = 2;
		int p = 1;
		int[][] a = new int[][] { new int[] {1}, new int[] {1} };
		int[][] b = new int[][] { new int[] {2, 1}, new int[] {1, 1} };

		LinearSystem sys = new LinearSystem(n, p, a, b);
		
		assertTrue(!sys.solveGauss(), "Aborting test: could solve the system");

		Logger logger = Logger.getLogger("TestLinearSystem2");
		logger.info("\n" + sys.toString());
	}
	
	@Test
	@DisplayName("test linear system 3")
	void testLinearSystem3() {
		int n = 3;
		int p = 2;
		int[][] a = new int[][] { new int[] {1, 1}, new int[] {0, 1}, new int[] {2, 2} };
		int[][] b = new int[][] { new int[] {2, 2, 1}, new int[] {0, 1, 1}, new int[] {4, 4, 2} };

		LinearSystem sys = new LinearSystem(n, p, a, b);
				
		assertTrue(!sys.solveGauss(), "Aborting test: could solve the system");

		Logger logger = Logger.getLogger("TestLinearSystem3");
		logger.info("\n" + sys.toString());
	}
	
	@Test
	@DisplayName("test linear system 4")
	void testLinearSystem4() {

		Logger logger = Logger.getLogger("TestLinearSystem4");

		try {
			ParserString parser = new ParserString();
			Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

			String s1 = "while(X,Y){X->s(X)}{X->s(X),Y->s(Y)}{X->s(0),Y->0}";
			String s2 = "while(X,Y){X->s(s(X))}{X->s(s(X)),Y->s(Y)}{X->s(s(0)),Y->s(0)}";
			
			SimplePatternTerm p = parser.parseSimplePatternTerm(s1, variables);
			SimplePatternTerm q = parser.parseSimplePatternTerm(s2, variables);

			LinearSystem sys = PatternRuleLp.getLinearSystem(
					p.getPatternSubs().getTheta(), q.getPatternSubs().getTheta());
			
			assertTrue(sys != null, "Aborting test: 'sys' is null");
			
			logger.info("Generated system:\n" + sys.toString());
						
			assertTrue(sys.solveGauss(), "Aborting test: could not solve the system");
			
			logger.info("Solved system:\n" + sys.toString());
		}
		catch (Exception e) {
			logger.info(e.toString());
			e.printStackTrace();
		}
	}
}
