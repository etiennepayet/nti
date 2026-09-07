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
import java.util.logging.Logger;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.pattern.LinearSystem;
import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
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

		Logger logger = Logger.getLogger("TestLinearSystem1");
		logger.info("System to solve:\n" + sys);

		assertTrue(sys.solve(), "Aborting test: could not solve the system");
		assertEquals(
				"""
				n = 2, m = 2
				1 1 = 2 2 1\s
				0 1 = 0 1 1\s
				""",
				sys.toString());

		logger.info("Solved system:\n" + sys);
	}

	@Test
	@DisplayName("test linear system 2")
	void testLinearSystem2() {
		int n = 2;
		int p = 1;
		int[][] a = new int[][] { new int[] {1}, new int[] {1} };
		int[][] b = new int[][] { new int[] {2, 1}, new int[] {1, 1} };

		LinearSystem sys = new LinearSystem(n, p, a, b);
		
		assertFalse(sys.solve(), "Aborting test: could solve the system");
		assertEquals(
				"""
				n = 2, m = 1
				1 = 2 1\s
				1 = 1 1\s
				""",
				sys.toString());

		Logger logger = Logger.getLogger("TestLinearSystem2");
		logger.info("\n" + sys);
	}
	
	@Test
	@DisplayName("test linear system 3")
	void testLinearSystem3() {
		int n = 3;
		int p = 2;
		int[][] a = new int[][] { new int[] {1, 1}, new int[] {0, 1}, new int[] {2, 2} };
		int[][] b = new int[][] { new int[] {2, 2, 1}, new int[] {0, 1, 1}, new int[] {4, 4, 2} };

		LinearSystem sys = new LinearSystem(n, p, a, b);
				
		assertTrue(sys.solve(), "Aborting test: could not solve the system");
		assertEquals(
				"""
				n = 3, m = 2
				1 1 = 2 2 1\s
				0 1 = 0 1 1\s
				2 2 = 4 4 2\s
				""",
				sys.toString());

		Logger logger = Logger.getLogger("TestLinearSystem3");
		logger.info("\n" + sys);
	}
	
	@Test
	@DisplayName("test linear system 4")
	void testLinearSystem4() throws IOException {

		Logger logger = Logger.getLogger("TestLinearSystem4");

		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

		String s1 = "while(X,Y){X->s(X)}{X->s(X),Y->s(Y)}{X->s(0),Y->0}";
		String s2 = "while(X,Y){X->s(s(X))}{X->s(s(X)),Y->s(Y)}{X->s(s(0)),Y->s(0)}";

		SimplePatternTerm p = parser.parseSimplePatternTerm(s1, variables);
		SimplePatternTerm q = parser.parseSimplePatternTerm(s2, variables);

		LinearSystem sys = PatternRuleLp.getLinearSystem(
				p.getPatternSubstitution().getHatFunctionSubstitution(),
				q.getPatternSubstitution().getHatFunctionSubstitution());

		assertNotNull(sys, "Aborting test: 'sys' is null");

		logger.info("Generated system:\n" + sys);

		assertTrue(sys.solve(), "Aborting test: could not solve the system");

		logger.info("Solved system:\n" + sys);
	}

	@Test
	@DisplayName("test linear system 5")
	void testLinearSystem5() {
		int n = 1;
		int p = 1;
		int[][] a = new int[][] { new int[] {2} };
		int[][] b = new int[][] { new int[] {1, -1} };

		LinearSystem sys = new LinearSystem(n, p, a, b);

		Logger logger = Logger.getLogger("TestLinearSystem5");
		logger.info("System to solve:\n" + sys);

		assertFalse(sys.solve(), "Aborting test: could solve the system");
	}

	@Test
	@DisplayName("solve a square system despite non-integral Gaussian factors")
	void solvesSquareSystemDespiteNonIntegralGaussianFactors() {
		int[][] a = {
				{2, 1},
				{1, 1}
		};
		int[][] b = {
				{2, 1, 0},
				{1, 1, 0}
		};
		LinearSystem system = new LinearSystem(2, 2, a, b);

		assertTrue(system.solve());
	}

	@Test
	@DisplayName("solve an underdetermined system")
	void solvesUnderdeterminedSystem() {
		int[][] a = {{2, 3}};
		int[][] b = {{3, 2, 5}};
		LinearSystem system = new LinearSystem(1, 2, a, b);

		assertTrue(system.solve());
	}

	@Test
	@DisplayName("reject a universally solvable system without affine solution")
	void rejectsUniversallySolvableSystemWithoutAffineSolution() {
		int[][] a = {{2, 3}};
		int[][] b = {{1, 0, 2}};
		LinearSystem system = new LinearSystem(1, 2, a, b);

		assertFalse(system.solve());
	}

	@Test
	@DisplayName("do not modify matrices upon failure")
	void doesNotModifyMatricesUponFailure() {
		int[][] a = {
				{1, 0, 0},
				{1, 2, 0},
				{1, 1, 1}
		};
		int[][] b = {
				{1, 0, 0, 0},
				{2, 0, 0, 0},
				{3, 0, 0, 0}
		};
		LinearSystem system = new LinearSystem(3, 3, a, b);

		assertFalse(system.solve());
		assertEquals(
				"""
				n = 3, m = 3
				1 0 0 = 1 0 0 0\s
				1 2 0 = 2 0 0 0\s
				1 1 1 = 3 0 0 0\s
				""",
				system.toString());
	}

	@Test
	@DisplayName("copy construction matrices")
	void copiesConstructionMatrices() {
		int[][] a = {{1}};
		int[][] b = {{1, 0}};
		LinearSystem system = new LinearSystem(1, 1, a, b);

		a[0][0] = 0;
		b[0][0] = 0;
		a[0] = new int[] {0};
		b[0] = new int[] {0, 1};

		assertEquals(
				"""
				n = 1, m = 1
				1 = 1 0\s
				""",
				system.toString());
		assertTrue(system.solve());
	}
}
