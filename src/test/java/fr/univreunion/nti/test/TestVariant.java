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
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class TestVariant {

	@Test
	@DisplayName("test variant 1")
	void testVariant1() {
		Logger logger = Logger.getLogger("TestVariant");

		try {
			ParserString parser = new ParserString();
			Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

			Term s = parser.parseTerm("f(X,g(X))", variables);
			Term t = parser.parseTerm("f(Y,g(Z))", variables);

			assertFalse(s.isVariantOf(t),
					"Aborting test: s.isVariantOf(t) returns true");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test variant 2")
	void testVariant2() {
		Logger logger = Logger.getLogger("TestVariant");

		try {
			ParserString parser = new ParserString();
			Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

			Term s = parser.parseTerm("f(X,g(T))", variables);
			Term t = parser.parseTerm("f(Y,g(Z))", variables);

			Substitution theta = new Substitution();
			
			assertTrue(s.isVariantOf(t, theta),
					"Aborting test: s.isVariantOf(t) returns false");
			
			logger.info("theta = " + theta.toString(reverse(variables)));
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test variant 3")
	void testVariant3() {
		Logger logger = Logger.getLogger("TestVariant");

		try {
			ParserString parser = new ParserString();
			Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

			Term s = parser.parseTerm("f(X,g(T))", variables);
			Term t = parser.parseTerm("f(Y,g(0))", variables);

			assertFalse(s.isVariantOf(t),
					"Aborting test: s.isVariantOf(t) returns true");
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test variant 4")
	void testVariant4() {
		Logger logger = Logger.getLogger("TestVariant");

		try {
			ParserString parser = new ParserString();
			Map<String, Variable> variables = new HashMap<>(); // The variables that we read.

			Term s = parser.parseTerm("f(X,g(T))", variables);
			Term t = parser.parseTerm("f(Y,Z)", variables);

			assertFalse(s.isVariantOf(t),
					"Aborting test: s.isVariantOf(t) returns true");
		}
		catch (Exception e) {
			logger.info(e.toString());
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
