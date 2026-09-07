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

package fr.univreunion.nti.parse.trs;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.SyntaxException;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;

class ParserTrsTest {

	@Test
	void parsesOrderedRulesNestedTermsAndSharedVariables() throws IOException {
		Trs program = parse("""
				(VAR TRS_TEST_X TRS_TEST_Y)
				(RULES
				  trs_test_f(TRS_TEST_X,trs_test_g(a,TRS_TEST_Y))
				    -> trs_test_h(TRS_TEST_Y,TRS_TEST_X)
				  trs_test_k -> TRS_TEST_X
				)
				""");
		var rules = program.iterator();
		RuleTrs firstRule = rules.next();
		RuleTrs secondRule = rules.next();
		Function firstLeft = firstRule.getLeft();
		Function firstRight = (Function) firstRule.getRight();

		assertEquals("test.trs", program.getName());
		assertEquals("FULL", program.getStrategy());
		assertEquals(2, program.size());
		assertEquals("trs_test_f", firstLeft.getRootSymbol().getName());
		assertEquals("trs_test_g", ((Function) firstLeft.getChild(1)).getRootSymbol().getName());
		assertEquals("trs_test_k", secondRule.getLeft().getRootSymbol().getName());
		assertSame(firstLeft.getChild(0), firstRight.getChild(1));
		assertSame(firstLeft.getChild(0), secondRule.getRight());
		assertSame(((Function) firstLeft.getChild(1)).getChild(1), firstRight.getChild(0));
	}

	@Test
	void ignoresAuxiliaryDeclarationsIncludingNestedParentheses() throws IOException {
		Trs program = parse("""
				(COMMENT "ignored text" (nested,data) arrow -> value)
				(VAR TRS_TEST_Z)
				(RULES trs_test_p(TRS_TEST_Z) -> TRS_TEST_Z)
				""");

		assertEquals(1, program.size());
		assertEquals("trs_test_p", program.iterator().next().getLeft().getRootSymbol().getName());
	}

	@Test
	void acceptsEmptyVariableAndRuleDeclarations() throws IOException {
		Trs program = parse("(VAR) (RULES)");

		assertEquals(0, program.size());
		assertEquals("FULL", program.getStrategy());
	}

	@Test
	void reportsInvalidSpecificationsAndVariableLeftHandSides() {
		SyntaxException invalidSpecification = assertThrows(SyntaxException.class,
				() -> parse("RULES"));
		assertEquals("syntax error at line 1", invalidSpecification.getMessage());
		assertEquals(1, invalidSpecification.getLineNumber());

		SyntaxException variableLeftSide = assertThrows(SyntaxException.class,
				() -> parse("(VAR TRS_TEST_V) (RULES TRS_TEST_V -> a)"));
		assertEquals("error at line 1: left-hand side of rule cannot be a variable",
				variableLeftSide.getMessage());
		assertEquals(1, variableLeftSide.getLineNumber());
	}

	@Test
	void reportsUnknownStrategiesAndTokenMismatches() {
		SyntaxException unknownStrategy = assertThrows(SyntaxException.class,
				() -> parse("(STRATEGY FULL)"));
		assertEquals("error at line 1: unknown strategy FULL", unknownStrategy.getMessage());
		assertEquals(1, unknownStrategy.getLineNumber());

		SyntaxException missingArrow = assertThrows(SyntaxException.class,
				() -> parse("(RULES trs_test_a trs_test_b)"));
		assertEquals("syntax error at line 1: ARROW expected, ID found instead",
				missingArrow.getMessage());
		assertEquals(1, missingArrow.getLineNumber());
	}

	private static Trs parse(String source) throws IOException {
		try (BufferedReader input = new BufferedReader(new StringReader(source))) {
			return (Trs) new ParserTrs("test.trs", new ScannerTrs(input)).parse();
		}
	}
}
