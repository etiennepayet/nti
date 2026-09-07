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

package fr.univreunion.nti.parse.srs;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.SyntaxException;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Variable;

class ParserSrsTest {

	@Test
	void parsesOrderedWordRulesWithSharedTerminalVariables() throws IOException {
		Trs program = parse("""
				(RULES
				  srs_test_a srs_test_b -> srs_test_c,
				  srs_test_d ->
				)
				""");
		var rules = program.iterator();
		RuleTrs firstRule = rules.next();
		RuleTrs secondRule = rules.next();
		Function firstLeft = firstRule.getLeft();
		Function firstLeftSuffix = (Function) firstLeft.getChild(0);
		Function firstRight = (Function) firstRule.getRight();
		Variable firstTerminal = (Variable) firstLeftSuffix.getChild(0);
		Variable secondTerminal = (Variable) secondRule.getLeft().getChild(0);

		assertEquals("test.srs", program.getName());
		assertEquals("FULL", program.getStrategy());
		assertEquals(2, program.size());
		assertEquals("srs_test_a", firstLeft.getRootSymbol().getName());
		assertEquals("srs_test_b", firstLeftSuffix.getRootSymbol().getName());
		assertEquals("srs_test_c", firstRight.getRootSymbol().getName());
		assertEquals("srs_test_d", secondRule.getLeft().getRootSymbol().getName());
		assertSame(firstTerminal, firstRight.getChild(0));
		assertSame(secondTerminal, secondRule.getRight());
	}

	@Test
	void ignoresAuxiliaryDeclarationsIncludingNestedParentheses() throws IOException {
		Trs program = parse("""
				(COMMENT "ignored text" (nested,data) arrow -> value)
				(RULES srs_test_e -> srs_test_f)
				""");

		assertEquals(1, program.size());
		assertEquals("srs_test_e", program.iterator().next().getLeft().getRootSymbol().getName());
	}

	@Test
	void acceptsAnEmptyRulesDeclaration() throws IOException {
		Trs program = parse("(RULES)");

		assertEquals(0, program.size());
		assertEquals("FULL", program.getStrategy());
	}

	@Test
	void reportsInvalidSpecificationsAndMissingRulesAfterCommas() {
		SyntaxException invalidSpecification = assertThrows(SyntaxException.class,
				() -> parse("RULES"));
		assertEquals("syntax error at line 1", invalidSpecification.getMessage());
		assertEquals(1, invalidSpecification.getLineNumber());

		SyntaxException missingRule = assertThrows(SyntaxException.class,
				() -> parse("(RULES srs_test_g -> srs_test_h, )"));
		assertEquals("ID expected, CLOSE_PAR found instead at line 1", missingRule.getMessage());
		assertEquals(1, missingRule.getLineNumber());
	}

	@Test
	void reportsUnknownStrategiesAndTokenMismatches() {
		SyntaxException unknownStrategy = assertThrows(SyntaxException.class,
				() -> parse("(STRATEGY FULL)"));
		assertEquals("error at line 1: unknown strategy FULL", unknownStrategy.getMessage());
		assertEquals(1, unknownStrategy.getLineNumber());

		SyntaxException missingArrow = assertThrows(SyntaxException.class,
				() -> parse("(RULES srs_test_i)"));
		assertEquals("syntax error at line 1: ARROW expected, CLOSE_PAR found instead",
				missingArrow.getMessage());
		assertEquals(1, missingArrow.getLineNumber());
	}

	@Test
	void preservesInnerToOuterFunctionSymbolInterningOrder() throws IOException {
		Trs program = parse("(RULES srs_test_outer srs_test_inner ->)");
		Function outer = program.iterator().next().getLeft();
		Function inner = (Function) outer.getChild(0);

		assertTrue(inner.getRootSymbol().lt(outer.getRootSymbol()));
	}

	private static Trs parse(String source) throws IOException {
		try (BufferedReader input = new BufferedReader(new StringReader(source))) {
			return (Trs) new ParserSrs("test.srs", new ScannerSrs(input)).parse();
		}
	}
}
