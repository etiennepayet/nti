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

package fr.univreunion.nti.parse.ari;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
import fr.univreunion.nti.term.Variable;

class ParserAriTest {

	@Test
	void previouslyDeclaredConstantsRemainVariablesInAnotherDocument() throws IOException {
		Trs previous = parse("(format TRS) (fun ari_scope_x 0) "
				+ "(rule ari_scope_x ari_scope_x)");
		Trs current = parse("(format TRS) (fun ari_scope_f 1) "
				+ "(rule (ari_scope_f ari_scope_x) ari_scope_x)");
		RuleTrs rule = current.iterator().next();
		assertInstanceOf(Variable.class, rule.getLeft().getChild(0));
		assertSame(rule.getLeft().getChild(0), rule.getRight());

		// Declaring the symbol in this document must still reuse its identity.
		Trs redeclared = parse("(format TRS) (fun ari_scope_x 0) "
				+ "(rule ari_scope_x ari_scope_x)");
		assertSame(previous.iterator().next().getLeft().getRootSymbol(),
				redeclared.iterator().next().getLeft().getRootSymbol());
	}

	@Test
	void rejectsApplicationsDeclaredOnlyInAnotherDocument() throws IOException {
		parse("(format TRS) (fun ari_scope_prior 1)");
		assertThrows(SyntaxException.class, () -> parse(
				"(format TRS) (rule (ari_scope_prior x) x)"));
	}

	@Test
	void rejectsVariableLeftSideEvenWhenAConstantWasPreviouslyDeclared() throws IOException {
		parse("(format TRS) (fun ari_scope_lhs 0)");
		assertThrows(SyntaxException.class, () -> parse(
				"(format TRS) (rule ari_scope_lhs ari_scope_lhs)"));
	}

	@Test
	void parsesDeclarationsRulesQuotedIdentifiersAndSharedVariables() throws IOException {
		Trs program = parse("""
				(format TRS)
				(fun ari_test_f 2)
				(fun |ari_test_0| 0)
				(rule (ari_test_f x |ari_test_0|) (ari_test_f |ari_test_0| x))
				(rule (ari_test_f y x) (ari_test_f x y))
				""");
		var rules = program.iterator();
		RuleTrs firstRule = rules.next();
		RuleTrs secondRule = rules.next();
		Function firstLeft = firstRule.getLeft();
		Function firstRight = (Function) firstRule.getRight();

		assertEquals("test.ari", program.getName());
		assertEquals("FULL", program.getStrategy());
		assertEquals(2, program.size());
		assertEquals("ari_test_f", firstLeft.getRootSymbol().getName());
		assertEquals("|ari_test_0|",
				((Function) firstLeft.getChild(1)).getRootSymbol().getName());
		assertSame(firstLeft.getChild(0), firstRight.getChild(1));
		assertSame(secondRule.getLeft().getChild(0),
				((Function) secondRule.getRight()).getChild(1));
	}

	@Test
	void rejectsFunctionDeclarationsAfterTheFirstRule() {
		SyntaxException exception = assertThrows(SyntaxException.class, () -> parse("""
				(format TRS)
				(fun ari_test_g 1)
				(rule (ari_test_g x) x)
				(fun ari_test_h 0)
				"""));

		assertEquals("error at line 4: 'rule' expected", exception.getMessage());
		assertEquals(4, exception.getLineNumber());
	}

	@Test
	void rejectsVariableLeftHandSidesAndUndeclaredApplications() {
		SyntaxException variableLeftSide = assertThrows(SyntaxException.class,
				() -> parse("(format TRS) (rule x x)"));
		assertEquals("error at line 1: left-hand side of rule cannot be a variable",
				variableLeftSide.getMessage());
		assertEquals(1, variableLeftSide.getLineNumber());

		SyntaxException undeclaredApplication = assertThrows(SyntaxException.class,
				() -> parse("(format TRS) (rule (ari_test_unknown x) x)"));
		assertEquals("error at line 1: undeclared identifier ari_test_unknown of arity 1",
				undeclaredApplication.getMessage());
		assertEquals(1, undeclaredApplication.getLineNumber());
	}

	@Test
	void reportsTokenMismatchesAsSyntaxErrors() {
		SyntaxException exception = assertThrows(SyntaxException.class,
				() -> parse("(format TRS (fun ari_test_k 0)"));

		assertEquals("syntax error at line 1: CLOSE_PAR expected, OPEN_PAR found instead",
				exception.getMessage());
		assertEquals(1, exception.getLineNumber());
	}

	private static Trs parse(String source) throws IOException {
		try (BufferedReader input = new BufferedReader(new StringReader(source))) {
			return (Trs) new ParserAri("test.ari", new ScannerAri(input)).parse();
		}
	}
}
