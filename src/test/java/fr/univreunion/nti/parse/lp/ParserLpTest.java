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

package fr.univreunion.nti.parse.lp;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.SyntaxException;
import fr.univreunion.nti.program.lp.Lp;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.term.Function;

class ParserLpTest {

	@Test
	void rejectsSeveralQueries() {
		SyntaxException exception = assertThrows(SyntaxException.class, () -> parse("""
				%query: append(o,i,o).
				append([],Ys,Ys).
				append([X|Xs],Ys,[X|Zs]) :- append(Xs,Ys,Zs).

				%query: append3(i,o,i,o).
				append3(Xs,Ys,Zs,Ts) :- append(Xs,Ys,Us), append(Us,Zs,Ts).
				"""));

		assertEquals("syntax error at line 5: only one %query directive is allowed",
				exception.getMessage());
		assertEquals(5, exception.getLineNumber());
	}

	@Test
	void requiresOneLeadingQueryAndAtLeastOneClause() {
		assertThrows(SyntaxException.class, () -> parse("p."));
		assertThrows(SyntaxException.class, () -> parse("%query: p."));
		assertThrows(SyntaxException.class, () -> parse("p.\n%query: p."));
	}

	@Test
	void parsesDecimalNumbersWithoutEndingListsAtTheDecimalPoint() throws IOException {
		Lp program = parse("""
				%query: p(i).
				p :- q(a).
				p :- q(b).
				q(a).
				q(b).

				q1([(e)]*f(0)).
				q2([[], a, 3.14|[(1,2,3)-f(a+b,a-b,a*b,a/b)]]).
				q2([f(a/b)]).

				r((a)).

				p(X) :- q(X, X).
				q(f(Y), Y) :- p(Y).
				""");
		String rendering = program.toString();

		assertEquals(10, program.size());
		assertTrue(rendering.contains("3.14"));
		assertTrue(rendering.contains("* mode:"));
		assertTrue(rendering.contains("p(i)"));
	}

	@Test
	void appliesPrologPrecedenceAndLeftAssociativity() throws IOException {
		Lp program = parse("%query: p.\np :- q(a-b-c,a+b*c,a/b/c).");

		assertTrue(program.toString().contains(
				"q(-(-(a,b),c),+(a,*(b,c)),/(/(a,b),c))"));
	}

	@Test
	void parsesAnIdentifierLedExpressionOnTheLeftOfEquality() throws IOException {
		Lp program = parse("%query: p(i,i,i).\np(X,Y,Z) :- f(X)+g(Y)*h(X)=Z.");
		RuleLp parsedRule = program.iterator().next();
		Function equality = parsedRule.getBody(0);
		Function sum = (Function) equality.getChild(0);

		assertEquals(2, program.size());
		assertEquals("=", equality.getRootSymbol().getName());
		assertEquals("+", sum.getRootSymbol().getName());
		assertEquals("f", ((Function) sum.getChild(0)).getRootSymbol().getName());
		assertEquals("*", ((Function) sum.getChild(1)).getRootSymbol().getName());
		assertSame(parsedRule.getHead().getChild(2), equality.getChild(1));
		assertSame(parsedRule.getHead().getChild(0), ((Function) sum.getChild(0)).getChild(0));
	}

	@Test
	void rejectsAnArithmeticExpressionUsedAsAnAtom() {
		assertThrows(SyntaxException.class, () -> parse("%query: p.\np :- a+b."));
		assertThrows(SyntaxException.class, () -> parse("%query: p.\np :- a*b."));
	}

	@Test
	void distinguishesExplicitAndTokenMismatchSyntaxErrors() {
		SyntaxException unexpectedItem = assertThrows(SyntaxException.class,
				() -> parse("%query: p.\nX."));
		assertEquals("syntax error at line 2", unexpectedItem.getMessage());
		assertEquals(2, unexpectedItem.getLineNumber());

		SyntaxException nonEndedList = assertThrows(SyntaxException.class,
				() -> parse("%query: p.\np([a)."));
		assertEquals("syntax error: non-ended list at line 2", nonEndedList.getMessage());
		assertEquals(2, nonEndedList.getLineNumber());

		SyntaxException tokenMismatch = assertThrows(SyntaxException.class,
				() -> parse("%query: p.\np(a]"));
		assertEquals("syntax error at line 2: CLOSE_PAR expected, CLOSE_SQ_PAR found instead",
				tokenMismatch.getMessage());
		assertEquals(2, tokenMismatch.getLineNumber());
	}

	@Test
	void preservesVariablesAndAddsTheReflexiveEqualityRule() throws IOException {
		Lp program = parse("%query: p(i).\np(X) :- X = f(X).");
		var rules = program.iterator();
		RuleLp parsedRule = rules.next();
		RuleLp equalityRule = rules.next();
		Function equalityAtom = parsedRule.getBody(0);

		assertEquals(2, program.size());
		assertEquals("=", equalityAtom.getRootSymbol().getName());
		assertSame(parsedRule.getHead().getChild(0), equalityAtom.getChild(0));
		assertSame(parsedRule.getHead().getChild(0), ((Function) equalityAtom.getChild(1)).getChild(0));
		assertSame(equalityRule.getHead().getChild(0), equalityRule.getHead().getChild(1));
	}

	private static Lp parse(String source) throws IOException {
		try (BufferedReader input = new BufferedReader(new StringReader(source))) {
			return (Lp) new ParserLp("test.pl", new ScannerLp(input)).parse();
		}
	}
}
