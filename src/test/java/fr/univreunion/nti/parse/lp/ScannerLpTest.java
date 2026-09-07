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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.LexicalException;
import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Token;

class ScannerLpTest {

	@Test
	void distinguishesIdentifiersVariablesAnonymousVariablesAndNumbers() throws IOException {
		ScannerLp scanner = scanner("lower_name A1 _Tail _ 0 12 3.14 3. x");
		assertPair(scanner, Token.ID, "lower_name");
		assertPair(scanner, Token.VAR, "A1");
		assertPair(scanner, Token.VAR, "_Tail");
		assertToken(scanner, Token.ANONYMOUS_VAR);
		assertPair(scanner, Token.NUM, "0");
		assertPair(scanner, Token.NUM, "12");
		assertPair(scanner, Token.NUM, "3.14");
		assertPair(scanner, Token.NUM, "3");
		assertToken(scanner, Token.DOT);
		assertPair(scanner, Token.ID, "x");
		assertToken(scanner, Token.DONE);
	}

	@Test
	void recognizesCommentsQueriesDivisionAndLineNumbers() throws IOException {
		ScannerLp scanner = scanner("""
				% ordinary comment
				%query:p(i).
				/* block
				comment */q/a.
				""");
		assertToken(scanner, Token.MODE);
		assertPair(scanner, Token.ID, "p");
		assertToken(scanner, Token.OPEN_PAR);
		assertPair(scanner, Token.ID, "i");
		assertToken(scanner, Token.CLOSE_PAR);
		assertToken(scanner, Token.DOT);
		assertPair(scanner, Token.ID, "q");
		assertPair(scanner, Token.DIV, '/');
		assertPair(scanner, Token.ID, "a");
		assertToken(scanner, Token.DOT);
		assertToken(scanner, Token.DONE);
		assertEquals(5, scanner.getLineno());
	}

	@Test
	void doesNotAdvanceLineForLineCommentEndingAtEndOfInput() throws IOException {
		ScannerLp scanner = scanner("% comment");
		assertToken(scanner, Token.DONE);
		assertEquals(1, scanner.getLineno());
	}

	@Test
	void countsLineCommentEndingsOnce() throws IOException {
		ScannerLp scanner = scanner("% lf\nx% cr\ry% crlf\r\nz");
		assertPair(scanner, Token.ID, "x");
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "y");
		assertEquals(3, scanner.getLineno());
		assertPair(scanner, Token.ID, "z");
		assertEquals(4, scanner.getLineno());
		assertToken(scanner, Token.DONE);
		assertEquals(4, scanner.getLineno());
	}

	@Test
	void countsWhitespaceQueryAndBlockCommentEndingsOnce() throws IOException {
		ScannerLp scanner = scanner("a\r\n%query:\r\nb/* one\r\ntwo\rthree\n*/c");
		assertPair(scanner, Token.ID, "a");
		assertEquals(1, scanner.getLineno());
		assertToken(scanner, Token.MODE);
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "b");
		assertEquals(3, scanner.getLineno());
		assertPair(scanner, Token.ID, "c");
		assertEquals(6, scanner.getLineno());
		assertToken(scanner, Token.DONE);
		assertEquals(6, scanner.getLineno());
	}

	@Test
	void recognizesBlockCommentEndingAfterConsecutiveStars() throws IOException {
		ScannerLp scanner = scanner("/***/x");
		assertPair(scanner, Token.ID, "x");
		assertToken(scanner, Token.DONE);
	}

	@Test
	void recognizesPunctuationAndOperatorAttributes() throws IOException {
		ScannerLp scanner = scanner("()[],.|=+-*/:-");
		assertToken(scanner, Token.OPEN_PAR);
		assertToken(scanner, Token.CLOSE_PAR);
		assertToken(scanner, Token.OPEN_SQ_PAR);
		assertToken(scanner, Token.CLOSE_SQ_PAR);
		assertToken(scanner, Token.COMMA);
		assertToken(scanner, Token.DOT);
		assertToken(scanner, Token.PIPE);
		assertToken(scanner, Token.EQ);
		assertPair(scanner, Token.PLUS, '+');
		assertPair(scanner, Token.MINUS, '-');
		assertPair(scanner, Token.TIMES, '*');
		assertPair(scanner, Token.DIV, '/');
		assertToken(scanner, Token.ARROW);
		assertToken(scanner, Token.DONE);
	}

	@Test
	void rejectsUnknownCharactersAndUnterminatedComments() throws IOException {
		ScannerLp unknownCharacterScanner = scanner("@");
		LexicalException unknownCharacter =
				assertThrows(LexicalException.class, unknownCharacterScanner::nextToken);
		assertEquals(1, unknownCharacter.getLineNumber());

		ScannerLp malformedArrowScanner = scanner(":x");
		LexicalException malformedArrow =
				assertThrows(LexicalException.class, malformedArrowScanner::nextToken);
		assertEquals(1, malformedArrow.getLineNumber());

		ScannerLp unterminatedCommentScanner = scanner("/* comment");
		LexicalException exception =
				assertThrows(LexicalException.class, unterminatedCommentScanner::nextToken);
		assertEquals("non-ended comment at line 1", exception.getMessage());
		assertEquals(1, exception.getLineNumber());
	}

	private static ScannerLp scanner(String source) {
		return new ScannerLp(new BufferedReader(new StringReader(source)));
	}

	private static void assertToken(ScannerLp scanner, Token expectedToken) throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertNull(pair.attribute());
	}

	private static void assertPair(ScannerLp scanner, Token expectedToken, Object expectedAttribute)
			throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertEquals(expectedAttribute, pair.attribute());
	}
}
