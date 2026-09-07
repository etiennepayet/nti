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
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.LexicalException;
import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Token;

class ScannerAriTest {

	@Test
	void recognizesKeywordsIdentifiersIntegersAndParentheses() throws IOException {
		ScannerAri scanner = scanner("(format TRS) (fun f-name 12) (rule x x)");

		assertToken(scanner, Token.OPEN_PAR);
		assertPair(scanner, Token.FORMAT, "format");
		assertPair(scanner, Token.TRS, "TRS");
		assertToken(scanner, Token.CLOSE_PAR);
		assertToken(scanner, Token.OPEN_PAR);
		assertPair(scanner, Token.FUN, "fun");
		assertPair(scanner, Token.ID, "f-name");
		assertPair(scanner, Token.INT, 12);
		assertToken(scanner, Token.CLOSE_PAR);
		assertToken(scanner, Token.OPEN_PAR);
		assertPair(scanner, Token.RULE, "rule");
		assertPair(scanner, Token.ID, "x");
		assertPair(scanner, Token.ID, "x");
		assertToken(scanner, Token.CLOSE_PAR);
		assertToken(scanner, Token.DONE);
	}

	@Test
	void preservesQuotedIdentifiersAndSkipsComments() throws IOException {
		ScannerAri scanner = scanner("; first comment\n|format| ; second comment\n|0|");

		assertPair(scanner, Token.ID, "|format|");
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "|0|");
		assertEquals(3, scanner.getLineno());
		assertToken(scanner, Token.DONE);
	}

	@Test
	void doesNotAdvanceLineForCommentEndingAtEndOfInput() throws IOException {
		ScannerAri scanner = scanner("; comment");

		assertToken(scanner, Token.DONE);
		assertEquals(1, scanner.getLineno());
	}

	@Test
	void countsLfCrAndCrLfLineEndingsOnce() throws IOException {
		ScannerAri scanner = scanner("a\nb\rc\r\nd");

		assertPair(scanner, Token.ID, "a");
		assertPair(scanner, Token.ID, "b");
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "c");
		assertEquals(3, scanner.getLineno());
		assertPair(scanner, Token.ID, "d");
		assertEquals(4, scanner.getLineno());
	}

	@Test
	void reportsMalformedQuotedIdentifiers() {
		ScannerAri emptyQuotedIdentifierScanner = scanner("||");
		LexicalException quotedIdentifierError = assertThrows(
				LexicalException.class, emptyQuotedIdentifierScanner::nextToken);
		assertEquals("ill-formed quoted identifier around line 1",
				quotedIdentifierError.getMessage());
		assertEquals(1, quotedIdentifierError.getLineNumber());

		ScannerAri unterminatedIdentifierScanner = scanner("|identifier");
		LexicalException unterminatedIdentifierError = assertThrows(
				LexicalException.class, unterminatedIdentifierScanner::nextToken);
		assertEquals(1, unterminatedIdentifierError.getLineNumber());
	}

	private static ScannerAri scanner(String source) {
		return new ScannerAri(new BufferedReader(new StringReader(source)));
	}

	private static void assertToken(ScannerAri scanner, Token expectedToken) throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertNull(pair.attribute());
	}

	private static void assertPair(ScannerAri scanner, Token expectedToken, Object expectedAttribute)
			throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertEquals(expectedAttribute, pair.attribute());
	}
}
