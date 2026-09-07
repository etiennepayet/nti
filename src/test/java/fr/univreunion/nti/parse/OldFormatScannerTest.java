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

package fr.univreunion.nti.parse;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.srs.ScannerSrs;
import fr.univreunion.nti.parse.trs.ScannerTrs;

class OldFormatScannerTest {

	@Test
	void recognizesTrsKeywordsIdentifiersAndPunctuation() throws IOException {
		ScannerTrs scanner = trsScanner("(VAR x) (RULES f(x) -> x) STRATEGY INNERMOST OUTERMOST");

		assertToken(scanner, Token.OPEN_PAR);
		assertPair(scanner, Token.VAR, "VAR");
		assertPair(scanner, Token.ID, "x");
		assertToken(scanner, Token.CLOSE_PAR);
		assertToken(scanner, Token.OPEN_PAR);
		assertPair(scanner, Token.RULES, "RULES");
		assertPair(scanner, Token.ID, "f");
		assertToken(scanner, Token.OPEN_PAR);
		assertPair(scanner, Token.ID, "x");
		assertToken(scanner, Token.CLOSE_PAR);
		assertPair(scanner, Token.ARROW, "->");
		assertPair(scanner, Token.ID, "x");
		assertToken(scanner, Token.CLOSE_PAR);
		assertPair(scanner, Token.STRATEGY, "STRATEGY");
		assertPair(scanner, Token.INNERMOST, "INNERMOST");
		assertPair(scanner, Token.OUTERMOST, "OUTERMOST");
		assertToken(scanner, Token.DONE);
	}

	@Test
	void usesTheKeywordsSpecificToEachFormat() throws IOException {
		ScannerSrs srsScanner = srsScanner("LEFTMOST RIGHTMOST INNERMOST VAR");
		assertPair(srsScanner, Token.LEFTMOST, "LEFTMOST");
		assertPair(srsScanner, Token.RIGHTMOST, "RIGHTMOST");
		assertPair(srsScanner, Token.ID, "INNERMOST");
		assertPair(srsScanner, Token.ID, "VAR");

		ScannerTrs trsScanner = trsScanner("LEFTMOST RIGHTMOST INNERMOST VAR");
		assertPair(trsScanner, Token.ID, "LEFTMOST");
		assertPair(trsScanner, Token.ID, "RIGHTMOST");
		assertPair(trsScanner, Token.INNERMOST, "INNERMOST");
		assertPair(trsScanner, Token.VAR, "VAR");
	}

	@Test
	void ignoresQuotedStringContentsAndCountsTheirLines() throws IOException {
		ScannerSrs scanner = srsScanner("\"ignored, (text)\ncontinued\" word");

		assertToken(scanner, Token.STRING);
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "word");
	}

	@Test
	void countsLfCrAndCrLfLineEndingsOnce() throws IOException {
		ScannerTrs scanner = trsScanner("a\nb\rc\r\nd");

		assertPair(scanner, Token.ID, "a");
		assertPair(scanner, Token.ID, "b");
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "c");
		assertEquals(3, scanner.getLineno());
		assertPair(scanner, Token.ID, "d");
		assertEquals(4, scanner.getLineno());
	}

	@Test
	void reportsUnterminatedStringsAsLexicalErrors() {
		ScannerSrs scanner = srsScanner("\"unterminated");

		LexicalException exception = assertThrows(LexicalException.class, scanner::nextToken);
		assertEquals("non-ended string at line 1", exception.getMessage());
		assertEquals(1, exception.getLineNumber());
	}

	private static ScannerSrs srsScanner(String source) {
		return new ScannerSrs(new BufferedReader(new StringReader(source)));
	}

	private static ScannerTrs trsScanner(String source) {
		return new ScannerTrs(new BufferedReader(new StringReader(source)));
	}

	private static void assertToken(Scanner scanner, Token expectedToken) throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertNull(pair.attribute());
	}

	private static void assertPair(Scanner scanner, Token expectedToken, Object expectedAttribute)
			throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertEquals(expectedAttribute, pair.attribute());
	}
}
