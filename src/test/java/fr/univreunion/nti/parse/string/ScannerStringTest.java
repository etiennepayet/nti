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

package fr.univreunion.nti.parse.string;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.IOException;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.LexicalException;
import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Token;

class ScannerStringTest {

	@Test
	void distinguishesIdentifiersVariablesAnonymousVariablesAndIntegers() throws IOException {
		ScannerString scanner = new ScannerString("lower_name A1 _Tail _ 0 12 34abc");
		assertPair(scanner, Token.ID, "lower_name");
		assertPair(scanner, Token.VAR, "A1");
		assertPair(scanner, Token.VAR, "_Tail");
		assertToken(scanner, Token.ANONYMOUS_VAR);
		assertPair(scanner, Token.INT, "0");
		assertPair(scanner, Token.INT, "12");
		assertPair(scanner, Token.INT, "34");
		assertPair(scanner, Token.ID, "abc");
		assertToken(scanner, Token.DONE);
	}

	@Test
	void recognizesArrowsPunctuationAndOperatorAttributes() throws IOException {
		ScannerString scanner = new ScannerString("-> - :- ()[]{},.|=+*/");
		assertToken(scanner, Token.ARROW);
		assertPair(scanner, Token.MINUS, '-');
		assertToken(scanner, Token.LPARROW);
		assertToken(scanner, Token.OPEN_PAR);
		assertToken(scanner, Token.CLOSE_PAR);
		assertToken(scanner, Token.OPEN_SQ_PAR);
		assertToken(scanner, Token.CLOSE_SQ_PAR);
		assertToken(scanner, Token.OPEN_BRACE);
		assertToken(scanner, Token.CLOSE_BRACE);
		assertToken(scanner, Token.COMMA);
		assertToken(scanner, Token.DOT);
		assertToken(scanner, Token.PIPE);
		assertToken(scanner, Token.EQ);
		assertPair(scanner, Token.PLUS, '+');
		assertPair(scanner, Token.TIMES, '*');
		assertPair(scanner, Token.DIV, '/');
		assertToken(scanner, Token.DONE);
	}

	@Test
	void countsLfCrAndCrLfLineEndingsOnce() throws IOException {
		ScannerString scanner = new ScannerString("a\nb\rc\r\nd");
		assertPair(scanner, Token.ID, "a");
		assertEquals(1, scanner.getLineno());
		assertPair(scanner, Token.ID, "b");
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "c");
		assertEquals(3, scanner.getLineno());
		assertPair(scanner, Token.ID, "d");
		assertEquals(4, scanner.getLineno());
		assertToken(scanner, Token.DONE);
		assertEquals(4, scanner.getLineno());
	}

	@Test
	void reportsUnknownCharactersAndMalformedLpArrows() {
		ScannerString unknownCharacterScanner = new ScannerString("\n@");
		LexicalException unknownCharacter =
				assertThrows(LexicalException.class, unknownCharacterScanner::nextToken);
		assertEquals("lexical error: unknown character @ at line 2", unknownCharacter.getMessage());
		assertEquals(2, unknownCharacter.getLineNumber());

		ScannerString malformedArrowScanner = new ScannerString(":x");
		LexicalException malformedArrow =
				assertThrows(LexicalException.class, malformedArrowScanner::nextToken);
		assertEquals("lexical error: unknown sequence ':120' at line 1", malformedArrow.getMessage());
		assertEquals(1, malformedArrow.getLineNumber());
	}

	private static void assertToken(ScannerString scanner, Token expectedToken) throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertNull(pair.attribute());
	}

	private static void assertPair(ScannerString scanner, Token expectedToken, Object expectedAttribute)
			throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertEquals(expectedAttribute, pair.attribute());
	}
}
