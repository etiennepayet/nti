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

package fr.univreunion.nti.parse.xml;

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

class ScannerXmlTest {

	@Test
	void recognizesProcessingInstructionsAndStructuralTags() throws IOException {
		ScannerXml scanner = scanner("""
				<?xml version="1.0"?>
				<?xml-stylesheet type="text/xsl"?>
				<problem type="termination"></problem>
				<trs></trs><rules></rules><rule></rule><lhs></lhs><rhs></rhs>
				<var></var><funapp></funapp><name></name><arg></arg>
				<signature></signature><funcsym></funcsym><arity></arity>
				<strategy></strategy><metainformation></metainformation>
				<originalfilename></originalfilename><author></author>
				<date></date><comment></comment>
				""");

		Token[] expectedTokens = {
				Token.XML_TAG, Token.XML_STYLESHEET_TAG,
				Token.OPEN_PROBLEM_TAG, Token.CLOSE_PROBLEM_TAG,
				Token.OPEN_TRS_TAG, Token.CLOSE_TRS_TAG,
				Token.OPEN_RULES_TAG, Token.CLOSE_RULES_TAG,
				Token.OPEN_RULE_TAG, Token.CLOSE_RULE_TAG,
				Token.OPEN_LHS_TAG, Token.CLOSE_LHS_TAG,
				Token.OPEN_RHS_TAG, Token.CLOSE_RHS_TAG,
				Token.OPEN_VAR_TAG, Token.CLOSE_VAR_TAG,
				Token.OPEN_FUNAPP_TAG, Token.CLOSE_FUNAPP_TAG,
				Token.OPEN_NAME_TAG, Token.CLOSE_NAME_TAG,
				Token.OPEN_ARG_TAG, Token.CLOSE_ARG_TAG,
				Token.OPEN_SIGN_TAG, Token.CLOSE_SIGN_TAG,
				Token.OPEN_FUNCSYM_TAG, Token.CLOSE_FUNCSYM_TAG,
				Token.OPEN_ARITY_TAG, Token.CLOSE_ARITY_TAG,
				Token.OPEN_STRATEGY_TAG, Token.CLOSE_STRATEGY_TAG,
				Token.OPEN_METAINFO_TAG, Token.CLOSE_METAINFO_TAG,
				Token.OPEN_FILENAME_TAG, Token.CLOSE_FILENAME_TAG,
				Token.OPEN_AUTHOR_TAG, Token.CLOSE_AUTHOR_TAG,
				Token.OPEN_DATE_TAG, Token.CLOSE_DATE_TAG,
				Token.OPEN_COMMENT_TAG, Token.CLOSE_COMMENT_TAG,
				Token.DONE
		};

		for (Token expectedToken : expectedTokens) assertToken(scanner, expectedToken);
	}

	@Test
	void readsTextAsIdentifiers() throws IOException {
		ScannerXml scanner = scanner("f/2 FULL file.xml");

		assertPair(scanner, Token.ID, "f/2");
		assertPair(scanner, Token.ID, "FULL");
		assertPair(scanner, Token.ID, "file.xml");
		assertToken(scanner, Token.DONE);
	}

	@Test
	void skipsMultilineCommentsContainingClosingTagCharacters() throws IOException {
		ScannerXml scanner = scanner("<!-- first >\r\nsecond -->\n<problem>");

		assertToken(scanner, Token.OPEN_PROBLEM_TAG);
		assertEquals(3, scanner.getLineno());
	}

	@Test
	void countsLfCrAndCrLfLineEndingsOnce() throws IOException {
		ScannerXml scanner = scanner("a\nb\rc\r\nd");

		assertPair(scanner, Token.ID, "a");
		assertPair(scanner, Token.ID, "b");
		assertEquals(2, scanner.getLineno());
		assertPair(scanner, Token.ID, "c");
		assertEquals(3, scanner.getLineno());
		assertPair(scanner, Token.ID, "d");
		assertEquals(4, scanner.getLineno());
	}

	@Test
	void reportsUnknownAndMalformedTags() {
		ScannerXml unknownTagScanner = scanner("<unknown>");
		LexicalException unknownTag = assertThrows(
				LexicalException.class, unknownTagScanner::nextToken);
		assertEquals("line 1: unknown tag <unknown>", unknownTag.getMessage());
		assertEquals(1, unknownTag.getLineNumber());

		ScannerXml malformedInstructionScanner = scanner("<?xml version=\"1.0\">");
		LexicalException malformedInstruction = assertThrows(
				LexicalException.class, malformedInstructionScanner::nextToken);
		assertEquals("tag '<?xml' not ended by '?>' at line 1",
				malformedInstruction.getMessage());
		assertEquals(1, malformedInstruction.getLineNumber());
	}

	@Test
	void reportsUnterminatedTagsAndCommentsAtEndOfInput() {
		ScannerXml tagScanner = scanner("<problem");
		LexicalException tagError = assertThrows(LexicalException.class, tagScanner::nextToken);
		assertEquals("tag not ended by '>' at line 1", tagError.getMessage());

		ScannerXml commentScanner = scanner("<!-- comment\n");
		LexicalException commentError = assertThrows(
				LexicalException.class, commentScanner::nextToken);
		assertEquals("XML comment not ended by '-->' at line 2", commentError.getMessage());
		assertEquals(2, commentError.getLineNumber());
	}

	private static ScannerXml scanner(String source) {
		return new ScannerXml(new BufferedReader(new StringReader(source)));
	}

	private static void assertToken(ScannerXml scanner, Token expectedToken) throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertNull(pair.attribute());
	}

	private static void assertPair(ScannerXml scanner, Token expectedToken, Object expectedAttribute)
			throws IOException {
		Pair pair = scanner.nextToken();
		assertEquals(expectedToken, pair.token());
		assertEquals(expectedAttribute, pair.attribute());
	}
}
