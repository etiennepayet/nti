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

import java.io.BufferedReader;
import java.io.IOException;

import fr.univreunion.nti.parse.LexicalException;
import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;

/**
 * A lexical analyzer for reading files storing
 * Term or String Rewrite Systems in the XML format.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class ScannerXml extends Scanner {

	/**
	 * The supported opening-tag prefixes and their corresponding tokens.
	 * Frequently occurring term tags come first because the definitions are
	 * searched sequentially.
	 */
	private static final TagDefinition[] OPEN_TAGS = {
			new TagDefinition("<funapp", Token.OPEN_FUNAPP_TAG),
			new TagDefinition("<name", Token.OPEN_NAME_TAG),
			new TagDefinition("<arg", Token.OPEN_ARG_TAG),
			new TagDefinition("<var", Token.OPEN_VAR_TAG),
			new TagDefinition("<problem", Token.OPEN_PROBLEM_TAG),
			new TagDefinition("<trs", Token.OPEN_TRS_TAG),
			new TagDefinition("<rules", Token.OPEN_RULES_TAG),
			new TagDefinition("<rule", Token.OPEN_RULE_TAG),
			new TagDefinition("<lhs", Token.OPEN_LHS_TAG),
			new TagDefinition("<rhs", Token.OPEN_RHS_TAG),
			new TagDefinition("<signature", Token.OPEN_SIGN_TAG),
			new TagDefinition("<funcsym", Token.OPEN_FUNCSYM_TAG),
			new TagDefinition("<arity", Token.OPEN_ARITY_TAG),
			new TagDefinition("<strategy", Token.OPEN_STRATEGY_TAG),
			new TagDefinition("<metainformation", Token.OPEN_METAINFO_TAG),
			new TagDefinition("<originalfilename", Token.OPEN_FILENAME_TAG),
			new TagDefinition("<author", Token.OPEN_AUTHOR_TAG),
			new TagDefinition("<date", Token.OPEN_DATE_TAG),
			new TagDefinition("<comment", Token.OPEN_COMMENT_TAG)
	};

	/**
	 * Reusable storage for the tag currently being read.
	 */
	private final StringBuilder tagBuffer = new StringBuilder(64);

	/**
	 * Builds a new lexical analyzer for TRS/SRS
	 * in the XML format.
	 *
	 * @param input the input to read
	 */
	public ScannerXml(BufferedReader input) {
		super(input);
	}

	/**
	 * Reads the next token from the input.
	 * If an input/output or lexical problem occurs, the corresponding exception
	 * is thrown.
	 *
	 * @return the token that has been read
	 */
	@Override
	public Pair nextToken() throws IOException {
		while (true) {
			int c = this.readNextNonSpace();
			if (c == -1) return new Pair(Token.DONE);

			if (c != '<') return this.readIdentifier(c);

			String tag = this.readTag();
			if (!tag.startsWith("<!--")) return this.toToken(tag);
		}
	}

	/**
	 * Reads the next non-space character, updating the current line number.
	 *
	 * @return the next non-space character, or {@code -1} at the end of the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private int readNextNonSpace() throws IOException {
		int c;
		while ((c = this.input.read()) != -1 && isSpace(c))
			this.consumeLineEnding(c);
		return c;
	}

	/**
	 * Reads an identifier starting with the specified character.
	 *
	 * @param firstCharacter the first character of the identifier
	 * @return the identifier token and its text
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private Pair readIdentifier(int firstCharacter) throws IOException {
		StringBuilder identifier = new StringBuilder().append((char) firstCharacter);

		while (true) {
			this.input.mark(1);
			int c = this.input.read();
			if (c == -1 || c == '<' || isSpace(c)) {
				this.input.reset();
				return new Pair(Token.ID, identifier.toString());
			}
			identifier.append((char) c);
		}
	}

	/**
	 * Reads a tag or an XML comment. Whitespace inside a tag is normalized to a
	 * space, as in the original scanner.
	 *
	 * @return the tag or comment text, including its delimiters
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws LexicalException if the tag or comment is not terminated
	 */
	private String readTag() throws IOException {
		StringBuilder tag = this.tagBuffer;
		tag.setLength(0);
		tag.append('<');
		boolean comment = false;

		while (true) {
			int c = this.input.read();
			if (c == -1)
				throw this.error(comment
						? "XML comment not ended by '-->' at line " + this.lineno
						: "tag not ended by '>' at line " + this.lineno);

			if (isSpace(c)) {
				tag.append(' ');
				this.consumeLineEnding(c);
			}
			else {
				tag.append((char) c);
			}

			if (tag.length() == 4) comment = "<!--".contentEquals(tag);
			if (comment ? endsComment(tag) : c == '>') return tag.toString();
		}
	}

	/**
	 * Converts a tag lexeme to the token expected by the XML parser.
	 *
	 * @param tag the complete tag lexeme
	 * @return the token corresponding to {@code tag}
	 * @throws LexicalException if the tag is unknown or a processing instruction
	 * is not terminated correctly
	 */
	private Pair toToken(String tag) {
		if ("<?xml?>".equals(tag)) return new Pair(Token.XML_TAG);

		if (tagStartsWith("<?xml", tag))
			return this.processingInstructionToken(tag, "<?xml", Token.XML_TAG);

		if (tagStartsWith("<?xml-stylesheet", tag))
			return this.processingInstructionToken(
					tag, "<?xml-stylesheet", Token.XML_STYLESHEET_TAG);

		Token closingToken = closingToken(tag);
		if (closingToken != null) return new Pair(closingToken);

		for (TagDefinition definition : OPEN_TAGS)
			if (tagStartsWith(definition.prefix(), tag)) return new Pair(definition.token());

		throw this.error("line " + this.lineno + ": unknown tag " + tag);
	}

	/**
	 * Checks and converts an XML processing instruction.
	 *
	 * @param tag the complete processing-instruction lexeme
	 * @param prefix the prefix used to identify the instruction
	 * @param token the token corresponding to the instruction
	 * @return a pair containing {@code token}
	 * @throws LexicalException if the instruction does not end with {@code ?>}
	 */
	private Pair processingInstructionToken(String tag, String prefix, Token token) {
		if (tag.endsWith("?>")) return new Pair(token);
		throw this.error("tag '" + prefix + "' not ended by '?>' at line " + this.lineno);
	}

	/**
	 * Updates the line number for a line-ending character. A CRLF sequence counts
	 * as one line ending.
	 *
	 * @param c the character most recently read
	 * @throws IOException if an I/O error occurs while checking for a CRLF sequence
	 */
	private void consumeLineEnding(int c) throws IOException {
		if (c == '\r') {
			this.input.mark(1);
			if (this.input.read() != '\n') this.input.reset();
		}
		if (isEndOfLine(c)) this.lineno++;
	}

	/**
	 * Creates a lexical exception at the current line.
	 *
	 * @param message the error message
	 * @return the lexical exception
	 */
	private LexicalException error(String message) {
		return new LexicalException(message, this.lineno);
	}

	/**
	 * Checks that the given tag starts with the given prefix followed by a space
	 * or by the closing tag character {@code >}.
	 *
	 * @param prefix the expected tag prefix
	 * @param tag the tag to check
	 * @return {@code true} if {@code tag} starts with the delimited prefix;
	 * {@code false} otherwise
	 */
	private static boolean tagStartsWith(String prefix, String tag) {
		int prefixLength = prefix.length();
		return tag.startsWith(prefix)
				&& prefixLength < tag.length()
				&& (tag.charAt(prefixLength) == '>' || isSpace(tag.charAt(prefixLength)));
	}

	/**
	 * Checks whether the accumulated text ends with an XML comment delimiter.
	 *
	 * @param text the accumulated comment text
	 * @return {@code true} if {@code text} ends with {@code -->};
	 * {@code false} otherwise
	 */
	private static boolean endsComment(StringBuilder text) {
		int length = text.length();
		return length >= 3
				&& text.charAt(length - 3) == '-'
				&& text.charAt(length - 2) == '-'
				&& text.charAt(length - 1) == '>';
	}

	/**
	 * Returns the token corresponding to a closing tag.
	 *
	 * @param tag the complete closing-tag lexeme
	 * @return the corresponding token, or {@code null} if {@code tag} is not a
	 * supported closing tag
	 */
	private static Token closingToken(String tag) {
		return switch (tag) {
			case "</problem>" -> Token.CLOSE_PROBLEM_TAG;
			case "</trs>" -> Token.CLOSE_TRS_TAG;
			case "</rules>" -> Token.CLOSE_RULES_TAG;
			case "</rule>" -> Token.CLOSE_RULE_TAG;
			case "</lhs>" -> Token.CLOSE_LHS_TAG;
			case "</rhs>" -> Token.CLOSE_RHS_TAG;
			case "</var>" -> Token.CLOSE_VAR_TAG;
			case "</funapp>" -> Token.CLOSE_FUNAPP_TAG;
			case "</name>" -> Token.CLOSE_NAME_TAG;
			case "</arg>" -> Token.CLOSE_ARG_TAG;
			case "</signature>" -> Token.CLOSE_SIGN_TAG;
			case "</funcsym>" -> Token.CLOSE_FUNCSYM_TAG;
			case "</arity>" -> Token.CLOSE_ARITY_TAG;
			case "</strategy>" -> Token.CLOSE_STRATEGY_TAG;
			case "</metainformation>" -> Token.CLOSE_METAINFO_TAG;
			case "</originalfilename>" -> Token.CLOSE_FILENAME_TAG;
			case "</author>" -> Token.CLOSE_AUTHOR_TAG;
			case "</date>" -> Token.CLOSE_DATE_TAG;
			case "</comment>" -> Token.CLOSE_COMMENT_TAG;
			default -> null;
		};
	}

	/**
	 * Associates an opening-tag prefix with the token returned by the scanner.
	 *
	 * @param prefix the opening-tag prefix
	 * @param token the corresponding token
	 */
	private record TagDefinition(String prefix, Token token) {}
}
