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

import java.io.BufferedReader;
import java.io.IOException;
import java.util.Map;

/**
 * Shared lexical analyzer for the old human-readable TRS and SRS formats.
 *
 * <p>The two formats use the same lexical rules and differ only in their
 * keywords.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public abstract class OldFormatScanner extends Scanner {

	/**
	 * The keywords recognized by this scanner.
	 */
	private final Map<String, Token> keywords;

	/**
	 * Builds a scanner for an old human-readable format.
	 *
	 * @param input the input to read
	 * @param keywords the keywords recognized by the concrete format
	 */
	protected OldFormatScanner(BufferedReader input, Map<String, Token> keywords) {
		super(input);
		this.keywords = Map.copyOf(keywords);
	}

	/**
	 * Reads the next token from the input.
	 *
	 * @return the token that has been read
	 */
	@Override
	public Pair nextToken() throws IOException {
		int character = this.readNextSignificantCharacter();
		if (character == -1) {
			return new Pair(Token.DONE);
		}
		if (character == '"') {
			return this.readString();
		}

		return switch (character) {
			case ',' -> new Pair(Token.COMMA);
			case '(' -> new Pair(Token.OPEN_PAR);
			case ')' -> new Pair(Token.CLOSE_PAR);
			default -> this.readIdentifierOrKeyword(character);
		};
	}

	/**
	 * Reads past whitespace.
	 *
	 * @return the first non-space character, or {@code -1} at end of input
	 */
	private int readNextSignificantCharacter() throws IOException {
		while (true) {
			int character = this.input.read();
			if (character == -1 || !isSpace(character)) {
				return character;
			}
			this.countLineEnding(character);
		}
	}

	/**
	 * Reads and ignores a quoted string.
	 *
	 * @return a string token
	 */
	private Pair readString() throws IOException {
		int character;
		while ((character = this.input.read()) != '"') {
			if (character == -1) {
				throw new LexicalException(
						"non-ended string at line " + this.lineno,
						this.lineno);
			}
			this.countLineEnding(character);
		}
		return new Pair(Token.STRING);
	}

	/**
	 * Reads an identifier or a keyword.
	 *
	 * @param firstCharacter the first character of the lexeme
	 * @return the corresponding token
	 */
	private Pair readIdentifierOrKeyword(int firstCharacter) throws IOException {
		StringBuilder lexeme = new StringBuilder();
		int character = firstCharacter;
		do {
			lexeme.append((char) character);
			this.input.mark(1);
			character = this.input.read();
		}
		while (isIdentifierCharacter(character));
		this.input.reset();

		String value = lexeme.toString();
		return new Pair(this.keywords.getOrDefault(value, Token.ID), value);
	}

	/**
	 * Indicates whether a character may occur in an identifier.
	 *
	 * @param character the character to inspect
	 * @return {@code true} if the character may occur in an identifier
	 */
	private static boolean isIdentifierCharacter(int character) {
		return character != -1
				&& character != ','
				&& character != '('
				&& character != ')'
				&& character != '"'
				&& !isSpace(character);
	}

	/**
	 * Counts a line ending, consuming the LF following a CR when present.
	 *
	 * @param character the character that has just been read
	 */
	private void countLineEnding(int character) throws IOException {
		if (character == '\r') {
			this.input.mark(1);
			if (this.input.read() != '\n') {
				this.input.reset();
			}
			this.lineno++;
		}
		else if (character == '\n') {
			this.lineno++;
		}
	}
}
