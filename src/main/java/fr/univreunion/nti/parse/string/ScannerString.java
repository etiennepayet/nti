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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.parse.string;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import fr.univreunion.nti.parse.LexicalException;
import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;

/**
 * A lexical analyzer for reading strings representing terms.
 * Mainly used for testing.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ScannerString extends Scanner {

	/**
	 * Builds a new lexical analyzer for
	 * terms given as strings.
	 *
	 * @param input the input string to read
	 */
	public ScannerString(String input) {
		super(new BufferedReader(new StringReader(input)));
	}

	/**
	 * Reads the next token from the input.
	 * If a problem occurs while reading the input
	 * then an IOException is thrown.
	 * Invalid lexemes are reported as lexical exceptions.
	 *
	 * @return the token that has been read
	 */
	@Override
	public Pair nextToken() throws IOException {
		while (true) {
			int character = this.input.read();
			if (character == -1)
				return new Pair(Token.DONE);
			if (isSpace(character)) {
				if (isEndOfLine(character))
					this.countLineEnding(character);
				continue;
			}

			return this.scanTokenStartingWith(character);
		}
	}

	/**
	 * Reads a token whose first non-space character has already been consumed.
	 *
	 * @param firstCharacter the first character of the token
	 * @return the token read
	 */
	private Pair scanTokenStartingWith(int firstCharacter) throws IOException {
		if (Character.isLetter(firstCharacter) || firstCharacter == '_')
			return this.scanIdentifier(firstCharacter);
		if (Character.isDigit(firstCharacter))
			return this.scanInteger(firstCharacter);
		if (firstCharacter == '-')
			return this.scanArrowOrMinus();
		if (firstCharacter == ':')
			return this.scanLpArrow();
		return this.scanPunctuation(firstCharacter);
	}

	/**
	 * Reads an identifier, named variable or anonymous variable.
	 *
	 * @param firstCharacter the first character of the lexeme
	 * @return the token read
	 */
	private Pair scanIdentifier(int firstCharacter) throws IOException {
		StringBuilder lexemeBuilder = new StringBuilder();
		lexemeBuilder.append((char) firstCharacter);

		while (true) {
			this.input.mark(1);
			int character = this.input.read();
			if (!Character.isLetterOrDigit(character) && character != '_') {
				this.input.reset();
				break;
			}
			lexemeBuilder.append((char) character);
		}

		String lexeme = lexemeBuilder.toString();
		if ("_".equals(lexeme))
			return new Pair(Token.ANONYMOUS_VAR);
		if (lexeme.startsWith("_") || Character.isUpperCase(lexeme.charAt(0)))
			return new Pair(Token.VAR, lexeme);
		return new Pair(Token.ID, lexeme);
	}

	/**
	 * Reads a non-negative integer.
	 *
	 * @param firstDigit the first digit of the lexeme
	 * @return the integer token read
	 */
	private Pair scanInteger(int firstDigit) throws IOException {
		StringBuilder lexemeBuilder = new StringBuilder();
		lexemeBuilder.append((char) firstDigit);

		while (true) {
			this.input.mark(1);
			int character = this.input.read();
			if (!Character.isDigit(character)) {
				this.input.reset();
				return new Pair(Token.INT, lexemeBuilder.toString());
			}
			lexemeBuilder.append((char) character);
		}
	}

	/**
	 * Reads either the TRS arrow or the minus operator.
	 *
	 * @return the token read
	 */
	private Pair scanArrowOrMinus() throws IOException {
		this.input.mark(1);
		if (this.input.read() == '>')
			return new Pair(Token.ARROW);
		this.input.reset();
		return new Pair(Token.MINUS, '-');
	}

	/**
	 * Reads the second character of the LP arrow.
	 *
	 * @return the LP arrow token
	 */
	private Pair scanLpArrow() throws IOException {
		int secondCharacter = this.input.read();
		if (secondCharacter == '-')
			return new Pair(Token.LPARROW);
		throw new LexicalException("lexical error: unknown sequence ':" + secondCharacter
				+ "' at line " + this.lineno, this.lineno);
	}

	/**
	 * Converts a single-character lexeme to its token.
	 *
	 * @param character the lexeme character
	 * @return the corresponding token
	 */
	private Pair scanPunctuation(int character) {
		return switch (character) {
			case '(' -> new Pair(Token.OPEN_PAR);
			case ')' -> new Pair(Token.CLOSE_PAR);
			case '[' -> new Pair(Token.OPEN_SQ_PAR);
			case ']' -> new Pair(Token.CLOSE_SQ_PAR);
			case '{' -> new Pair(Token.OPEN_BRACE);
			case '}' -> new Pair(Token.CLOSE_BRACE);
			case ',' -> new Pair(Token.COMMA);
			case '.' -> new Pair(Token.DOT);
			case '|' -> new Pair(Token.PIPE);
			case '=' -> new Pair(Token.EQ);
			case '+' -> new Pair(Token.PLUS, '+');
			case '*' -> new Pair(Token.TIMES, '*');
			case '/' -> new Pair(Token.DIV, '/');
			default -> throw new LexicalException("lexical error: unknown character " + (char) character
					+ " at line " + this.lineno, this.lineno);
		};
	}

	/**
	 * Counts a consumed line ending. A carriage-return/line-feed sequence is
	 * consumed and counted as one line ending.
	 *
	 * @param character the already consumed line-ending character
	 */
	private void countLineEnding(int character) throws IOException {
		if (character == '\r')
			this.consumeOptionalLineFeed();
		this.lineno++;
	}

	/**
	 * Consumes the line feed following a carriage return, when present.
	 */
	private void consumeOptionalLineFeed() throws IOException {
		this.input.mark(1);
		if (this.input.read() != '\n')
			this.input.reset();
	}
}
