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

package fr.univreunion.nti.parse.lp;

import java.io.BufferedReader;
import java.io.IOException;

import fr.univreunion.nti.parse.LexicalException;
import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;

/**
 * A lexical analyzer for reading files storing logic programs (LP).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ScannerLp extends Scanner {
	private static final String QUERY_DIRECTIVE = "query:";

	/**
	 * Builds a new lexical analyzer for LPs.
	 * 
	 * @param input the input to read
	 */
	public ScannerLp(BufferedReader input) {
		super(input);
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

			Pair pair = this.scanTokenStartingWith(character);
			if (pair != null)
				return pair;
		}
	}

	/**
	 * Reads a token whose first non-space character has already been consumed.
	 * A {@code null} result means that a comment was skipped and scanning must
	 * continue.
	 *
	 * @param firstCharacter the first character of the token
	 * @return the token read, or {@code null} after a skipped comment
	 */
	private Pair scanTokenStartingWith(int firstCharacter) throws IOException {
		if (firstCharacter == '%')
			return this.scanLineCommentOrMode();
		if (firstCharacter == '/')
			return this.scanDivisionOrComment();
		if (Character.isLetter(firstCharacter) || firstCharacter == '_')
			return this.scanIdentifier(firstCharacter);
		if (Character.isDigit(firstCharacter))
			return this.scanNumber(firstCharacter);
		if (firstCharacter == ':')
			return this.scanArrow();
		return this.scanPunctuation(firstCharacter);
	}

	/**
	 * Reads either the {@code %query:} marker or an ordinary line comment.
	 *
	 * @return the mode token, or {@code null} after a skipped comment
	 */
	private Pair scanLineCommentOrMode() throws IOException {
		this.input.mark(QUERY_DIRECTIVE.length());
		char[] directive = new char[QUERY_DIRECTIVE.length()];
		if (this.input.read(directive) == directive.length
				&& QUERY_DIRECTIVE.equals(new String(directive)))
			return new Pair(Token.MODE);

		this.input.reset();
		this.skipLineComment();
		return null;
	}

	/**
	 * Skips an ordinary line comment and consumes its line ending, if any.
	 */
	private void skipLineComment() throws IOException {
		int character;
		while ((character = this.input.read()) != -1) {
			if (isEndOfLine(character)) {
				this.countLineEnding(character);
				return;
			}
		}
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

	/**
	 * Reads either the division operator or a block comment.
	 *
	 * @return the division token, or {@code null} after a skipped comment
	 */
	private Pair scanDivisionOrComment() throws IOException {
		this.input.mark(1);
		int nextCharacter = this.input.read();
		if (nextCharacter != '*') {
			this.input.reset();
			return new Pair(Token.DIV, '/');
		}

		this.skipBlockComment();
		return null;
	}

	/**
	 * Skips the remainder of a block comment.
	 */
	private void skipBlockComment() throws IOException {
		boolean previousCharacterWasStar = false;
		while (true) {
			int character = this.input.read();
			if (character == -1)
				throw new LexicalException("non-ended comment at line " + this.lineno, this.lineno);
			if (previousCharacterWasStar && character == '/')
				return;
			previousCharacterWasStar = character == '*';
			if (isEndOfLine(character))
				this.countLineEnding(character);
		}
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
	 * Reads a non-negative integer or decimal number.
	 *
	 * @param firstDigit the first digit of the lexeme
	 * @return the number token read
	 */
	private Pair scanNumber(int firstDigit) throws IOException {
		StringBuilder lexemeBuilder = new StringBuilder();
		lexemeBuilder.append((char) firstDigit);

		while (true) {
			this.input.mark(2);
			int character = this.input.read();
			if (Character.isDigit(character)) {
				lexemeBuilder.append((char) character);
				continue;
			}
			if (character == '.' && this.appendFirstDecimalDigit(lexemeBuilder))
				return this.scanRemainingDecimalDigits(lexemeBuilder);

			this.input.reset();
			return new Pair(Token.NUM, lexemeBuilder.toString());
		}
	}

	/**
	 * Appends a decimal point and the following digit, when present.
	 *
	 * @param lexemeBuilder the number lexeme being built
	 * @return {@code true} if a first decimal digit was read
	 */
	private boolean appendFirstDecimalDigit(StringBuilder lexemeBuilder) throws IOException {
		int firstDecimalDigit = this.input.read();
		if (!Character.isDigit(firstDecimalDigit))
			return false;
		lexemeBuilder.append('.');
		lexemeBuilder.append((char) firstDecimalDigit);
		return true;
	}

	/**
	 * Reads the remaining digits of a decimal number.
	 *
	 * @param lexemeBuilder the number lexeme being built
	 * @return the number token read
	 */
	private Pair scanRemainingDecimalDigits(StringBuilder lexemeBuilder) throws IOException {
		while (true) {
			this.input.mark(1);
			int character = this.input.read();
			if (!Character.isDigit(character)) {
				this.input.reset();
				return new Pair(Token.NUM, lexemeBuilder.toString());
			}
			lexemeBuilder.append((char) character);
		}
	}

	/**
	 * Reads the second character of the {@code :-} arrow.
	 *
	 * @return the arrow token
	 */
	private Pair scanArrow() throws IOException {
		int secondCharacter = this.input.read();
		if (secondCharacter == '-')
			return new Pair(Token.ARROW);
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
			case ',' -> new Pair(Token.COMMA);
			case '.' -> new Pair(Token.DOT);
			case '|' -> new Pair(Token.PIPE);
			case '=' -> new Pair(Token.EQ);
			case '+' -> new Pair(Token.PLUS, '+');
			case '-' -> new Pair(Token.MINUS, '-');
			case '*' -> new Pair(Token.TIMES, '*');
			default -> throw new LexicalException("lexical error: unknown character " + (char) character
					+ " at line " + this.lineno, this.lineno);
		};
	}
}
