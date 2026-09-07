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

package fr.univreunion.nti.parse.ari;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.Map;

import fr.univreunion.nti.parse.LexicalException;
import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;

/**
 * A lexical analyzer for reading files storing Term or String Rewrite Systems
 * in the <A HREF="https://termination-portal.org/wiki/Term_Rewriting">ARI</A>
 * format.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ScannerAri extends Scanner {

	/**
	 * The keywords of the language used to write TRSs/SRSs.
	 */
	private static final Map<String, Token> KEYWORDS = Map.of(
			"format", Token.FORMAT,
			"fun", Token.FUN,
			"rule", Token.RULE,
			"TRS", Token.TRS);

	/**
	 * Builds a new lexical analyzer for TRSs/SRSs
	 * in the ARI format.
	 *
	 * @param input the input to read
	 */
	public ScannerAri(BufferedReader input) {
		super(input);
	}

	/**
	 * Returns {@code true} iff the provided
	 * character is allowed in identifiers.
	 *
	 * @param character a character
	 * @return {@code true} iff {@code character}
	 * is allowed in identifiers
	 */
	private static boolean isAllowedInIdentifier(int character) {
		return !isSpace(character)
				&& character != '('
				&& character != ')'
				&& character != ';'
				&& character != '|'
				&& character != -1;
	}

	/**
	 * Reads the next token from the input.
	 * If a problem occurs while reading the input
	 * then an IOException is thrown.
	 *
	 * @return the token that has been read
	 */
	@Override
	public Pair nextToken() throws IOException {
		int character = this.readNextSignificantCharacter();
		if (character == -1) {
			return new Pair(Token.DONE);
		}
		if (Character.isDigit((char) character)) {
			return this.readInteger(character);
		}
		if (character == '|') {
			return this.readQuotedIdentifier();
		}
		if (isAllowedInIdentifier(character)) {
			return this.readIdentifierOrKeyword(character);
		}

		return switch (character) {
			case '(' -> new Pair(Token.OPEN_PAR);
			case ')' -> new Pair(Token.CLOSE_PAR);
			default -> throw new LexicalException(
					"lexical error: unknown character " + (char) character
							+ " at line " + this.lineno,
					this.lineno);
		};
	}

	/**
	 * Reads past spaces and comments.
	 *
	 * @return the first significant character, or {@code -1} at end of input
	 */
	private int readNextSignificantCharacter() throws IOException {
		while (true) {
			int character = this.input.read();
			if (character == -1) {
				return -1;
			}
			if (character == ';') {
				if (!this.skipLineComment()) {
					return -1;
				}
				this.lineno++;
			}
			else if (character == '\r') {
				this.input.mark(1);
				if (this.input.read() != '\n') {
					this.input.reset();
				}
				this.lineno++;
			}
			else if (character == '\n') {
				this.lineno++;
			}
			else if (!isSpace(character)) {
				return character;
			}
		}
	}

	/**
	 * Reads a comment up to its line ending.
	 *
	 * @return {@code true} if the comment ends with a line ending, or
	 * {@code false} if it ends at end of input
	 */
	private boolean skipLineComment() throws IOException {
		int character;
		while ((character = this.input.read()) != -1) {
			if (character == '\n') {
				return true;
			}
			if (character == '\r') {
				this.input.mark(1);
				if (this.input.read() != '\n') {
					this.input.reset();
				}
				return true;
			}
		}
		return false;
	}

	/**
	 * Reads a positive integer.
	 *
	 * @param firstCharacter the first digit
	 * @return the corresponding integer token
	 */
	private Pair readInteger(int firstCharacter) throws IOException {
		StringBuilder lexeme = new StringBuilder();
		int character = firstCharacter;
		do {
			lexeme.append((char) character);
			this.input.mark(1);
			character = this.input.read();
		}
		while (Character.isDigit((char) character));
		this.input.reset();
		return new Pair(Token.INT, Integer.valueOf(lexeme.toString()));
	}

	/**
	 * Reads a non-empty identifier enclosed in vertical bars.
	 *
	 * @return the corresponding identifier token
	 */
	private Pair readQuotedIdentifier() throws IOException {
		StringBuilder lexeme = new StringBuilder("|");
		int character = this.input.read();
		while (isAllowedInIdentifier(character)) {
			lexeme.append((char) character);
			character = this.input.read();
		}
		if (character != '|' || lexeme.length() == 1) {
			throw new LexicalException(
					"ill-formed quoted identifier around line " + this.lineno,
					this.lineno);
		}
		lexeme.append('|');
		return new Pair(Token.ID, lexeme.toString());
	}

	/**
	 * Reads an unquoted identifier or a keyword.
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
		while (isAllowedInIdentifier(character));
		this.input.reset();

		String value = lexeme.toString();
		return new Pair(KEYWORDS.getOrDefault(value, Token.ID), value);
	}
}
