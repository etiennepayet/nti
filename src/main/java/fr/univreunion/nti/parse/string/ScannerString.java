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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.parse.string;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;

/**
 * A lexical analyzer for reading strings representing terms.
 * 
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
	 * Used to switch from the current automaton to the
	 * next one.
	 * 
	 * @return the start state of the next automaton
	 * @throws RuntimeException if a lexical error or a scanner error occurs
	 */
	private int fail() {
		if (this.start == 0) this.start = 1;
		else if (this.start == 1) this.start = 4;
		else if (this.start == 4) this.start = 7;
		else if (this.start == 7) this.start = 9;
		else if (this.start == 9) this.start = 11;
		else if (this.start == 11)
			throw new RuntimeException("lexical error at line " +  this.lineno);
		else
			throw new RuntimeException("scanner error at line " +  this.lineno);

		return this.start;
	}

	/**
	 * Reads the next token from the input.
	 * If a problem occurs while reading the input
	 * then an IOException is thrown.
	 * 
	 * @return the token that has been read
	 * @throws IOException
	 */
	public Pair nextToken() throws IOException {
		this.start = 0;

		int c = -1;
		int state = 0;
		StringBuffer lexbuf = new StringBuffer();

		while (true) {
			// Delimiters:
			if (state == 0) {
				c = this.input.read();
				if (c == -1) return new Pair(Token.DONE);
				else if (isEndOfLine(c)) this.lineno++;
				else if (!isSpace(c)) state = this.fail();
			}
			// Identifiers + variables:
			else if (state == 1) {
				if (Character.isLetter(c) || c == '_') {
					lexbuf.append((char)c);
					state = 2;
				}
				else state = this.fail();
			}
			else if (state == 2) {
				this.input.mark(1);
				c = this.input.read();
				if (Character.isLetterOrDigit(c) || c == '_') 
					lexbuf.append((char)c);
				else state = 3;
			}
			else if (state == 3) {
				this.input.reset();
				String lexeme = lexbuf.toString();
				if ("_".equals(lexeme))
					return new Pair(Token.ANONYMOUS_VAR);
				else if (lexeme.startsWith("_") || Character.isUpperCase(lexeme.charAt(0)))
					return new Pair(Token.VAR, lexeme);
				return new Pair(Token.ID, lexeme);
			}
			// Positive integers:
			else if (state == 4) {
				if (Character.isDigit(c)) {
					lexbuf.append((char)c);
					state = 5;
				}
				else state = this.fail();
			}
			else if (state == 5) {
				this.input.mark(1);
				c = this.input.read();
				if (Character.isDigit(c)) lexbuf.append((char)c);
				else state = 6;
			}
			else if (state == 6) {
				this.input.reset();
				return new Pair(Token.INT, lexbuf.toString());
			}
			// Arrow ('->') and minus ('-'):
			else if (state == 7) {
				if (c == '-') state = 8;
				else state = this.fail();
			}
			else if (state == 8) {
				this.input.mark(1);
				c = this.input.read();
				if (c == '>') return new Pair(Token.ARROW);
				else {
					this.input.reset();
					return new Pair(Token.MINUS, '-');
				}
			}
			// LP arrow (':-'):
			else if (state == 9) {
				if (c == ':') state = 10;
				else state = this.fail();
			}
			else if (state == 10) {
				c = this.input.read();
				if (c == '-') return new Pair(Token.LPARROW);
				else throw new RuntimeException("lexical error: unknown sequence ':" + c +
						"' at line " + this.lineno);
			}
			// Other characters:
			else if (state == 11) {
				switch (c) {
				case '(': return new Pair(Token.OPEN_PAR);
				case ')': return new Pair(Token.CLOSE_PAR);
				case '[': return new Pair(Token.OPEN_SQ_PAR);
				case ']': return new Pair(Token.CLOSE_SQ_PAR);
				case '{': return new Pair(Token.OPEN_BRACE);
				case '}': return new Pair(Token.CLOSE_BRACE);
				case ',': return new Pair(Token.COMMA);
				case '.': return new Pair(Token.DOT);
				case '|': return new Pair(Token.PIPE);
				case '=': return new Pair(Token.EQ);
				case '+': return new Pair(Token.PLUS, '+');
				case '*': return new Pair(Token.TIMES, '*');
				case '/': return new Pair(Token.DIV, '/');
				default: throw new RuntimeException("lexical error: unknown character " + (char)c +
						" at line " + this.lineno);
				}
			}
			else
				throw new RuntimeException("scanner error: unknown state " + state +
						" at line " + this.lineno);
		}
	}
}

