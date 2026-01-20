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

package fr.univreunion.nti.parse.trs;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.HashMap;

import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;


/**
 * A lexical analyzer for reading files storing
 * Term or String Rewrite Systems in the old, 
 * human readable, format.
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ScannerTrs extends Scanner {

	/**
	 * The keywords of the language used to write SRSs.
	 */
	private final HashMap<String,Token> keywords =
			new HashMap<String,Token>();

	/**
	 * Builds a new lexical analyzer for TRS/SRS
	 * in the old, human readable, format.
	 * 
	 * @param input the input to read
	 */
	public ScannerTrs(BufferedReader input) {
		super(input);
		this.keywords.put("VAR", Token.VAR);
		this.keywords.put("RULES", Token.RULES);
		this.keywords.put("STRATEGY", Token.STRATEGY);
		this.keywords.put("INNERMOST", Token.INNERMOST);
		this.keywords.put("OUTERMOST", Token.OUTERMOST);
		this.keywords.put("->", Token.ARROW);
	}

	/**
	 * Used to switch from the current automaton to the
	 * next one.
	 * 
	 * @return the start state of the next automaton
	 * @throws RuntimeException if a lexical error or a scanner error occurs
	 */
	private int fail() {
		if (this.start == 0) this.start = 3;
		else if (this.start == 3) this.start =  5;
		else if (this.start == 5) this.start =  8;
		else if (this.start == 8) 
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

		while (true)
			// Delimiters:
			if (state == 0) {
				c = this.input.read();
				if (c == -1) return new Pair(Token.DONE);
				else if (isEndOfLine(c)) this.lineno++;
				else if (!isSpace(c)) state = this.fail();
			}
		// Strings:
			else if (state == 3) {
				if (c == '"') state = 4;
				else state = this.fail();
			}
			else if (state == 4) {
				c = this.input.read();
				if (c == -1)
					throw new RuntimeException("non-ended string at line " + this.lineno);
				if (c == '"') return new Pair(Token.STRING);
			}
		// id + keywords:
			else if (state == 5) {
				if (c != ',' && c != '(' && c != ')') {
					lexbuf.append((char)c);
					state = 6;
				}
				else state = this.fail();
			}
			else if (state == 6) {
				this.input.mark(1);
				c = this.input.read();
				if (c != ',' && c != '(' && c != ')' && !isSpace(c)
						&& c != '"' && c != -1)
					lexbuf.append((char)c);
				else state = 7;
			}
			else if (state == 7) {
				this.input.reset();
				String lexeme = lexbuf.toString();
				Token lookahead = keywords.get(lexeme);
				if (lookahead == null)
					lookahead = Token.ID;
				return new Pair(lookahead, lexeme);
			}
		// Other characters:
			else if (state == 8) {
				switch (c) {
				case ',': return new Pair(Token.COMMA);
				case '(': return new Pair(Token.OPEN_PAR);
				case ')': return new Pair(Token.CLOSE_PAR);
				default: throw new RuntimeException("lexical error: unknown character " + (char)c +
						" at line " + this.lineno);
				}
			}
			else
				throw new RuntimeException("scanner error: unknown state " + state +
						" at line " + this.lineno);
	}
}
