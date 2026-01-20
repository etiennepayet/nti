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

package fr.univreunion.nti.parse.ari;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.HashMap;

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
	private final HashMap<String,Token> keywords =
			new HashMap<String,Token>();

	/**
	 * Builds a new lexical analyzer for TRSs/SRSs
	 * in the ARI format.
	 * 
	 * @param input the input to read
	 */
	public ScannerAri(BufferedReader input) {
		super(input);
		// We initialize the keyword set:
		this.keywords.put("format", Token.FORMAT);
		this.keywords.put("fun", Token.FUN);
		this.keywords.put("rule", Token.RULE);
		this.keywords.put("TRS", Token.TRS);
	}

	/**
	 * Returns <code>true</code> iff the provided
	 * character is allowed in identifiers.
	 * 
	 * @param c a character
	 * @return <code>true</code> iff <code>c</code>
	 * is allowed in identifiers
	 */
	private boolean allowedInIds(int c) {
		return !isSpace(c) &&
				c != '(' && c != ')' &&
				c != ';' &&
				c != '|' &&
				c != -1;
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

		int c = -1;

		// Spaces + comments:
		while (true) {
			c = this.input.read();
			// EOF:
			if (c == -1)
				return new Pair(Token.DONE);
			// Comments:
			if (c == ';') {
				this.input.readLine(); // we ignore comments
				this.lineno++;
			}
			else if (isEndOfLine(c))
				this.lineno++;
			else if (!isSpace(c))
				break;
		}

		// Positive integers:
		if (Character.isDigit((char)c)) {
			StringBuffer lexbuf = new StringBuffer();
			do {
				lexbuf.append((char)c);
				this.input.mark(1);
				c = this.input.read();
			}
			while (Character.isDigit((char)c));
			this.input.reset();
			return new Pair(Token.INT, Integer.valueOf(lexbuf.toString()));
		}

		// Quoted identifiers:
		if (c == '|') {
			StringBuffer lexbuf = new StringBuffer();
			do {
				lexbuf.append((char)c);
				c = this.input.read();
			}
			while (allowedInIds(c));
			if (c != '|' || lexbuf.length() < 2) // quoted identifiers must be non-empty
				throw new RuntimeException("ill-formed quoted identifier around line " + this.lineno);
			lexbuf.append('|');
			// Necessarily, lexeme is not a keyword
			// because keywords do not contain '|'.
			return new Pair(Token.ID, lexbuf.toString());
		}

		// Non-quoted identifiers + keywords:
		if (allowedInIds(c)) {
			StringBuffer lexbuf = new StringBuffer();
			do {
				lexbuf.append((char)c);
				this.input.mark(1);
				c = this.input.read();
			}
			while (allowedInIds(c));
			this.input.reset();
			String lexeme = lexbuf.toString();
			Token lookahead = keywords.get(lexeme);
			if (lookahead == null)
				lookahead = Token.ID;
			return new Pair(lookahead, lexeme);
		}

		// Others:
		switch (c) {
		case '(': return new Pair(Token.OPEN_PAR);
		case ')': return new Pair(Token.CLOSE_PAR);
		default: throw new RuntimeException("lexical error: unknown character " + (char)c +
				" at line " + this.lineno);
		}
	}
}
