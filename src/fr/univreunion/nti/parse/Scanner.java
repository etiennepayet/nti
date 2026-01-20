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

package fr.univreunion.nti.parse;

import java.io.BufferedReader;
import java.io.IOException;

/**
 * A lexical analyzer for reading programs (LP, SRS, TRS, ...)
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class Scanner {
	
	/**
	 * The input for this lexical analyzer.
	 */
	protected final BufferedReader input;

	/**
	 * The starting state of the current finite automaton
	 * to run for lexical analysis.
	 */
	protected int start;

	/**
	 * The current line number in the input.
	 */
	protected int lineno = 1;

	/**
	 * Builds a new lexical analyzer.
	 * 
	 * @param input the input to read
	 */
	public Scanner(BufferedReader input) {
		this.input = input;
	}
	
	/**
	 * Returns the current line number in the input.
	 * 
	 * @return the current line number in the input
	 */
	public int getLineno() {
		return this.lineno;
	}
	
	/**
	 * Indicates whether the given character corresponds
	 * to a space.
	 * 
	 * @param c a character
	 * @return <code>true</code> if <code>c</code> corresponds 
	 * 	to a space and <code>false</code> otherwise
	 */
	public static boolean isSpace(int c) {
		return (
				c == ' '  || // space char
				c == '\n' || // new line
				c == '\t' || // horizontal tab
				c == '\r' || // carriage return 
				c == '\f' || // new page
				c == '\b'    // backspace
		);
	}
	
	/**
	 * Indicates whether the given character corresponds
	 * to an end of line character.
	 * 
	 * @param c a character
	 * @return <code>true</code> if <code>c</code> corresponds 
	 * 	to an end of line character and <code>false</code> otherwise
	 */
	public static boolean isEndOfLine(int c) {
		return (c == '\n' || c == '\r');
	}
	
	/**
	 * Reads the next token from the input.
	 * If a problem occurs while reading the input
	 * then an IOException is thrown.
	 * 
	 * @return the token that has been read
	 * @throws IOException
	 */
	public abstract Pair nextToken() throws IOException;
}
