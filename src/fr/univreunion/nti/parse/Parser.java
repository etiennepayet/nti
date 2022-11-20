/*
 * Copyright 2022 Etienne Payet <etienne.payet at univ-reunion.fr>
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

import java.io.IOException;

import fr.univreunion.nti.program.Program;

/**
 * A parser for programs (LP, SRS, TRS, ...)
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class Parser {

	/**
	 * The scanner which is used for reading the input.
	 */
	protected final Scanner scanner;

	/**
	 * The last pair (token, attribute) returned by the scanner.
	 */
	protected Pair lookahead;

	/**
	 * The name of the program to be built.
	 */
	protected final String progName;

	/**
	 * Builds a parser for programs (LP, SRS, TRS, ...).
	 * 
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public Parser(String progName, Scanner scanner) {
		this.progName = progName;
		this.scanner = scanner;
	}

	/**
	 * Checks that the value of the current lookahead (ie, the
	 * token that has just been read) is equal to the given token.
	 * If this check succeeds, then reads the next token in
	 * the input. Otherwise, a RuntimeException is thrown.
	 * If a problem occurs while reading the input, then
	 * an IOException is thrown.
	 * 
	 * @param token a token to check
	 * @throws RuntimeException
	 * @throws IOException
	 */
	protected void match(Token token) throws IOException {
		if (this.lookahead.getToken() == token)
			this.lookahead = this.scanner.nextToken();
		else {
			throw new RuntimeException("syntax error at line " +
					this.scanner.getLineno() +
					": " + token + " expected, " +
					this.lookahead.getToken() + " found instead");
		}
	}

	/**
	 * Parses the input and builds a program from it.
	 * If a problem occurs while reading the input, then
	 * an IOException is thrown.
	 * 
	 * @return the program constructed from the input
	 * @throws IOException
	 */
	public abstract Program parse() throws IOException;
}
