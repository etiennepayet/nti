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

package fr.univreunion.nti.parse;

import java.io.IOException;

import fr.univreunion.nti.program.Program;

/**
 * Base class for parsers that build an NTI program from a token stream.
 *
 * <p>Concrete parsers initialize {@link #lookahead}, consume tokens from
 * {@link #scanner} through {@link #match(Token)}, and return the resulting
 * {@link Program}.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public abstract class Parser {

	/**
	 * The scanner which is used for reading the input.
	 */
	protected Scanner scanner;

	/**
	 * The last pair (token, attribute) returned by the scanner.
	 */
	protected Pair lookahead;

	/**
	 * The name of the program to be built.
	 */
	protected final String progName;

	/**
	 * Builds a parser for the specified program.
	 *
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	protected Parser(String progName, Scanner scanner) {
		this.progName = progName;
		this.scanner = scanner;
	}

	/**
	 * Checks that the current lookahead has the expected token and advances to
	 * the next token.
	 *
	 * @param token the expected token
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws SyntaxException if the current token is not {@code token}
	 */
	protected void match(Token token) throws IOException {
		if (this.lookahead.token() == token)
			this.lookahead = this.scanner.nextToken();
		else {
			int lineNumber = this.scanner.getLineno();
			throw new SyntaxException("syntax error at line " +
					lineNumber +
					": " + token + " expected, " +
					this.lookahead.token() + " found instead", lineNumber);
		}
	}

	/**
	 * Parses the input and builds a program from it.
	 *
	 * @return the program constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	public abstract Program parse() throws IOException;
}
