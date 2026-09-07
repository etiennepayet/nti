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

package fr.univreunion.nti.parse.srs;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.parse.Parser;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.SyntaxException;
import fr.univreunion.nti.parse.Token;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A parser for string rewrite systems in the legacy human-readable format.
 *
 * <p>The accepted token grammar is:</p>
 * <pre>{@code
 * specification    ::= ('(' declaration ')')* EOF
 * declaration      ::= "RULES" rule-list?
 *                    | "STRATEGY" strategy
 *                    | identifier auxiliary-token*
 * rule-list        ::= rule (',' rule)*
 * rule             ::= word '->' word?
 * word             ::= identifier+
 * strategy         ::= "LEFTMOST" | "RIGHTMOST"
 * auxiliary-token  ::= '->' | identifier | string | ','
 *                    | '(' auxiliary-token* ')'
 * }</pre>
 *
 * <p>Each word is encoded as a chain of unary function symbols ending in a
 * shared variable. Auxiliary declarations are accepted and ignored.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class ParserSrs extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final List<RuleTrs> rules = new ArrayList<>();

	/**
	 * The rewriting strategy (standard, innermost, ...)
	 * considered for the program to be built.
	 * Default value is FULL (standard rewriting).
	 */
	private String strategy = "FULL";

	/**
	 * Builds a parser for an SRS in the legacy human-readable format.
	 *
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserSrs(String progName, Scanner scanner) {
		super(progName, scanner);
	}

	/**
	 * Parses the input and builds a string rewrite system from it.
	 *
	 * @return the program constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	@Override
	public Program parse() throws IOException {
		this.lookahead = this.scanner.nextToken();
		this.parseSpecification();
		return new Trs(this.progName, this.rules, this.strategy);
	}

	/**
	 * <pre>{@code specification ::= ('(' declaration ')')* EOF}</pre>
	 */
	private void parseSpecification() throws IOException {
		while (this.lookahead.token() == Token.OPEN_PAR) {
			this.match(Token.OPEN_PAR);
			this.parseDeclaration();
			this.match(Token.CLOSE_PAR);
		}

		if (this.lookahead.token() != Token.DONE) {
			throw this.unexpectedSyntaxException();
		}
	}

	/**
	 * <pre>{@code
	 * declaration ::= "RULES" rule-list?
	 *               | "STRATEGY" strategy
	 *               | identifier auxiliary-token*}
	 * </pre>
	 */
	private void parseDeclaration() throws IOException {
		Token token = this.lookahead.token();
		switch (token) {
			case RULES -> {
				this.match(token);
				if (this.lookahead.token() == Token.ID) {
					this.parseRules();
				}
			}
			case STRATEGY -> {
				this.match(token);
				this.strategy = this.parseStrategy();
			}
			case ID -> {
				this.match(token);
				this.skipDeclarationBody();
			}
			default -> throw this.unexpectedSyntaxException();
		}
	}

	/**
	 * <pre>{@code
	 * auxiliary-token ::= '->' | identifier | string | ','
	 *                   | '(' auxiliary-token* ')'}
	 * </pre>
	 */
	private void skipDeclarationBody() throws IOException {
		int nestedParentheses = 0;
		while (true) {
			Token token = this.lookahead.token();
			switch (token) {
				case OPEN_PAR -> {
					nestedParentheses++;
					this.match(token);
				}
				case CLOSE_PAR -> {
					if (nestedParentheses == 0) {
						return;
					}
					nestedParentheses--;
					this.match(token);
				}
				case ARROW, ID, STRING, COMMA -> this.match(token);
				default -> {
					return;
				}
			}
		}
	}

	/**
	 * <pre>{@code rule-list ::= rule (',' rule)*}</pre>
	 */
	private void parseRules() throws IOException {
		this.rules.add(this.parseRule());
		while (this.lookahead.token() == Token.COMMA) {
			this.match(Token.COMMA);
			if (this.lookahead.token() != Token.ID) {
				int lineNumber = this.scanner.getLineno();
				throw new SyntaxException(Token.ID + " expected, "
						+ this.lookahead.token() + " found instead at line " + lineNumber,
						lineNumber);
			}
			this.rules.add(this.parseRule());
		}
	}

	/**
	 * <pre>{@code rule ::= word '->' word?}</pre>
	 *
	 * @return the rule that has been read
	 */
	private RuleTrs parseRule() throws IOException {
		Variable terminalVariable = new Variable();
		Function left = this.parseWord(terminalVariable);
		this.match(Token.ARROW);
		Term right = this.lookahead.token() == Token.ID
				? this.parseWord(terminalVariable)
				: terminalVariable;

		return new RuleTrs(left, right);
	}

	/**
	 * <pre>{@code word ::= identifier+}</pre>
	 *
	 * @param terminalVariable the variable terminating the encoded word
	 * @return the word that has been read
	 */
	private Function parseWord(Variable terminalVariable) throws IOException {
		List<String> symbols = new ArrayList<>();
		do {
			String lexeme = (String) this.lookahead.attribute();
			this.match(Token.ID);
			symbols.add(lexeme);
		}
		while (this.lookahead.token() == Token.ID);

		Term suffix = terminalVariable;
		for (int index = symbols.size() - 1; index >= 0; index--) {
			suffix = new Function(
					FunctionSymbol.intern(symbols.get(index), 1),
					List.of(suffix));
		}
		return (Function) suffix;
	}

	/**
	 * <pre>{@code strategy ::= "LEFTMOST" | "RIGHTMOST"}</pre>
	 */
	private String parseStrategy() throws IOException {
		Token token = this.lookahead.token();
		return switch (token) {
			case LEFTMOST, RIGHTMOST -> {
				String strategyName = this.lookahead.attribute().toString();
				this.match(token);
				yield strategyName;
			}
			default -> throw this.syntaxException(
					"unknown strategy " + this.lookahead.attribute());
		};
	}

	/**
	 * Creates a generic syntax exception for the current line.
	 *
	 * @return the syntax exception
	 */
	private SyntaxException unexpectedSyntaxException() {
		int lineNumber = this.scanner.getLineno();
		return new SyntaxException("syntax error at line " + lineNumber, lineNumber);
	}

	/**
	 * Creates a detailed syntax exception for the current line.
	 *
	 * @param detail the error detail
	 * @return the syntax exception
	 */
	private SyntaxException syntaxException(String detail) {
		int lineNumber = this.scanner.getLineno();
		return new SyntaxException("error at line " + lineNumber + ": " + detail, lineNumber);
	}
}
