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

package fr.univreunion.nti.parse.trs;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
 * A parser for term rewrite systems in the legacy human-readable format.
 *
 * <p>The accepted token grammar is:</p>
 * <pre>{@code
 * specification    ::= ('(' declaration ')')* EOF
 * declaration      ::= "VAR" identifier*
 *                    | "RULES" rule*
 *                    | "STRATEGY" strategy
 *                    | identifier auxiliary-token*
 * rule             ::= term '->' term
 * term             ::= identifier | identifier '(' term-list? ')'
 * term-list        ::= term (',' term)*
 * strategy         ::= "INNERMOST" | "OUTERMOST"
 * auxiliary-token  ::= '->' | identifier | string | ','
 *                    | '(' auxiliary-token* ')'
 * }</pre>
 *
 * <p>Identifiers declared by {@code VAR} are parsed as variables; all other
 * identifiers denote function symbols. Auxiliary declarations are accepted
 * and ignored.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class ParserTrs extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final List<RuleTrs> rules = new ArrayList<>();

	/**
	 * The variables of the program to be built.
	 * They are declared using the <code>var</code>
	 * keyword. The following data structure is
	 * a dictionary { lexeme -> variable }.
	 */
	private final Map<String, Variable> variables = new HashMap<>();

	/**
	 * The rewriting strategy (standard, innermost, ...)
	 * considered for the program to be built.
	 * Default value is FULL (standard rewriting).
	 */
	private String strategy = "FULL";

	/**
	 * Builds a parser for a TRS in the legacy human-readable format.
	 *
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserTrs(String progName, Scanner scanner) {
		super(progName, scanner);
	}

	/**
	 * Parses the input and builds a term rewrite system from it.
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
	 * declaration ::= "VAR" identifier*
	 *               | "RULES" rule*
	 *               | "STRATEGY" strategy
	 *               | identifier auxiliary-token*}
	 * </pre>
	 */
	private void parseDeclaration() throws IOException {
		Token token = this.lookahead.token();
		switch (token) {
			case VAR -> {
				this.match(token);
				this.parseVariableDeclarations();
			}
			case RULES -> {
				this.match(token);
				this.parseRules();
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
	 *  </pre>
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
	 * <pre>{@code term-list ::= term (',' term)*}</pre>
	 */
	private void parseVariableDeclarations() throws IOException {
		while (this.lookahead.token() == Token.ID) {
			String lexeme = (String) this.lookahead.attribute();
			this.match(Token.ID);
			this.variables.computeIfAbsent(lexeme, ignored -> new Variable());
		}
	}

	/**
	 * <pre>{@code rule-list ::= rule (',' rule)*}</pre>
	 */
	private void parseRules() throws IOException {
		while (this.lookahead.token() == Token.ID) {
			this.rules.add(this.parseRule());
		}
	}

	/**
	 * <pre>{@code rule ::= term '->' term}</pre>
	 *
	 * @return the rule that has been read
	 */
	private RuleTrs parseRule() throws IOException {
		Term left = this.parseTerm();
		if (!(left instanceof Function leftFunction)) {
			throw this.syntaxException(
					"left-hand side of rule cannot be a variable");
		}

		this.match(Token.ARROW);
		Term right = this.parseTerm();

		return new RuleTrs(leftFunction, right);
	}

	/**
	 * <pre>{@code term ::= identifier | identifier '(' term-list? ')'}</pre>
	 *
	 * @return the term that has been read
	 */
	private Term parseTerm() throws IOException {
		String lexeme = (String) this.lookahead.attribute();
		this.match(Token.ID);

		Variable variable = this.variables.get(lexeme);
		if (variable != null) {
			return variable;
		}

		List<Term> arguments = new ArrayList<>();
		if (this.lookahead.token() == Token.OPEN_PAR) {
			this.match(Token.OPEN_PAR);
			if (this.lookahead.token() != Token.CLOSE_PAR) {
				this.parseTermList(arguments);
			}
			this.match(Token.CLOSE_PAR);
		}
		return new Function(FunctionSymbol.intern(lexeme, arguments.size()), arguments);
	}

	/**
	 * <pre>{@code term-list ::= term (',' term)*}</pre>
	 *
	 * @param terms the list of terms to fill
	 */
	private void parseTermList(List<Term> terms) throws IOException {
		terms.add(this.parseTerm());
		while (this.lookahead.token() == Token.COMMA) {
			this.match(Token.COMMA);
			terms.add(this.parseTerm());
		}
	}

	/**
	 * <pre>{@code strategy ::= "INNERMOST" | "OUTERMOST"}</pre>
	 */
	private String parseStrategy() throws IOException {
		if (this.lookahead.token() == Token.INNERMOST) {
			String strategyName = this.lookahead.attribute().toString();
			this.match(Token.INNERMOST);
			return strategyName;
		}
		if (this.lookahead.token() == Token.OUTERMOST) {
			String strategyName = this.lookahead.attribute().toString();
			this.match(Token.OUTERMOST);
			return strategyName;
		}

		throw this.syntaxException(
				"unknown strategy " + this.lookahead.attribute());
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
