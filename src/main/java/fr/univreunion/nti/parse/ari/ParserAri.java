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
 * A parser for term or string rewrite systems in the
 * <a href="https://termination-portal.org/wiki/Term_Rewriting">ARI format</a>.
 *
 * <p>The accepted token grammar is:</p>
 * <pre>{@code
 * document             ::= '(' "format" "TRS" ')' declaration* rule* EOF
 * declaration          ::= '(' "fun" identifier integer ')'
 * rule                 ::= '(' "rule" term term ')'
 * term                 ::= identifier | '(' identifier term+ ')'
 * }</pre>
 *
 * <p>Comments start with {@code ;} and continue to the end of the line.
 * Function declarations must precede rules. A declared nullary identifier is
 * a constant; any other bare identifier is a variable. Non-nullary function
 * applications must use a declared symbol with the declared arity.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class ParserAri extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final List<RuleTrs> rules = new ArrayList<>();

	/**
	 * The variables of the program to be built.
	 * The following data structure is a dictionary
	 * of the form { lexeme -> variable }.
	 */
	private final Map<String, Variable> variables = new HashMap<>();

	/**
	 * Declarations of this document. Global symbol interning preserves identity,
	 * but declarations from an earlier parse must not affect this grammar.
	 */
	private final Map<Signature, FunctionSymbol> declaredSymbols = new HashMap<>();

	private record Signature(String name, int arity) {}

    /**
	 * Builds a parser for a TRS/SRS in ARI format.
	 *
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserAri(String progName, Scanner scanner) {
		super(progName, scanner);
	}

	/**
	 * Parses the input and builds a rewrite system from it.
	 *
	 * @return the program constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	@Override
	public Program parse() throws IOException {
		this.lookahead = this.scanner.nextToken();
		this.parseDocument();
		return new Trs(this.progName, this.rules, "FULL");
	}

	/**
	 * <pre>
	 *     {@code document ::= '(' "format" "TRS" ')' declaration* rule* EOF}
	 * </pre>
	 */
	private void parseDocument() throws IOException {
		this.match(Token.OPEN_PAR);
		this.match(Token.FORMAT);
		this.match(Token.TRS);
		this.match(Token.CLOSE_PAR);

		this.parseDeclarationsAndRules();

		this.match(Token.DONE);
	}

	/**
	 * <pre>
	 *     {@code declarations_and_rules ::= ( '(' declaration ')' )*  ( '(' rule ')' )*}
	 * </pre>
	 */
	private void parseDeclarationsAndRules() throws IOException {
		boolean declarationsAllowed = true;

		while (this.lookahead.token() == Token.OPEN_PAR) {
			this.match(Token.OPEN_PAR);

			if (declarationsAllowed && this.lookahead.token() == Token.FUN) {
				this.parseFunctionDeclaration();
			}
			else if (this.lookahead.token() == Token.RULE) {
				// Once we have read a rule, we cannot read
				// a function symbol declaration anymore:
				declarationsAllowed = false;
				this.parseRule();
			}
			else {
				int lineNumber = this.scanner.getLineno();
				throw new SyntaxException("error at line " + lineNumber + ": "
						+ (declarationsAllowed ? "'fun' or " : "")
						+ "'rule' expected", lineNumber);
			}

			this.match(Token.CLOSE_PAR);
		}
	}

	/**
	 * <pre>{@code declaration ::= "fun" identifier integer}</pre>
	 */
	private void parseFunctionDeclaration() throws IOException {
		this.match(Token.FUN);

		String lexeme = (String) this.lookahead.attribute();
		this.match(Token.ID);

		int arity = (int) this.lookahead.attribute();
		this.match(Token.INT);

		this.declaredSymbols.put(new Signature(lexeme, arity),
				FunctionSymbol.intern(lexeme, arity));
	}

	/**
	 * <pre>{@code rule ::= "rule" term term}</pre>
	 */
	private void parseRule() throws IOException {
		this.match(Token.RULE);

		Term left = this.parseTerm();
		if (!(left instanceof Function leftFunction)) {
			int lineNumber = this.scanner.getLineno();
			throw new SyntaxException("error at line " + lineNumber
					+ ": left-hand side of rule cannot be a variable", lineNumber);
		}

		Term right = this.parseTerm();

		this.rules.add(new RuleTrs(leftFunction, right));
	}

	/**
	 * <pre>{@code term ::= identifier | '(' identifier term+ ')'}</pre>
	 *
	 * @return the term that has been read
	 */
	private Term parseTerm() throws IOException {
		if (this.lookahead.token() == Token.ID) {
			return this.parseIdentifierTerm();
		}

		return this.parseFunctionApplication();
	}

	/**
	 * Parses a nullary function or a variable.
	 *
	 * @return the parsed term
	 */
	private Term parseIdentifierTerm() throws IOException {
		String lexeme = (String) this.lookahead.attribute();
		this.match(Token.ID);

		FunctionSymbol functionSymbol = this.declaredSymbols.get(new Signature(lexeme, 0));
		if (functionSymbol != null) {
			return new Function(functionSymbol, List.of());
		}

		return this.variables.computeIfAbsent(lexeme, ignored -> new Variable());
	}

	/**
	 * Parses a function application.
	 *
	 * @return the parsed function
	 */
	private Function parseFunctionApplication() throws IOException {
		this.match(Token.OPEN_PAR);

		String lexeme = (String) this.lookahead.attribute();
		this.match(Token.ID);

		List<Term> arguments = new ArrayList<>();
		do {
			arguments.add(this.parseTerm());
		}
		while (this.lookahead.token() == Token.ID
				|| this.lookahead.token() == Token.OPEN_PAR);

		this.match(Token.CLOSE_PAR);

		int arity = arguments.size();
		FunctionSymbol functionSymbol = this.declaredSymbols.get(new Signature(lexeme, arity));
		if (functionSymbol == null) {
			int lineNumber = this.scanner.getLineno();
			throw new SyntaxException("error at line " + lineNumber
					+ ": undeclared identifier " + lexeme + " of arity " + arity,
					lineNumber);
		}
		return new Function(functionSymbol, arguments);
	}
}
