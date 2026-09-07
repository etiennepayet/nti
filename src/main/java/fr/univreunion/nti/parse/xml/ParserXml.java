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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.parse.xml;

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
 * A parser for XML files storing term or string rewrite systems.
 *
 * <p>The accepted token grammar is:</p>
 * <pre>{@code
 * document        ::= xml-declaration stylesheet? problem
 * problem         ::= <problem> trs strategy metadata? </problem>
 * trs             ::= <trs> rules signature </trs>
 * rules           ::= <rules> rule* </rules>
 * rule            ::= <rule> <lhs> function </lhs> <rhs> term </rhs> </rule>
 * term            ::= variable | function
 * variable        ::= <var> identifier </var>
 * function        ::= <funapp> <name> identifier </name> argument* </funapp>
 * argument        ::= <arg> term </arg>
 * signature       ::= <signature> function-symbol* </signature>
 * function-symbol ::= <funcsym> <name> identifier </name>
 *                     <arity> identifier </arity> </funcsym>
 * strategy        ::= <strategy> identifier </strategy>
 * metadata        ::= <metainformation> token* </metainformation>
 * }</pre>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class ParserXml extends Parser {

	/**
	 * The rules of the program being built, in source order.
	 */
	private final List<RuleTrs> rules = new ArrayList<>();

	/**
	 * The rewriting strategy considered for the program being built.
	 */
	private String strategy = "FULL";

	/**
	 * Builds a parser for a TRS/SRS in XML format.
	 *
	 * @param programName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserXml(String programName, Scanner scanner) {
		super(programName, scanner);
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
		return new Trs(this.progName, this.rules, this.strategy);
	}

	/**
	 * Parses the complete XML document through the closing problem tag.
	 *
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private void parseDocument() throws IOException {
		this.parseHeader();
		this.match(Token.OPEN_PROBLEM_TAG);

		this.match(Token.OPEN_TRS_TAG);
		this.match(Token.OPEN_RULES_TAG);
		this.parseRules();
		this.match(Token.CLOSE_RULES_TAG);
		this.match(Token.OPEN_SIGN_TAG);
		this.parseFunctionSymbols();
		this.match(Token.CLOSE_SIGN_TAG);
		this.match(Token.CLOSE_TRS_TAG);

		this.match(Token.OPEN_STRATEGY_TAG);
		this.strategy = this.parseIdentifier();
		this.match(Token.CLOSE_STRATEGY_TAG);

		this.parseMetadata();
		this.match(Token.CLOSE_PROBLEM_TAG);
	}

	/**
	 * Parses the mandatory XML declaration and optional stylesheet instruction.
	 *
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private void parseHeader() throws IOException {
		this.match(Token.XML_TAG);
		if (this.lookahead.token() == Token.XML_STYLESHEET_TAG)
			this.match(Token.XML_STYLESHEET_TAG);
	}

	/**
	 * Parses all consecutive rules in source order.
	 *
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private void parseRules() throws IOException {
		while (this.lookahead.token() == Token.OPEN_RULE_TAG)
			this.rules.add(this.parseRule());
	}

	/**
	 * Parses one rewrite rule.
	 *
	 * @return the parsed rule
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private RuleTrs parseRule() throws IOException {
		this.match(Token.OPEN_RULE_TAG);
		Map<String, Variable> variables = new HashMap<>();

		this.match(Token.OPEN_LHS_TAG);
		Function left = this.parseFunction(variables);
		this.match(Token.CLOSE_LHS_TAG);

		this.match(Token.OPEN_RHS_TAG);
		Term right = this.parseTerm(variables);
		this.match(Token.CLOSE_RHS_TAG);
		this.match(Token.CLOSE_RULE_TAG);

		return new RuleTrs(left, right);
	}

	/**
	 * Parses a variable or function term.
	 *
	 * @param variables the variables already encountered in the current rule
	 * @return the parsed term
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws SyntaxException if the lookahead does not start a term
	 */
	private Term parseTerm(Map<String, Variable> variables) throws IOException {
		return switch (this.lookahead.token()) {
			case OPEN_VAR_TAG -> this.parseVariable(variables);
			case OPEN_FUNAPP_TAG -> this.parseFunction(variables);
			default -> throw this.unexpectedTerm();
		};
	}

	/**
	 * Parses a variable, reusing an earlier occurrence from the current rule.
	 *
	 * @param variables the variables already encountered in the current rule
	 * @return the parsed variable
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private Variable parseVariable(Map<String, Variable> variables) throws IOException {
		this.match(Token.OPEN_VAR_TAG);
		String name = this.parseIdentifier();
		this.match(Token.CLOSE_VAR_TAG);
		return variables.computeIfAbsent(name, ignored -> new Variable());
	}

	/**
	 * Parses a function application and its arguments.
	 *
	 * @param variables the variables already encountered in the current rule
	 * @return the parsed function
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private Function parseFunction(Map<String, Variable> variables) throws IOException {
		this.match(Token.OPEN_FUNAPP_TAG);
		this.match(Token.OPEN_NAME_TAG);
		String name = this.parseIdentifier();
		this.match(Token.CLOSE_NAME_TAG);

		List<Term> arguments = this.parseArguments(variables);
		Function function = new Function(
				FunctionSymbol.intern(name, arguments.size()), arguments);
		this.match(Token.CLOSE_FUNAPP_TAG);
		return function;
	}

	/**
	 * Parses all consecutive arguments of a function application.
	 *
	 * @param variables the variables already encountered in the current rule
	 * @return the parsed arguments in source order
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private List<Term> parseArguments(Map<String, Variable> variables) throws IOException {
		List<Term> arguments = new ArrayList<>();
		while (this.lookahead.token() == Token.OPEN_ARG_TAG) {
			this.match(Token.OPEN_ARG_TAG);
			arguments.add(this.parseTerm(variables));
			this.match(Token.CLOSE_ARG_TAG);
		}
		return arguments;
	}

	/**
	 * Parses all consecutive function-symbol declarations.
	 *
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private void parseFunctionSymbols() throws IOException {
		while (this.lookahead.token() == Token.OPEN_FUNCSYM_TAG)
			this.parseFunctionSymbol();
	}

	/**
	 * Parses one function-symbol declaration and validates its arity.
	 *
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws SyntaxException if the arity is not a non-negative integer
	 */
	private void parseFunctionSymbol() throws IOException {
		this.match(Token.OPEN_FUNCSYM_TAG);
		this.match(Token.OPEN_NAME_TAG);
		this.parseIdentifier();
		this.match(Token.CLOSE_NAME_TAG);

		this.match(Token.OPEN_ARITY_TAG);
		this.validateArity(this.parseIdentifier());
		this.match(Token.CLOSE_ARITY_TAG);
		this.match(Token.CLOSE_FUNCSYM_TAG);
	}

	/**
	 * Parses an identifier and returns its attribute.
	 *
	 * @return the identifier text
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private String parseIdentifier() throws IOException {
		Object attribute = this.lookahead.attribute();
		this.match(Token.ID);
		return attribute.toString();
	}

	/**
	 * Validates a function-symbol arity.
	 *
	 * @param lexeme the arity text
	 * @throws SyntaxException if {@code lexeme} is not a non-negative integer
	 */
	private void validateArity(String lexeme) {
		int lineNumber = this.scanner.getLineno();
		try {
			if (Integer.parseInt(lexeme) < 0)
				throw new SyntaxException(
						"arity at line " + lineNumber + " is not a positive integer", lineNumber);
		}
		catch (NumberFormatException exception) {
			throw new SyntaxException(
					"arity at line " + lineNumber + " is not an integer", lineNumber);
		}
	}

	/**
	 * Parses the optional metadata section, ignoring its contents.
	 *
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws SyntaxException if the metadata section reaches the end of the input
	 * without a closing tag
	 */
	private void parseMetadata() throws IOException {
		if (this.lookahead.token() != Token.OPEN_METAINFO_TAG) return;

		this.match(Token.OPEN_METAINFO_TAG);
		while (this.lookahead.token() != Token.CLOSE_METAINFO_TAG) {
			if (this.lookahead.token() == Token.DONE)
				this.match(Token.CLOSE_METAINFO_TAG);
			this.match(this.lookahead.token());
		}
		this.match(Token.CLOSE_METAINFO_TAG);
	}

	/**
	 * Creates the syntax error for a token that cannot start a term.
	 *
	 * @return the syntax exception
	 */
	private SyntaxException unexpectedTerm() {
		int lineNumber = this.scanner.getLineno();
		return new SyntaxException("syntax error at line " + lineNumber
				+ ": OPEN_VAR_TAG or OPEN_FUNAPP_TAG expected, "
				+ this.lookahead.token() + " found instead", lineNumber);
	}
}
