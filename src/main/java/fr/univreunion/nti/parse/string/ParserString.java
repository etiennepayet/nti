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

package fr.univreunion.nti.parse.string;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.SyntaxException;
import fr.univreunion.nti.parse.Token;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.PrologList;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A parser for strings representing terms, substitutions and individual
 * rewrite rules. It is primarily used by tests and textual helper APIs.
 *
 * <p>The accepted token grammar is:</p>
 * <pre>{@code
 * term                        ::= function | variable | anonymous-variable
 *                                 | integer | prolog-list
 * function                    ::= identifier | identifier '(' term-list ')'
 * term-list                   ::= term (',' term)*
 * prolog-list                 ::= '[' ']'
 *                                 | '[' term-list ']'
 *                                 | '[' term-list '|' term ']'
 * substitution                ::= '{' '}' | '{' mapping-list '}'
 * mapping-list                ::= mapping (',' mapping)*
 * mapping                     ::= variable '->' term
 * simple-pattern-substitution ::= substitution substitution substitution*
 * simple-pattern-term         ::= term simple-pattern-substitution
 * lp-rule                     ::= function '.'
 *                                 | function ':-' function-list '.'
 * function-list               ::= function (',' function)*
 * trs-rule                    ::= function '->' (function | variable | integer)
 * pattern-rule                ::= simple-pattern-term '->' simple-pattern-term
 * }</pre>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public final class ParserString {

	/**
	 * The scanner reading the current input.
	 */
	private ScannerString scanner;

	/**
	 * The last token and attribute returned by the scanner.
	 */
	private Pair lookahead;

	/**
	 * Builds a parser for textual terms, substitutions and rules.
	 */
	public ParserString() {
		// No initialization is needed: each public parse operation calls init(...).
	}

	/**
	 * Initializes this parser before parsing.
	 *
	 * @param input the input to read
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private void init(String input) throws IOException {
		this.scanner = new ScannerString(input);
		this.lookahead = this.scanner.nextToken();
	}

	/**
	 * Checks that the parsed value consumed the complete input.
	 *
	 * @param parsedValue the value constructed from the input
	 * @param <T> the type of the parsed value
	 * @return the parsed value
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	private <T> T finishParsing(T parsedValue) throws IOException {
		this.match(Token.DONE);
		return parsedValue;
	}

	/**
	 * Checks that the current token is the expected one and reads the next token.
	 *
	 * @param token the expected token
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws SyntaxException if the current token is not {@code token}
	 */
	private void match(Token token) throws IOException {
		if (this.lookahead.token() == token) {
			this.lookahead = this.scanner.nextToken();
			return;
		}

		int lineNumber = this.scanner.getLineno();
		throw new SyntaxException("syntax error at line " + lineNumber
				+ ": " + token + " expected, " + this.lookahead.token()
				+ " found instead", lineNumber);
	}

	/**
	 * Parses a term and adds its named variables to the supplied variable map.
	 *
	 * @param input the input string to parse
	 * @param variables the variables encountered so far
	 * @return the term constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	public Term parseTerm(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.finishParsing(this.readTerm(variables));
	}

	/**
	 * Parses a substitution and adds its named variables to the supplied map.
	 *
	 * @param input the input string to parse
	 * @param variables the variables encountered so far
	 * @return the substitution constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	public Substitution parseSubstitution(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.finishParsing(this.readSubstitution(variables));
	}

	/**
	 * Parses a simple pattern substitution and adds its named variables to the
	 * supplied map.
	 *
	 * @param input the input string to parse
	 * @param variables the variables encountered so far
	 * @return the simple pattern substitution constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	public SimplePatternSubstitution parseSimplePatternSubstitution(
			String input, Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.finishParsing(this.readSimplePatternSubstitution(variables));
	}

	/**
	 * Parses a simple pattern term and adds its named variables to the supplied
	 * map.
	 *
	 * @param input the input string to parse
	 * @param variables the variables encountered so far
	 * @return the simple pattern term constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	public SimplePatternTerm parseSimplePatternTerm(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.finishParsing(this.readSimplePatternTerm(variables));
	}

	/**
	 * Parses an LP rule and adds its named variables to the supplied map.
	 *
	 * @param input the input string to parse
	 * @param variables the variables encountered so far
	 * @return the LP rule constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	public RuleLp parseLpRule(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.finishParsing(this.readLpRule(variables));
	}

	/**
	 * Parses a TRS rule and adds its named variables to the supplied map.
	 *
	 * @param input the input string to parse
	 * @param variables the variables encountered so far
	 * @return the TRS rule constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	public RuleTrs parseTrsRule(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.finishParsing(this.readTrsRule(variables));
	}

	/**
	 * Parses a pattern TRS rule and adds its named variables to the supplied map.
	 *
	 * @param input the input string to parse
	 * @param variables the variables encountered so far
	 * @return the pattern rule constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	public PatternRuleTrs parsePatternRuleTrs(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);

		SimplePatternTerm left = this.readSimplePatternTerm(variables);
		this.match(Token.ARROW);
		SimplePatternTerm right = this.readSimplePatternTerm(variables);

		return this.finishParsing(PatternRuleTrs.tryBuild(left, right, 0));
	}

	/**
	 * <pre>{@code simple-pattern-term ::= term simple-pattern-substitution}</pre>
	 *
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the simple pattern term that has
	 * been read
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	private SimplePatternTerm readSimplePatternTerm(
			Map<String, Variable> variables) throws IOException {
		Term baseTerm = this.readTerm(variables);
		SimplePatternSubstitution patternSubstitution =
				this.readSimplePatternSubstitution(variables);

		return SimplePatternTerm.tryBuild(baseTerm, patternSubstitution);
	}

	/**
	 * <pre>{@code
	 * term ::= function | variable | anonymous-variable
	 *          | integer | prolog-list}
	 * </pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 */
	private Term readTerm(Map<String, Variable> variables) throws IOException {
		Token token = this.lookahead.token();
		if (token == Token.ID)
			return this.readFunction(variables);
		if (token == Token.VAR) {
			String lexeme = this.readLexeme(token);
			return getOrCreateVariable(lexeme, variables);
		}
		if (token == Token.INT) {
			String lexeme = this.readLexeme(token);
			return new Function(FunctionSymbol.intern(lexeme, 0), List.of());
		}
		if (token == Token.ANONYMOUS_VAR) {
			this.match(token);
			return new Variable();
		}
		return this.readPrologList(variables);
	}

	/**
	 * <pre>{@code function ::= identifier | identifier '(' term-list ')'}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the function that has been read
	 */
	private Function readFunction(Map<String, Variable> variables) throws IOException {
		List<Term> arguments = new ArrayList<>();

		String lexeme = this.readLexeme(Token.ID);

		if (this.lookahead.token() == Token.OPEN_PAR) {
			this.match(Token.OPEN_PAR);
			this.readTermSequence(variables, arguments);
			this.match(Token.CLOSE_PAR);
		}

		return new Function(
				FunctionSymbol.intern(lexeme, arguments.size()),
				arguments);
	}

	/**
	 * Reads the lexeme carried by the expected token. The token is validated
	 * before its attribute is accessed.
	 *
	 * @param token the expected token
	 * @return the token lexeme
	 */
	private String readLexeme(Token token) throws IOException {
		Pair tokenAndAttribute = this.lookahead;
		this.match(token);
		return tokenAndAttribute.attribute().toString();
	}

	/**
	 * <pre>{@code
	 * prolog-list ::= '[' ']'
	 *                 | '[' term-list ']'
	 *                 | '[' term-list '|' term ']'}
	 * </pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the Prolog list that has been read
	 */
	private PrologList readPrologList(Map<String, Variable> variables) throws IOException {
		this.match(Token.OPEN_SQ_PAR);
		if (this.lookahead.token() == Token.CLOSE_SQ_PAR) {
			this.match(Token.CLOSE_SQ_PAR);
			return PrologList.emptyPrologList();
		}

		List<Term> elements = new ArrayList<>();
		this.readTermSequence(variables, elements);
		Token token = this.lookahead.token();
		if (token == Token.CLOSE_SQ_PAR) {
			this.match(token);
			return new PrologList(elements);
		}
		if (token == Token.PIPE) {
			this.match(token);
			PrologList list = new PrologList(elements, this.readTerm(variables));
			this.match(Token.CLOSE_SQ_PAR);
			return list;
		}

		int lineNumber = this.scanner.getLineno();
		throw new SyntaxException("syntax error: non-ended list at line " + lineNumber, lineNumber);
	}

	/**
	 * <pre>{@code term-list ::= term (',' term)*}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @param terms list of terms to fill
	 */
	private void readTermSequence(Map<String, Variable> variables, List<Term> terms)
			throws IOException {
		terms.add(this.readTerm(variables));
		while (this.lookahead.token() == Token.COMMA) {
			this.match(Token.COMMA);
			terms.add(this.readTerm(variables));
		}
	}

	/**
	 * Returns the variable associated with the specified name, creating it when
	 * it has not been encountered yet.
	 *
	 * @param lexeme the variable name
	 * @param variables the variables encountered so far
	 * @return the variable associated with the name
	 */
	private static Variable getOrCreateVariable(
			String lexeme, Map<String, Variable> variables) {
		return variables.computeIfAbsent(lexeme, ignoredName -> new Variable());
	}

	/**
	 * <pre>{@code simple-pattern-substitution ::= substitution substitution substitution*}</pre>
	 * <p>
	 *  <p>
	 * A simple pattern substitution consists of at least
	 * two substitutions (a closing substitution and at
	 * least one pumping substitution).
	 * </p>
	 *
	 * @param variables the set of variables that have
	 * been encountered so far
	 * @return the simple pattern substitution that has
	 * been read
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	private SimplePatternSubstitution readSimplePatternSubstitution(
			Map<String, Variable> variables) throws IOException {
		List<Substitution> substitutions = new ArrayList<>();

		// A pattern substitution consists of at
		// least two substitutions.
		substitutions.add(this.readSubstitution(variables));
		substitutions.add(this.readSubstitution(variables));

		while (this.lookahead.token() == Token.OPEN_BRACE)
			substitutions.add(this.readSubstitution(variables));

		// Returns null if substitutions
		// does not have the correct form.
		return SimplePatternSubstitution.tryBuild(substitutions);
	}

	/**
	 * <pre>{@code substitution ::= '{' '}' | '{' mapping-list '}'}</pre>
	 *
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the substitution that has been read
	 */
	private Substitution readSubstitution(Map<String, Variable> variables) throws IOException {
		this.match(Token.OPEN_BRACE);
		Substitution substitution = new Substitution();

		if (this.lookahead.token() == Token.VAR)
			this.readMappings(substitution, variables);

		this.match(Token.CLOSE_BRACE);
		return substitution;
	}

	/**
	 * <pre>{@code mapping-list ::= mapping (',' mapping)*}</pre>
	 *
	 * @param substitution the substitution to fill
	 * @param variables the set of variables that have been encountered so far
	 */
	private void readMappings(
			Substitution substitution, Map<String, Variable> variables) throws IOException {
		this.readMapping(substitution, variables);
		while (this.lookahead.token() == Token.COMMA) {
			this.match(Token.COMMA);
			this.readMapping(substitution, variables);
		}
	}

	/**
	 * <pre>{@code mapping ::= variable '->' term}</pre>
	 *
	 * @param substitution the substitution to fill
	 * @param variables the set of variables that have been encountered so far
	 */
	private void readMapping(
			Substitution substitution, Map<String, Variable> variables) throws IOException {
		String variableName = this.readLexeme(Token.VAR);
		this.match(Token.ARROW);

		Variable domainVariable = getOrCreateVariable(variableName, variables);
		substitution.add(domainVariable, this.readTerm(variables));
	}

	/**
	 * <pre>{@code
	 * lp-rule ::= function '.'
	 *             | function ':-' function-list '.'}
	 * </pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the LP rule that has been read
	 */
	private RuleLp readLpRule(Map<String, Variable> variables) throws IOException {
		Function head = this.readFunction(variables);
		List<Function> body = new ArrayList<>();
		if (this.lookahead.token() == Token.LPARROW) {
			this.match(Token.LPARROW);
			this.readFunctionSequence(variables, body);
		}
		this.match(Token.DOT);

		return new RuleLp(head, body.toArray(Function[]::new));
	}

	/**
	 * <pre>{@code function-list ::= function (',' function)*}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @param functions the list of functions to fill
	 */
	private void readFunctionSequence(
			Map<String, Variable> variables, List<Function> functions) throws IOException {
		functions.add(this.readFunction(variables));
		while (this.lookahead.token() == Token.COMMA) {
			this.match(Token.COMMA);
			functions.add(this.readFunction(variables));
		}
	}

	/**
	 * <pre>{@code trs-rule ::= function '->' (function | variable | integer)}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the TRS rule that has been read
	 */
	private RuleTrs readTrsRule(Map<String, Variable> variables) throws IOException {
		Function left = this.readFunction(variables);
		this.match(Token.ARROW);
		return new RuleTrs(left, this.readTrsRightHandSide(variables));
	}

	/**
	 * Reads the right-hand side of a TRS rule.
	 *
	 * @param variables the variables encountered so far
	 * @return the right-hand side read
	 */
	private Term readTrsRightHandSide(Map<String, Variable> variables) throws IOException {
		Token token = this.lookahead.token();
		if (token == Token.VAR || token == Token.INT)
			return this.readTerm(variables);
		return this.readFunction(variables);
	}
}
