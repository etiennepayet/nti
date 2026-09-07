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

package fr.univreunion.nti.parse.lp;

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
import fr.univreunion.nti.program.lp.Lp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.PrologList;
import fr.univreunion.nti.term.PrologTuple;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A parser for Prolog-style logic programs.
 *
 * <p>Tokens and lexemes:</p>
 * <pre>{@code
 * done          = {EOF}
 * id            = lowercase_letter.(digit + letter + '_')*
 * var           = (uppercase_letter + '_').(digit + letter + '_')^+
 * anonymous_var = '_'
 * num           = digit.digit* ('.' digit.digit*)?
 * mode          = { '%query:' }
 * }</pre>
 *
 * <p>Non-terminal symbols:</p>
 * <pre>{@code
 * Lr = logic program (start symbol)
 * R  = rule
 * U  = Prolog directive
 * M  = mandatory query declaration
 * I  = rule or Prolog directive
 * La = list of atoms or functions
 * A  = atom
 * F  = function
 * E  = arithmetic expression consisting of +, - and products
 * B  = arithmetic product consisting of *, / and terms
 * T  = term
 * Li = Prolog list
 * Tu = Prolog tuple
 * Lt = list of terms
 * }</pre>
 *
 * <p>The accepted grammar is:</p>
 * <pre>{@code
 * Lr ::= M U* R I* done
 * I  ::= R | U
 * R  ::= F '.' | F ':-' La '.'
 * U  ::= ':-' A '.'
 * M  ::= mode F '.'
 * La ::= A | A ',' La
 * A  ::= F | E '=' E
 * F  ::= id | id Tu
 * E  ::= B (('+' | '-') B)*
 * B  ::= T (('*' | '/') T)*
 * T  ::= F | var | anonymous_var | num | Li | Tu
 * Li ::= '[' ']' | '[' Lt ']' | '[' Lt '|' E ']'
 * Tu ::= '(' Lt ')'
 * Lt ::= E | E ',' Lt
 * }</pre>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParserLp extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final List<RuleLp> rules = new ArrayList<>();

	/**
	 * A flag indicating whether the unification operator '='
	 * occurs in the program to be built. If this flag is true
	 * after parsing the program, then a rule of the form '=(X,X).'
	 * is added to the program.
	 */
	private boolean equalityOccurs;

	/**
	 * Builds a parser for a logic program.
	 *
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserLp(String progName, Scanner scanner) {
		super(progName, scanner);
	}

	/**
	 * Parses the input and builds a logic program from it.
	 *
	 * @return the program constructed from the input
	 * @throws IOException if an I/O error occurs while reading the input
	 */
	@Override
	public Program parse() throws IOException {
		this.lookahead = this.scanner.nextToken();
		Mode mode = this.parseMode();
		this.parseProgramItems();
		if (this.rules.isEmpty())
			throw this.syntaxException("at least one clause is required");
		if (this.equalityOccurs)
			this.addEqualityRule();

		return new Lp(this.progName, this.rules, mode);
	}

	/**
	 * Parses the rules and optional Prolog directives following the mandatory
	 * query declaration.
	 */
	private void parseProgramItems() throws IOException {
		while (this.lookahead.token() != Token.DONE)
			this.parseProgramItem();
	}

	/**
	 * Parses one rule or Prolog directive.
	 */
	private void parseProgramItem() throws IOException {
		switch (this.lookahead.token()) {
			case ID -> this.rules.add(this.parseRule());
			case ARROW -> this.parseDirective();
			case MODE -> throw this.syntaxException("only one %query directive is allowed");
			default -> throw this.syntaxException(null);
		}
	}

	/**
	 * Adds the rule {@code =(X,X).} required by programs containing equality.
	 */
	private void addEqualityRule() {
		List<Term> arguments = new ArrayList<>();
		Variable reflexiveVariable = new Variable();
		arguments.add(reflexiveVariable);
		arguments.add(reflexiveVariable);
		Function equality = new Function(FunctionSymbol.intern("=", 2), arguments);
		this.rules.add(new RuleLp(equality));
	}

	/**
	 * <pre>{@code R ::= F '.' | F ':-' La '.'}</pre>
	 *
	 * @return the rule that has been read
	 */
	private RuleLp parseRule() throws IOException {
		Map<String, Variable> variables = new HashMap<>();

		Function head = this.parseFunction(variables);
		List<Function> body = new ArrayList<>();
		if (this.lookahead.token() == Token.ARROW) {
			this.match(Token.ARROW);
			this.parseAtomList(variables, body);
		}
		this.match(Token.DOT);

		return new RuleLp(head, body.toArray(Function[]::new));
	}

	/**
	 * <pre>{@code U ::= ':-' A '.'}</pre>
	 */
	private void parseDirective() throws IOException {
		this.match(Token.ARROW);
		this.parseAtom(new HashMap<>());
		this.match(Token.DOT);
	}

	/**
	 * Parses the unique query declaration at the beginning of the program.
	 *
	 * <pre>{@code M ::= "%query:" F '.'}</pre>
	 */
	private Mode parseMode() throws IOException {
		this.match(Token.MODE);
		Mode mode = new Mode(this.parseFunction(new HashMap<>()));
		this.match(Token.DOT);
		return mode;
	}

	/**
	 * Builds a syntax exception at the current input line.
	 *
	 * @param detail a description of the error, or {@code null} for none
	 * @return the syntax exception
	 */
	private SyntaxException syntaxException(String detail) {
		int lineNumber = this.scanner.getLineno();
		String message = "syntax error at line " + lineNumber;
		if (detail != null)
			message += ": " + detail;
		return new SyntaxException(message, lineNumber);
	}

	/**
	 * <pre>{@code La ::= A | A ',' La}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @param atoms the list of atoms to fill
	 */
	private void parseAtomList(Map<String, Variable> variables, List<Function> atoms) throws IOException {
		while (true) {
			atoms.add(this.parseAtom(variables));
			if (this.lookahead.token() != Token.COMMA)
				return;
			this.match(Token.COMMA);
		}
	}

	/**
	 * <pre>{@code A ::= F | E '=' E}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the atom that has been read
	 */
	private Function parseAtom(Map<String, Variable> variables) throws IOException {
		Token firstToken = this.lookahead.token();
		ParsedExpression expression = this.parseExpressionWithMetadata(variables);
		if (this.lookahead.token() == Token.EQ)
			return this.parseEquality(expression.term(), variables);
		if (firstToken == Token.ID && !expression.hasTopLevelOperator())
			return (Function) expression.term();

		return this.parseEquality(expression.term(), variables);
	}

	/**
	 * Parses the equality operator and its right-hand side.
	 *
	 * @param leftHandSide the already parsed left-hand side
	 * @param variables the variables encountered in the current clause
	 * @return the equality atom that has been read
	 */
	private Function parseEquality(Term leftHandSide, Map<String, Variable> variables) throws IOException {
		this.match(Token.EQ);
		Term rightHandSide = this.parseExpression(variables);
		this.equalityOccurs = true;
		return this.createBinaryFunction("=", leftHandSide, rightHandSide);
	}

	/**
	 * <pre>{@code F ::= id | id Tu}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the atom that has been read
	 */
	private Function parseFunction(Map<String, Variable> variables) throws IOException {
		List<Term> arguments = new ArrayList<>();

		String lexeme = this.lookahead.attribute().toString();
		this.match(Token.ID);

		if (this.lookahead.token() == Token.OPEN_PAR) {
			this.match(Token.OPEN_PAR);
			this.parseTermList(variables, arguments);
			this.match(Token.CLOSE_PAR);
		}

		return new Function(
				FunctionSymbol.intern(lexeme, arguments.size()),
				arguments);
	}

	/**
	 * <pre>{@code E ::= B (('+' | '-') B)*}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read

	 */
	private Term parseExpression(Map<String, Variable> variables) throws IOException {
		return this.parseExpressionWithMetadata(variables).term();
	}

	/**
	 * Parses an expression and records whether it contains a top-level arithmetic
	 * operator. This distinguishes an ordinary atom from an arithmetic
	 * expression when no equality operator follows it.
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the parsed expression and its top-level operator metadata
	 */
	private ParsedExpression parseExpressionWithMetadata(Map<String, Variable> variables) throws IOException {
		ParsedExpression firstProduct = this.parseProduct(variables);
		Term expression = firstProduct.term();
		boolean hasTopLevelOperator = firstProduct.hasTopLevelOperator();

		while (this.lookahead.token() == Token.PLUS || this.lookahead.token() == Token.MINUS) {
			Token token = this.lookahead.token();
			String operator = this.lookahead.attribute().toString();
			this.match(token);
			Term rightOperand = this.parseProduct(variables).term();
			expression = this.createBinaryFunction(operator, expression, rightOperand);
			hasTopLevelOperator = true;
		}

		return new ParsedExpression(expression, hasTopLevelOperator);
	}

	/**
	 * <pre>{@code B ::= T (('*' | '/') T)*}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 */
	private ParsedExpression parseProduct(Map<String, Variable> variables) throws IOException {
		Term product = this.parseTerm(variables);
		boolean hasTopLevelOperator = false;

		while (this.lookahead.token() == Token.TIMES || this.lookahead.token() == Token.DIV) {
			Token token = this.lookahead.token();
			String operator = this.lookahead.attribute().toString();
			this.match(token);
			Term rightOperand = this.parseTerm(variables);
			product = this.createBinaryFunction(operator, product, rightOperand);
			hasTopLevelOperator = true;
		}

		return new ParsedExpression(product, hasTopLevelOperator);
	}

	/**
	 * Builds a binary function application.
	 *
	 * @param operator the root-symbol name
	 * @param leftOperand the first argument
	 * @param rightOperand the second argument
	 * @return the constructed function
	 */
	private Function createBinaryFunction(String operator, Term leftOperand, Term rightOperand) {
		return new Function(FunctionSymbol.intern(operator, 2), List.of(leftOperand, rightOperand));
	}

	/**
	 * <pre>{@code T ::= F | var | anonymous_var | num | Li | Tu}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 */
	private Term parseTerm(Map<String, Variable> variables) throws IOException {
		Token token = this.lookahead.token();
		if (token == Token.ID)
			return this.parseFunction(variables);
		if (token == Token.VAR) {
			String lexeme = this.lookahead.attribute().toString();
			this.match(token);
			return variables.computeIfAbsent(lexeme, ignored -> new Variable());
		}
		if (token == Token.NUM) {
			String lexeme = this.lookahead.attribute().toString();
			this.match(token);
			return new Function(FunctionSymbol.intern(lexeme, 0), List.of());
		}
		if (token == Token.ANONYMOUS_VAR) {
			this.match(token);
			return new Variable();
		}
		if (token == Token.OPEN_SQ_PAR)
			return this.parseList(variables);
		return this.parseTuple(variables);
	}

	/**
	 * <pre>{@code Li ::= '[' ']' | '[' Lt ']' | '[' Lt '|' E ']'}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @return the Prolog list that has been read
	 */
	private PrologList parseList(Map<String, Variable> variables) throws IOException {
		this.match(Token.OPEN_SQ_PAR);
		if (this.lookahead.token() == Token.CLOSE_SQ_PAR) {
			this.match(Token.CLOSE_SQ_PAR);
			return PrologList.emptyPrologList();
		}

		List<Term> elements = new ArrayList<>();
		this.parseTermList(variables, elements);
		Token token = this.lookahead.token();
		if (token == Token.CLOSE_SQ_PAR) {
			this.match(token);
			return new PrologList(elements);
		}
		if (token == Token.PIPE) {
			this.match(token);
			Term suffix = this.parseExpression(variables);
			this.match(Token.CLOSE_SQ_PAR);
			return new PrologList(elements, suffix);
		}
		int lineNumber = this.scanner.getLineno();
		throw new SyntaxException("syntax error: non-ended list at line " + lineNumber, lineNumber);
	}

	/**
	 * <pre>{@code Tu ::= '(' Lt ')'}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 */
	private PrologTuple parseTuple(Map<String, Variable> variables) throws IOException {
		this.match(Token.OPEN_PAR);
		List<Term> elements = new ArrayList<>();
		this.parseTermList(variables, elements);
		this.match(Token.CLOSE_PAR);

		return new PrologTuple(elements);
	}

	/**
	 * <pre>{@code Lt ::= E | E ',' Lt}</pre>
	 *
	 * @param variables the set of variables that have been encountered so far
	 * @param terms the list of terms to fill
	 */
	private void parseTermList(Map<String, Variable> variables, List<Term> terms) throws IOException {
		while (true) {
			terms.add(this.parseExpression(variables));
			if (this.lookahead.token() != Token.COMMA)
				return;
			this.match(Token.COMMA);
		}
	}

	/**
	 * An expression together with the presence of an arithmetic operator at its
	 * top level.
	 *
	 * @param term the parsed term
	 * @param hasTopLevelOperator whether a top-level arithmetic operator was
	 *        parsed
	 */
	private record ParsedExpression(Term term, boolean hasTopLevelOperator) {
	}
}
