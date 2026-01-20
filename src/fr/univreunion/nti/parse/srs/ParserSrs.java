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

package fr.univreunion.nti.parse.srs;

import java.io.IOException;
import java.util.LinkedList;

import fr.univreunion.nti.parse.Parser;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A parser for processing files storing Term or String Rewrite Systems
 * (old, human readable, format).
 * 
 * Tokens with corresponding lexemes:
 *   done       = {EOF}
 *   rules      = {RULES}
 *   strategy   = {STRATEGY}
 *   leftmost   = {LEFTMOST}
 *   rightmost  = {RIGHTMOST}
 *   id         = non-empty sequences of characters except space,
 *                '(', ')', '"', ',' and excluding special sequence
 *                '->' and keyword RULES
 *   string    = '"' . any_character* . '"'
 * 
 * Start symbol = Spec
 *
 * Rules:
 *   Spec  -> '(' Decl ')' Spec  |  done
 *   Decl  -> rules Lr  |  rules |  strategy S  | id L
 *   L     -> '->' L  |  id L  |  string L  | '(' L ')' L
 *          |  ',' L  |  epsilon
 *   Lr    -> R ',' Lr  |  R
 *   R     -> W '->' W | W '->'
 *   W     -> id | id W 
 *   S     -> leftmost  |  rightmost
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParserSrs extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final LinkedList<RuleTrs> rules = new LinkedList<RuleTrs>();

	/**
	 * The rewriting strategy (standard, innermost, ...) 
	 * considered for the program to be built.
	 * 
	 * Default value is FULL (standard rewriting).
	 */
	private String strategy = "FULL";
	
	/**
	 * Builds a parser for TRS (old, human readable, format).
	 * 
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserSrs(String progName, Scanner scanner) {
		super(progName, scanner);
	}

	/**
	 * Parses the input and builds a program from it.
	 * If a problem occurs while reading the input, then
	 * an IOException is thrown.
	 * 
	 * @return the program constructed from the input
	 * @throws IOException
	 */
	@Override
	public Program parse() throws IOException {
		this.lookahead = this.scanner.nextToken();
		this.Spec();

		return new Trs(this.progName, this.rules, this.strategy);

	}

	/**
	 * Spec -> '(' Decl ')' Spec  |  done
	 * 
	 * @throws IOException
	 */
	private void Spec() throws IOException {
		Token token = this.lookahead.getToken();
		if (token == Token.OPEN_PAR) {
			this.match(token);
			this.Decl();
			this.match(Token.CLOSE_PAR);
			this.Spec();
		}
		else if (token != Token.DONE)
			throw new RuntimeException("syntax error at line " + this.scanner.getLineno());
	}

	/**
	 * Decl -> rules Lr | rules | strategy S | id L
	 * 
	 * @throws IOException
	 */
	private void Decl() throws IOException {
		Token token = this.lookahead.getToken();
		if (token == Token.RULES) {
			this.match(token);
			if (this.lookahead.getToken() == Token.ID)
				this.Lr();
		}
		else if (token == Token.STRATEGY) {
			this.match(token);
			this.strategy = this.S();
		}
		else if (token == Token.ID) {
			this.match(token);
			this.L();
		}
		else
			throw new RuntimeException("syntax error at line " + this.scanner.getLineno());
	}

	/**
	 * L -> '->' L | id L | string L | '(' L ')' L | ',' L | epsilon
	 * 
	 * @throws IOException
	 */
	private void L() throws IOException {
		Token token = this.lookahead.getToken();
		if (token == Token.ARROW || token == Token.ID || token == Token.STRING) {
			this.match(token);
			this.L();
		}
		else if (token == Token.OPEN_PAR) {
			this.match(token);
			this.L();
			this.match(Token.CLOSE_PAR);
			this.L();
		}
		else if (token == Token.COMMA) {
			this.match(token);
			this.L();
		}
		// production L -> epsilon : nothing to do
	}

	/**
	 * Lr -> R ',' Lr  |  R
	 * 
	 * @throws IOException
	 */
	private void Lr() throws IOException {
		this.rules.addLast(this.R());
		if (this.lookahead.getToken() == Token.COMMA) {
			this.match(Token.COMMA);
			if (this.lookahead.getToken() == Token.ID)
				this.Lr();
			else
				throw new RuntimeException(Token.ID + " expected, " +
						this.lookahead.getToken() + " found instead at line " +
						this.scanner.getLineno());
		}	
		else			
			return;
	}

	/**
	 * R -> W '->' W | W '->'
	 * 
	 * @return the rule that has been read
	 * @throws IOException
	 */
	private RuleTrs R() throws IOException {
		Function left;
		Term right;

		Variable X = new Variable();
		left = this.W(X);
		this.match(Token.ARROW);
		if (this.lookahead.getToken() == Token.ID)
			right = this.W(X);
		else
			right = X;

		return new RuleTrs(left, right);
	}

	/**
	 * W -> id | id W
	 * 
	 * @param X the variable used when converting the word into a term
	 * @return the word that has been read
	 * @throws IOException
	 */
	private Function W(Variable X) throws IOException {
		Function t = null;

		if (this.lookahead.getToken() == Token.ID) {
			String lexeme = (String) this.lookahead.getAttribute();
			this.match(Token.ID);
			LinkedList<Term> argument = new LinkedList<Term>();
			if (this.lookahead.getToken() == Token.ID)
				argument.add(this.W(X));
			else
				argument.add(X);
			t = new Function(FunctionSymbol.getInstance(lexeme, 1), argument);
		}
		else
			throw new RuntimeException("missing id at line " + this.scanner.getLineno());

		return t;
	}
	
	/**
	 * S -> leftmost | rightmost
	 *  
	 * @throws IOException
	 */
	private String S() throws IOException {
		// The string to be returned.
		String result = null;
		
		if (this.lookahead.getToken() == Token.LEFTMOST) {
			result = this.lookahead.getAttribute().toString();
			this.match(Token.LEFTMOST);
		}
		else if (this.lookahead.getToken() == Token.RIGHTMOST) {
			result = this.lookahead.getAttribute().toString();
			this.match(Token.RIGHTMOST);
		}
		else
			throw new RuntimeException(
					"error at line " + this.scanner.getLineno() +
					": unknown strategy " + this.lookahead.getAttribute());
		
		return result;
	}
}
