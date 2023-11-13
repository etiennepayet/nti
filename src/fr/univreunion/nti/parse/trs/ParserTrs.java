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

package fr.univreunion.nti.parse.trs;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

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
 *   var        = {VAR}
 *   rules      = {RULES}
 *   strategy   = {STRATEGY}
 *   innermost  = {INNERMOST}
 *   outermost  = {OUTERMOST}
 *   id         = non-empty sequences of characters except space,
 *                '(', ')', '"', ',' and excluding special sequence
 *                '->' and keywords VAR and RULES
 *   string    = '"' . any_character* . '"'
 * 
 * Start symbol = Spec
 *
 * Rules:
 *   Spec  -> '(' Decl ')' Spec  |  done
 *   Decl  -> var Lid  |  rules Lr  |  strategy S  |  id L
 *   L     -> '->' L  |  id L  |  string L  | '(' L ')' L
 *          |  ',' L  |  epsilon
 *   Lid   -> id Lid | epsilon
 *   Lr    -> R  Lr  |  epsilon
 *   R     -> T '->' T
 *   T     -> id  |  id '(' ')'  |  id '(' Lt ')'
 *   Lt    -> T ',' Lt | epsilon
 *   S     -> innermost  |  outermost
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParserTrs extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final List<RuleTrs> rules = new LinkedList<RuleTrs>();

	/**
	 * The variables of the program to be built.
	 * They are declared using the <code>var</code>
	 * keyword. The following data structure is
	 * a dictionary { lexeme -> variable }.
	 */
	private final Map<String,Variable> variables = new HashMap<String,Variable>();

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
	public ParserTrs(String progName, Scanner scanner) {
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
	 * Spec  -> '(' Decl ')' Spec  |  done
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
	 * Decl  -> var Lid  |  rules Lr  |  strategy S  |  id L
	 * 
	 * @throws IOException
	 */
	private void Decl() throws IOException {
		Token token = this.lookahead.getToken();
		if (token == Token.VAR) {
			this.match(token);
			this.Lid();
		}
		else if (token == Token.RULES) {
			this.match(token);
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
	 * Lid -> id Lid | epsilon
	 * 
	 * @throws IOException
	 */
	private void Lid() throws IOException {
		if (this.lookahead.getToken() == Token.ID) {
			String lexeme = (String) this.lookahead.getAttribute();
			this.match(Token.ID);

			Variable v = this.variables.get(lexeme);
			if (v == null) {
				v = new Variable();
				this.variables.put(lexeme, v);
			}

			this.Lid();
		}
		// production L -> epsilon : nothing to do
	}

	/**
	 * Lr -> R Lr  |  epsilon
	 * 
	 * @throws IOException
	 */
	private void Lr() throws IOException {
		if (this.lookahead.getToken() == Token.ID) {
			this.rules.add(this.R());
			this.Lr();
		}
		// production L -> epsilon : nothing to do
	}

	/**
	 * R -> T '->' T
	 * 
	 * @return the rule that has been read
	 * @throws IOException
	 */
	private RuleTrs R() throws IOException {
		Term left = this.T();

		if (!(left instanceof Function))
			throw new RuntimeException("error at line " +
					this.scanner.getLineno() +
					": left-hand side of rule cannot be a variable");

		this.match(Token.ARROW);
		Term right = this.T();

		return new RuleTrs((Function) left, right, this.rules.size() + 1); 
	}

	/**
	 * T -> id  |  id '(' ')'  |  id '(' Lt ')'
	 * 
	 * @return the term that has been read
	 * @throws IOException
	 */
	private Term T() throws IOException {
		String lexeme = (String) this.lookahead.getAttribute();
		this.match(Token.ID);

		// The term to be returned.
		Term result = this.variables.get(lexeme); // Have we read a variable symbol?

		if (result == null) {
			// Here, we have not read a variable symbol,
			// so necessarily we have read a function symbol.
			List<Term> argumentList = new LinkedList<Term>(); 
			if (this.lookahead.getToken() == Token.OPEN_PAR) {
				this.match(Token.OPEN_PAR);
				if (this.lookahead.getToken() != Token.CLOSE_PAR)
					this.Lt(argumentList);
				this.match(Token.CLOSE_PAR);
			}
			// The function to be returned:
			result = new Function(
					FunctionSymbol.getInstance(lexeme, argumentList.size()),
					argumentList);
		}

		return result;
	}

	/**
	 * Lt -> T ',' Lt | T
	 * 
	 * @param L the list of terms to fill
	 * @throws IOException
	 */
	private void Lt(List<Term> L) throws IOException {
		L.add(this.T());
		if (this.lookahead.getToken() == Token.COMMA) {
			this.match(Token.COMMA);
			this.Lt(L);
		}
	}
	
	/**
	 * S -> innermost  |  outermost
	 *  
	 * @throws IOException
	 */
	private String S() throws IOException {
		// The string to be returned.
		String result = null;
		
		if (this.lookahead.getToken() == Token.INNERMOST) {
			result = this.lookahead.getAttribute().toString();
			this.match(Token.INNERMOST);
		}
		else if (this.lookahead.getToken() == Token.OUTERMOST) {
			result = this.lookahead.getAttribute().toString();
			this.match(Token.OUTERMOST);
		}
		else
			throw new RuntimeException(
					"error at line " + this.scanner.getLineno() +
					": unknown strategy " + this.lookahead.getAttribute());
		
		return result;
	}
}
