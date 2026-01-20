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

package fr.univreunion.nti.parse.ari;

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
 * A parser for processing files storing Term or String Rewrite Systems in
 * the <A HREF="https://termination-portal.org/wiki/Term_Rewriting">ARI</A>
 * format.
 * 
 * Tokens with corresponding lexemes:
 *   done   = {EOF}
 *   format = {format}
 *   trs    = {TRS}
 *   fun    = {fun}
 *   id     = non-empty sequences of characters except
 *            spaces, '(', ')', ';' and ':'
 *            must not be a keyword (fun, format, rule)
 *            may be enclosed in two '|'
 *   int    = non-empty sequences of digits
 *   
 * Start symbol = A (standing for ARI-format)
 * 
 * Rules:
 *   A -> '(' format trs ')' L done
 *   L -> ( '(' F ')' )^*  ( '(' R ')' )^*
 *   F -> fun id int
 *   R -> rule T T
 *   T -> id | '(' id T^+ ')'
 * 
 * - Comments start with a semicolon (';') and end with \n.
 *   They can occur anywhere.
 * - Function symbols and their arities are declared by (fun f n).
 * - Function symbols must be declared once.
 *   Undeclared identifiers are regarded as variables.
 *   In terms, function symbols must be used with
 *   the same number of arguments as specified in
 *   their arities. 
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParserAri extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final List<RuleTrs> rules = new LinkedList<RuleTrs>();

	/**
	 * The variables of the program to be built.
	 * The following data structure is a dictionary
	 * of the form { lexeme -> variable }.
	 */
	private final Map<String,Variable> variables =
			new HashMap<String,Variable>();

	/**
	 * The rewriting strategy (standard, innermost, ...) 
	 * considered for the program to be built.
	 * 
	 * Default value is FULL (standard rewriting).
	 */
	private final String strategy = "FULL";

	/**
	 * Builds a parser for TRSs/SRSs (ARI format).
	 * 
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserAri(String progName, Scanner scanner) {
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
	public Program parse() throws IOException {
		this.lookahead = this.scanner.nextToken();
		this.A();

		return new Trs(this.progName, this.rules, this.strategy);
	}

	/**
	 * A -> '(' format trs ')' L done
	 * 
	 * @throws IOException
	 */
	private void A() throws IOException {
		this.match(Token.OPEN_PAR);
		this.match(Token.FORMAT);
		this.match(Token.TRS);
		this.match(Token.CLOSE_PAR);

		this.L();
		
		this.match(Token.DONE);
	}

	/**
	 * L -> ( '(' F ')' )^*  ( '(' R ')' )^*
	 * 
	 * @throws IOException
	 */
	private void L() throws IOException {
		boolean fun = true;

		while (this.lookahead.getToken() == Token.OPEN_PAR) {
			this.match(Token.OPEN_PAR);

			if (fun && this.lookahead.getToken() == Token.FUN) 
				this.F();
			else if (this.lookahead.getToken() == Token.RULE) {
				// Once we have read a rule, we cannot read
				// a function symbol declaration anymore:
				fun = false; 
				this.R();
			}
			else
				throw new RuntimeException("error at line " +
						this.scanner.getLineno() + ": " +
						(fun ? "'fun' or " : "") +
						"'rule' expected");

			this.match(Token.CLOSE_PAR);
		}
	}

	/**
	 * F -> fun id int
	 * 
	 * @throws IOException
	 */
	private void F() throws IOException {
		this.match(Token.FUN);
		
		Object lexeme = this.lookahead.getAttribute();
		this.match(Token.ID);
		
		Object arity = this.lookahead.getAttribute(); 
		this.match(Token.INT);
		
		// We insert the function symbol that
		// has been read in the symbol table:
		FunctionSymbol.getInstance((String) lexeme, (int) arity);
	}

	/**
	 * R -> rule T T
	 * 
	 * @throws IOException
	 */
	private void R() throws IOException {
		this.match(Token.RULE);

		Term left = this.T();
		if (!(left instanceof Function))
			throw new RuntimeException("error at line " +
					this.scanner.getLineno() +
					": left-hand side of rule cannot be a variable");

		Term right = this.T();

		this.rules.add(new RuleTrs((Function) left, right));
	}

	/**
	 * T -> id | '(' id T^+ ')'
	 * 
	 * @return the term that has been read
	 * @throws IOException
	 */
	private Term T() throws IOException {
		// The term to be returned.
		Term result = null;

		if (this.lookahead.getToken() == Token.ID) {
			String lexeme = (String) this.lookahead.getAttribute();
			this.match(Token.ID);
			FunctionSymbol funsymbol = FunctionSymbol.get(lexeme, 0);
			if (funsymbol == null) {
				// The identifier is not declared,
				// hence it is a variable.
				Variable v = this.variables.get(lexeme); // Have we already met this variable?
				if (v == null) {
					// No, this variable has not been met before.
					v = new Variable();
					this.variables.put(lexeme, v);
				}
				result = v;
			}
			else
				// The identifier is declared.
				result = new Function(funsymbol, new LinkedList<Term>());
		}
		else {
			this.match(Token.OPEN_PAR);

			Object lexeme = this.lookahead.getAttribute();
			this.match(Token.ID);

			List<Term> argumentList = new LinkedList<Term>();
			Token tok = null;
			do {
				argumentList.add(this.T());
				tok = this.lookahead.getToken();
			}
			while (tok == Token.ID || tok == Token.OPEN_PAR);

			this.match(Token.CLOSE_PAR);

			int arity = argumentList.size();
			FunctionSymbol funsymbol = FunctionSymbol.get((String)lexeme, arity);
			if (funsymbol == null)
				// Here, id cannot be a variable,
				// hence it must have been declared
				// before.
				throw new RuntimeException(
						"error at line " + this.scanner.getLineno() +
						": undeclared identifier " + lexeme + " of arity " + arity);
			result = new Function(funsymbol, argumentList);
		}

		return result;
	}
}
