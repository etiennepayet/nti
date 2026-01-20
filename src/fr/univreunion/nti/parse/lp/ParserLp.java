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

package fr.univreunion.nti.parse.lp;

import java.io.IOException;
import java.util.LinkedList;
import java.util.HashMap;

import fr.univreunion.nti.parse.Parser;
import fr.univreunion.nti.parse.Scanner;
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
 * A parser for logic programs.
 * 
 * Tokens and lexemes:
 *   done          = {EOF}
 *   id            = lowercase_letter.(digit + letter + '_')*
 *   var           = (uppercase_letter + '_').(digit + letter + '_')^+
 *   anonymous_var = '_'
 *   int           = digit.digit*
 *   mode          = { '%query:' }
 *
 * Non-terminal symbols:
 *   Lr   = list of rules (start symbol),
 *   R    = rule,
 *   U    = Prolog directive,
 *   M    = declaration of a mode
 *   La   = list of atoms or functions,
 *   A    = atom,
 *   F    = function,
 *   E    = arithmetic expression consisting of +, - and terms
 *   B    = arithmetic sub-expression consisting of *, / and terms
 *   T    = term,
 *   Li   = Prolog list,
 *   Tu   = Prolog tuple,
 *   Lt   = list of terms
 *
 * Rules:
 *   Lr   -> R Lr | U Lr | M Lr | done
 *   R    -> F '.'  |  F ':-' La '.'
 *   U    -> ':-' A '.'
 *   M    -> mode F '.'
 *   La   -> A  |  A ',' La
 *   
 *   A    -> F  |  E = E
 *   F    -> id  |  id Tu
 *   E    -> B + E  |  B - E  |  B 
 *   B    -> T * B  |  T / B  |  T 
 *   T    -> F | var | anonymous_var | int | Li | Tu
 *   Li   -> '[' ']'  |  '[' Lt ']'  |  '[' Lt '|' E ']'
 *   Tu   -> '(' Lt ')'
 *   Lt   -> E  |  E ',' Lt
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParserLp extends Parser {

	/**
	 * The rules of the program to be built.
	 */
	private final LinkedList<RuleLp> rules = new LinkedList<RuleLp>();

	/**
	 * The modes of the program to be built.
	 */
	private final LinkedList<Mode> modes = new LinkedList<Mode>();
	
	/**
	 * A flag indicating whether the unification operator '='
	 * occurs in the program to be built. If this flag is true
	 * after parsing the program, then a rule of the form '=(X,X).'
	 * is added to the program.
	 */
	private boolean eqOccurs = false;

	/**
	 * Builds a parser for logic programs.
	 * 
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserLp(String progName, Scanner scanner) {
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
		// First, we parse the file storing the program.
		this.lookahead = this.scanner.nextToken();
		this.Lr();
		if (this.eqOccurs) {
			// We add a rule of the form '=(X,X).' to the program.
			LinkedList<Term> arguments = new LinkedList<Term>();
			Variable X = new Variable();
			arguments.add(X); arguments.add(X);
			this.rules.add(
					new RuleLp(
							new Function(FunctionSymbol.getInstance("=", 2), arguments)));
		}

		return new Lp(this.progName, this.rules, this.modes);
	}

	/**
	 * Lr -> R Lr | U Lr | M Lr | done
	 * 
	 * @throws IOException
	 */
	private void Lr() throws IOException {
		Token token = this.lookahead.getToken(); 
		if (token == Token.ID) {
			this.rules.addLast(this.R());
			this.Lr();
		}
		else if (token == Token.ARROW) {
			this.U();
			this.Lr();
		}
		else if (token == Token.MODE) {
			this.M();
			this.Lr();
		}
		else if (token != Token.DONE)
			throw new RuntimeException("syntax error at line " + this.scanner.getLineno());
	}

	/**
	 * R -> F '.'  | F ':-' La '.'
	 * 
	 * @return the rule that has been read
	 * @throws IOException
	 */
	private RuleLp R() throws IOException {
		HashMap<String,Variable> variables = new HashMap<String,Variable>();

		Function head = this.F(variables);
		LinkedList<Function> body = new LinkedList<Function>();
		if (this.lookahead.getToken() == Token.ARROW) {
			this.match(Token.ARROW);
			this.La(variables, body);
		}
		this.match(Token.DOT);

		Function[] B = new Function[body.size()];
		int index = 0;
		for (Function A: body)
			B[index++] = A;
		
		return new RuleLp(head, B);
	}

	/**
	 * U -> ':-' A '.'
	 * 
	 * @throws IOException
	 */
	private void U() throws IOException {
		this.match(Token.ARROW);
		this.A(new HashMap<String,Variable>());
		this.match(Token.DOT);  
	}

	/**
	 * M -> mode F '.'
	 * 
	 * @throws IOException
	 */
	private void M() throws IOException {
		this.match(Token.MODE);
		this.modes.add(new Mode(this.F(new HashMap<String,Variable>())));
		this.match(Token.DOT);
	}

	/**
	 * La -> A  |  A ',' La
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @param L the list of atoms to fill
	 * @throws IOException
	 */
	private void La(HashMap<String,Variable> variables, LinkedList<Function> L)  throws IOException {
		L.addLast(this.A(variables));
		if (this.lookahead.getToken() == Token.COMMA) {
			this.match(Token.COMMA);
			this.La(variables, L);
		}
	}

	/**
	 * A -> F  |  E = E 
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the atom that has been read
	 * @throws IOException
	 */
	private Function A(HashMap<String,Variable> variables) throws IOException {
		Function f = null;

		if (this.lookahead.getToken() == Token.ID) {
			Function t = this.F(variables);
			if (this.lookahead.getToken() == Token.EQ) {
				LinkedList<Term> argumentList = new LinkedList<Term>();

				argumentList.add(t);
				this.match(Token.EQ);
				argumentList.add(this.E(variables));

				f = new Function(FunctionSymbol.getInstance("=", 2), argumentList);

				this.eqOccurs = true;
			}
			else f = t;
		}
		else {
			LinkedList<Term> argumentList = new LinkedList<Term>();

			argumentList.add(this.E(variables));
			this.match(Token.EQ);
			argumentList.add(this.E(variables));

			f = new Function(FunctionSymbol.getInstance("=", 2), argumentList);

			this.eqOccurs = true;
		}

		return f;
	}

	/**
	 * F -> id  |  id '(' Lt ')'
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the atom that has been read
	 * @throws IOException
	 */
	private Function F(HashMap<String,Variable> variables) throws IOException {
		LinkedList<Term> argumentList = new LinkedList<Term>();

		String lexeme = this.lookahead.getAttribute().toString();
		this.match(Token.ID);

		if (this.lookahead.getToken() == Token.OPEN_PAR) { 
			this.match(Token.OPEN_PAR);
			this.Lt(variables, argumentList);
			this.match(Token.CLOSE_PAR);
		}

		return new Function(
				FunctionSymbol.getInstance(lexeme, argumentList.size()),
				argumentList);
	}
	
	/**
	 * E -> B + E  |  B - E  |  B
	 *  
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 * @throws IOException
	 */
	private Term E(HashMap<String,Variable> variables) throws IOException {
		Term t = this.B(variables);

		Token token = this.lookahead.getToken();
		if (token == Token.PLUS || token == Token.MINUS) {
			String lexeme = this.lookahead.getAttribute().toString();
			this.match(token);

			LinkedList<Term> argumentList = new LinkedList<Term>();
			argumentList.add(t);
			argumentList.add(this.E(variables));

			t = new Function(
					FunctionSymbol.getInstance(lexeme, argumentList.size()),
					argumentList);
		}

		return t;
	}
	
	/**
	 * 	B -> T * B  |  T / B  |  T
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 * @throws IOException
	 */
	private Term B(HashMap<String,Variable> variables) throws IOException {
		Term t = this.T(variables);

		Token token = this.lookahead.getToken();
		if (token == Token.TIMES || token == Token.DIV) {
			String lexeme = this.lookahead.getAttribute().toString();
			this.match(token);

			LinkedList<Term> argumentList = new LinkedList<Term>();
			argumentList.add(t);
			argumentList.add(this.B(variables));

			t = new Function(
					FunctionSymbol.getInstance(lexeme, argumentList.size()),
					argumentList);
		}

		return t;
	}

	/**
	 * T -> F | var | anonymous_var | int | Li | Tu
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 * @throws IOException
	 */
	private Term T(HashMap<String,Variable> variables) throws IOException {
		Term t = null;

		Token token = this.lookahead.getToken();
		if (token == Token.ID)
			t = this.F(variables);
		else if (token == Token.VAR || token == Token.INT) {
			String lexeme = this.lookahead.getAttribute().toString();
			this.match(token);

			if (token == Token.VAR) {
				t = variables.get(lexeme);
				if (t == null) {
					t = new Variable();
					variables.put(lexeme, (Variable)t);
				}
			}
			else if (token == Token.INT)
				t = new Function(FunctionSymbol.getInstance(lexeme, 0),
						new LinkedList<Term>());
		}
		else if (token == Token.ANONYMOUS_VAR) {
			this.match(token);
			t = new Variable();
		}
		else if (token == Token.OPEN_SQ_PAR)
			t = this.Li(variables);
		else
			t = this.Tu(variables);

		return t;
	}

	/**
	 * Li -> '[' ']'  |  '[' Lt ']'  |  '[' Lt '|' E ']'
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the Prolog list that has been read
	 * @throws IOException
	 */
	private PrologList Li(HashMap<String,Variable> variables) throws IOException {
		PrologList L = null;

		this.match(Token.OPEN_SQ_PAR);
		if (this.lookahead.getToken() == Token.CLOSE_SQ_PAR) {
			// Li -> '[' ']'
			this.match(Token.CLOSE_SQ_PAR);
			L = PrologList.emptyPrologList();
		}
		else {
			LinkedList<Term> elements = new LinkedList<Term>();

			this.Lt(variables, elements);
			Token token = this.lookahead.getToken();
			if (token == Token.CLOSE_SQ_PAR) {
				// Li -> '[' Lt ']'
				this.match(token);
				L = new PrologList(elements);
			}
			else if (token == Token.PIPE) {
				// Li -> '[' Lt '|' E ']'
				this.match(token);
				L = new PrologList(elements, this.E(variables));
				this.match(Token.CLOSE_SQ_PAR);
			}
			else throw new RuntimeException("syntax error: non-ended list at line " + this.scanner.getLineno());  
		}
		return L;
	}
	
	/**
	 * Tu -> '(' Lt ')'
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @throws IOException
	 */
	private PrologTuple Tu(HashMap<String,Variable> variables) throws IOException {
		
		this.match(Token.OPEN_PAR);
		LinkedList<Term> argumentList = new LinkedList<Term>();
		this.Lt(variables, argumentList);
		this.match(Token.CLOSE_PAR);

		return new PrologTuple(argumentList);
	}

	/**
	 * Lt -> E  |  E ',' Lt
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @param L list of terms to fill
	 * @throws IOException
	 */
	private void Lt(HashMap<String,Variable> variables, LinkedList<Term> L) throws IOException {
		L.addLast(this.E(variables));
		if (this.lookahead.getToken() == Token.COMMA) {
			this.match(Token.COMMA);
			this.Lt(variables, L);
		}
	}
}
