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

package fr.univreunion.nti.parse.xml;

import java.io.IOException;
import java.util.LinkedList;
import java.util.HashMap;

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
 * A parser for processing XML files storing Term or String Rewrite Systems.
 * 
 * Tokens with corresponding lexemes:
 *   done          = {EOF}
 *   anything      = *
 *   xml           = {<?xml ... ?>}
 *   xmlStyleSheet = {<?xml-stylesheet ... ?>}
 *   problem       = {<problem ... >}
 *   endProblem    = {</problem>}
 *   trs           = {<trs ... >}
 *   endTrs        = {</trs>}
 *   rules         = {<rules ... >}
 *   endRules      = {</rules>}
 *   rule          = {<rule ... >}
 *   endRule       = {</rule>}
 *   lhs           = {<lhs ... >}
 *   endLhs        = {</lhs>}
 *   rhs           = {<rhs ... >}
 *   endRhs        = {</rhs>}
 *   var           = {<var ... >}
 *   endVar        = {</var>}
 *   funapp        = {<funapp ... >}
 *   endFunapp     = {</funapp>}
 *   name          = {<name ... >}
 *   endName       = {</name>}
 *   arg           = {<arg ... >}
 *   endArg        = {</arg>}
 *   sig           = {<signature ...>}
 *   endSig        = {</signature}
 *   funcsym       = {<funcsym ... >}
 *   endFuncsym    = {</funcsym>}
 *   arity         = {<arity ...>}
 *   endArity      = {</arity>}
 *   strategy      = {<strategy ...>}
 *   endStrategy   = {</strategy>}
 *   metainfo      = {<metainformation ...>}
 *   endMetainfo   = {</metainformation>}
 *   filename      = {<originalfilename ...>}
 *   endFilename   = {</originalfilename>}
 *   id            = non-empty sequences of characters except spaces and '<'
 *   int           = non-empty sequences of digits
 *                
 * Start symbol = S
 * 
 * Rules:
 *   S     -> X
 *            problem
 *              trs
 *                rules Lr endRules
 *                sig Lsymb endSig
 *              endTrs
 *              strategy id endStrategy
 *              M
 *            endProblem
 *   X     -> xml | xml xmlStyleSheet
 *   Lr    -> epsilon | R Lr
 *   R     -> rule lhs F endLhs rhs T endRhs endRule
 *   T     -> V | F
 *   V     -> var id endVar
 *   F     -> funapp name id endName Largs endFunapp
 *   Largs -> epsilon | arg T endArg Largs
 *   Lsymb -> epsilon | Symb Lsymb
 *   Symb  -> funcsym name id endName arity int endArity endFuncsym
 *   M     -> epsilon | metainfo anything endMetainfo
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParserXml extends Parser {

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
	 * Builds a parser for TRS/SRS (XML format).
	 * 
	 * @param progName the name of the program to build
	 * @param scanner the scanner reading the input
	 */
	public ParserXml(String progName, Scanner scanner) {
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
		this.S();

		return new Trs(this.progName, this.rules, this.strategy);
	}

	/**
	 * S -> X
	 *      problem
	 *        trs
	 *          rules Lr endRules
	 *          sig Lsymb endSig
	 *        endTrs
	 *        strategy id endStrategy
	 *        M
	 *      endProblem
	 * 
	 * @throws IOException
	 */
	private void S() throws IOException {
		this.X();
		this.match(Token.OPEN_PROBLEM_TAG);

		this.match(Token.OPEN_TRS_TAG);
		this.match(Token.OPEN_RULES_TAG);
		this.Lr();
		this.match(Token.CLOSE_RULES_TAG);
		this.match(Token.OPEN_SIGN_TAG);
		this.Lsymb();
		this.match(Token.CLOSE_SIGN_TAG);
		this.match(Token.CLOSE_TRS_TAG);

		this.match(Token.OPEN_STRATEGY_TAG);
		this.strategy = this.lookahead.getAttribute().toString();
		this.match(Token.ID);
		this.match(Token.CLOSE_STRATEGY_TAG);

		this.M();

		this.match(Token.CLOSE_PROBLEM_TAG);
	}

	/**
	 * X -> xml | xml xmlStyleSheet
	 * 
	 * @throws IOException
	 */
	private void X() throws IOException {
		this.match(Token.XML_TAG);
		if (this.lookahead.getToken() == Token.XML_STYLESHEET_TAG)
			this.match(Token.XML_STYLESHEET_TAG);
	}

	/**
	 * Lr -> epsilon | R Lr
	 * 
	 * @throws IOException
	 */
	private void Lr() throws IOException {
		if (this.lookahead.getToken() == Token.OPEN_RULE_TAG) {
			rules.addLast(this.R());
			this.Lr();
		}
		// production Lr -> epsilon : nothing to do
	}

	/**
	 * R -> rule lhs T endLhs rhs T endRhs endRule
	 * 
	 * @return the rule that has been read
	 * @throws RuntimeException if the rule is not a
	 * valid rewrite rule
	 * @throws IOException
	 */
	private RuleTrs R() throws IOException {
		this.match(Token.OPEN_RULE_TAG);		

		HashMap<String,Variable> variables = new HashMap<String,Variable>();

		this.match(Token.OPEN_LHS_TAG);
		Function lhs = this.F(variables);
		this.match(Token.CLOSE_LHS_TAG);

		this.match(Token.OPEN_RHS_TAG);
		Term rhs = this.T(variables);
		this.match(Token.CLOSE_RHS_TAG);

		this.match(Token.CLOSE_RULE_TAG);

		return new RuleTrs(lhs, rhs);
	}

	/**
	 * T -> V | F
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 * @throws IOException
	 */
	private Term T(HashMap<String,Variable> variables) throws IOException {
		Token token = this.lookahead.getToken();
		if (token == Token.OPEN_VAR_TAG) 
			return this.V(variables);
		else if (token == Token.OPEN_FUNAPP_TAG)
			return this.F(variables);
		else
			throw new RuntimeException("<var> or <funapp> expected at line " + this.scanner.getLineno());
	}

	/**
	 * V -> var id endVar
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the variable that has been read
	 * @throws IOException
	 */
	private Variable V(HashMap<String,Variable> variables) throws IOException {
		this.match(Token.OPEN_VAR_TAG);
		String lexeme = this.lookahead.getAttribute().toString();
		this.match(Token.ID);
		this.match(Token.CLOSE_VAR_TAG);

		Variable v = variables.get(lexeme);
		if (v == null) {
			v = new Variable();
			variables.put(lexeme, v);
		}

		return v;
	}	

	/**
	 * F -> funapp name id endName Largs endFunapp
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the function that has been read
	 * @throws IOException
	 */
	private Function F(HashMap<String,Variable> variables) throws IOException {
		this.match(Token.OPEN_FUNAPP_TAG);

		// The root symbol:
		this.match(Token.OPEN_NAME_TAG);
		String lexeme = this.lookahead.getAttribute().toString();
		this.match(Token.ID);
		this.match(Token.CLOSE_NAME_TAG);

		// The arguments:
		LinkedList<Term> argumentList = new LinkedList<Term>();
		this.Largs(variables, argumentList);

		// The term to be returned:
		Function f = new Function(
				FunctionSymbol.getInstance(lexeme, argumentList.size()),
				argumentList);

		this.match(Token.CLOSE_FUNAPP_TAG);

		return f;
	}

	/**
	 * Largs -> epsilon | arg T endArg Largs
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @param L the list of terms (arguments) to fill
	 * @throws IOException
	 */
	private void Largs(HashMap<String,Variable> variables, LinkedList<Term> L) throws IOException {
		if (this.lookahead.getToken() == Token.OPEN_ARG_TAG) {
			this.match(Token.OPEN_ARG_TAG);
			L.addLast(this.T(variables));
			this.match(Token.CLOSE_ARG_TAG);
			this.Largs(variables, L);
		}
		// production Largs -> epsilon : nothing to do
	}

	/**
	 * Lsymb -> epsilon | Symb Lsymb
	 * 
	 * @throws IOException
	 */
	private void Lsymb() throws IOException {
		if (this.lookahead.getToken() == Token.OPEN_FUNCSYM_TAG) {
			this.Symb();
			this.Lsymb();
		}
		// production Lsymb -> epsilon : nothing to do
	}	

	/**
	 * Symb -> funcsym name id endName arity int endArity endFuncsym
	 * 
	 * @throws IllegalArgumentException if the specified arity is not
	 * a positive integer
	 * @throws IOException
	 */
	private void Symb() throws IOException {
		this.match(Token.OPEN_FUNCSYM_TAG);

		this.match(Token.OPEN_NAME_TAG);
		this.match(Token.ID);
		this.match(Token.CLOSE_NAME_TAG);

		this.match(Token.OPEN_ARITY_TAG);
		String lexeme = this.lookahead.getAttribute().toString();
		this.match(Token.ID);
		try {
			if (Integer.parseInt(lexeme) < 0)
				throw new IllegalArgumentException("arity at line " + this.scanner.getLineno() + " is not a positive integer");
		} catch (NumberFormatException e) {
			throw new IllegalArgumentException("arity at line " + this.scanner.getLineno() + " is not an integer");
		}
		this.match(Token.CLOSE_ARITY_TAG);

		this.match(Token.CLOSE_FUNCSYM_TAG);
	}

	/**
	 * M -> epsilon | metainfo anything endMetainfo
	 *          
	 * @throws IOException
	 */
	private void M() throws IOException {
		if (this.lookahead.getToken() == Token.OPEN_METAINFO_TAG) {
			this.match(Token.OPEN_METAINFO_TAG);
			Token lookahead;
			while ((lookahead = this.lookahead.getToken()) != Token.CLOSE_METAINFO_TAG)
				this.match(lookahead);
			this.match(Token.CLOSE_METAINFO_TAG);
		}
	}
}
