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

package fr.univreunion.nti.parse.string;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.parse.Parser;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.nonloop.iclp25.PatternRuleTrsIclp25;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.PrologList;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A parser for strings representing terms.
 * 
 * Mainly used for testing.
 * 
 * Tokens and lexemes:
 *   done          = {EOF}
 *   id            = lowercase_letter.(digit + letter + '_')*
 *   var           = (uppercase_letter + '_').(digit + letter + '_')^+
 *   anonymous_var = '_'
 *   int           = digit.digit*
 *
 * Non-terminal symbols:
 *   T    = term
 *   Lt   = list of terms
 *   F    = function
 *   Lf   = list of functions
 *   Li   = Prolog list
 *   Sub  = substitution
 *   Map  = mapping
 *   Lm   = list of mappings
 *   Rlp  = LP rule
 *   Rtrs = TRS rule
 *   Spatsub  = simple pattern substitution
 *   Spatterm = simple pattern term
 *   
 * Terms:
 *   Spatterm -> T Spatsub
 *   T  -> F | var | anonymous_var | int | Li
 *   F  -> id  |  id '(' Lt ')'
 *   Li -> '[' ']'  |  '[' Lt ']'  |  '[' Lt '|' T ']'
 *   Lt -> T  |  T ',' Lt
 *   
 * Substitutions:
 *   Spatsub  -> Sub Sub |  Sub Spatsub
 *   Sub -> '{' '}' | '{' Lm '}'
 *   Lm  -> Map  |  Map ',' Lm
 *   Map -> var '->' T
 *   
 * LP rules:
 *   Rlp -> F '.'  |  F ':-' Lf '.'
 *   Lf  -> F  |  F ',' Lf
 *   
 * TRS rules:
 *   Rtrs -> F '->' F | var
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParserString extends Parser {

	/**
	 * Builds a parser for strings representing terms.
	 */
	public ParserString() {
		this(null);
	}

	/**
	 * Builds a parser for strings representing terms.
	 * 
	 * @param scanner the scanner reading the input
	 */
	public ParserString(Scanner scanner) {
		super("", scanner);
	}

	/**
	 * Initializes this parser before parsing.
	 * 
	 * @param input the input to read
	 * @throws IOException
	 */
	private void init(String input) throws IOException {
		this.scanner = new ScannerString(input);
		this.lookahead = this.scanner.nextToken();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Program parse() throws IOException {
		throw new UnsupportedOperationException();
	}

	/**
	 * Parses the input and builds a term from it.
	 * If a problem occurs while reading the input,
	 * then an IOException is thrown.
	 * 
	 * The provided set of variables is completed
	 * with the variables of the constructed term.
	 * 
	 * @param input the input string to parse
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the term constructed from the input
	 * @throws IOException
	 */
	public Term parseTerm(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.mT(variables);
	}

	/**
	 * Parses the input and builds a substitution from it.
	 * If a problem occurs while reading the input, then
	 * an IOException is thrown.
	 * 
	 * The provided set of variables is completed with
	 * the variables of the constructed substitution.
	 * 
	 * @param input the input string to parse
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the substitution constructed from the input
	 * @throws IOException
	 */
	public Substitution parseSubstitution(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.mSub(variables);
	}

	/**
	 * Parses the input and builds a simple pattern
	 * substitution from it. If a problem occurs
	 * while reading the input then an exception
	 * is thrown.
	 * 
	 * The provided set of variables is completed
	 * with the variables of the constructed
	 * simple pattern substitution.
	 * 
	 * @param input the input string to parse
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the simple pattern substitution
	 * constructed from the input
	 * @throws IOException
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	public SimplePatternSubstitution parseSimplePatternSubstitution(
			String input, Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.mSpatsub(variables);
	}

	/**
	 * Parses the input and builds a simple pattern term
	 * from it. If a problem occurs while reading the input,
	 * then exception is thrown.
	 * 
	 * The provided set of variables is completed with
	 * the variables of the constructed simple pattern term.
	 * 
	 * @param input the input string to parse
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the simple pattern term constructed from
	 * the input
	 * @throws IOException
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	public SimplePatternTerm parseSimplePatternTerm(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.mSpatterm(variables);
	}

	/**
	 * Parses the input and builds a LP rule from it.
	 * If a problem occurs while reading the input, then
	 * an IOException is thrown.
	 * 
	 * The provided set of variables is completed with
	 * the variables of the constructed LP rule.
	 * 
	 * @param input the input string to parse
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the LP rule constructed from the input
	 * @throws IOException
	 */
	public RuleLp parseLpRule(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.mRlp(variables);
	}
	
	/**
	 * Parses the input and builds a TRS rule from it.
	 * If a problem occurs while reading the input, then
	 * an IOException is thrown.
	 * 
	 * The provided set of variables is completed with
	 * the variables of the constructed TRS rule.
	 * 
	 * @param input the input string to parse
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the TRS rule constructed from the input
	 * @throws IOException
	 */
	public RuleTrs parseTrsRule(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);
		return this.mRtrs(variables);
	}
	
	/**
	 * Parses the input and builds a pattern rule
	 * from it. If a problem occurs while reading
	 * the input, then exception is thrown.
	 * 
	 * The provided set of variables is completed
	 * with the variables of the constructed pattern
	 * rule.
	 * 
	 * @param input the input string to parse
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the simple pattern rule constructed
	 * from the input
	 * @throws IOException
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	public PatternRuleTrsIclp25 parsePatternRuleTrs(String input,
			Map<String, Variable> variables) throws IOException {

		this.init(input);

		SimplePatternTerm left = this.mSpatterm(variables);
		this.match(Token.ARROW);
		SimplePatternTerm right = this.mSpatterm(variables);

		return PatternRuleTrsIclp25.getInstance(left, right, 0);
	}
	
	/**
	 * Spatterm -> T Spatsub
	 * 
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the simple pattern term that has
	 * been read
	 * @throws IOException
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	private SimplePatternTerm mSpatterm(
			Map<String, Variable> variables) throws IOException {
		
		Term s = this.mT(variables);
		SimplePatternSubstitution theta = this.mSpatsub(variables);

		return SimplePatternTerm.getInstance(s, theta);
	}

	/**
	 * T -> F | var | anonymous_var | int | Li
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the term that has been read
	 * @throws IOException
	 */
	private Term mT(Map<String,Variable> variables) throws IOException {
		Term t = null;

		Token token = this.lookahead.getToken();
		if (token == Token.ID)
			t = this.mF(variables);
		else if (token == Token.VAR || token == Token.INT) {
			String lexeme = this.lookahead.getAttribute().toString();
			this.match(token);

			if (token == Token.VAR) {
				t = variables.get(lexeme);
				if (t == null) {
					t = new Variable();
					variables.put(lexeme, (Variable) t);
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
		else 
			t = this.mLi(variables);

		return t;
	}

	/**
	 * F -> id  |  id '(' Lt ')'
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the function that has been read
	 * @throws IOException
	 */
	private Function mF(Map<String,Variable> variables) throws IOException {
		LinkedList<Term> argumentList = new LinkedList<Term>();

		String lexeme = this.lookahead.getAttribute().toString();
		this.match(Token.ID);

		if (this.lookahead.getToken() == Token.OPEN_PAR) { 
			this.match(Token.OPEN_PAR);
			this.mLt(variables, argumentList);
			this.match(Token.CLOSE_PAR);
		}

		return new Function(
				FunctionSymbol.getInstance(lexeme, argumentList.size()),
				argumentList);
	}

	/**
	 * Li -> '[' ']'  |  '[' Lt ']'  |  '[' Lt '|' T ']'
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the Prolog list that has been read
	 * @throws IOException
	 */
	private PrologList mLi(Map<String,Variable> variables) throws IOException {
		PrologList l = null;

		this.match(Token.OPEN_SQ_PAR);
		if (this.lookahead.getToken() == Token.CLOSE_SQ_PAR) {
			// Li -> '[' ']'
			this.match(Token.CLOSE_SQ_PAR);
			l = PrologList.emptyPrologList();
		}
		else {
			LinkedList<Term> elements = new LinkedList<Term>();

			this.mLt(variables, elements);
			Token token = this.lookahead.getToken();
			if (token == Token.CLOSE_SQ_PAR) {
				// Li -> '[' Lt ']'
				this.match(token);
				l = new PrologList(elements);
			}
			else if (token == Token.PIPE) {
				// Li -> '[' Lt '|' T ']'
				this.match(token);
				l = new PrologList(elements, this.mT(variables));
				this.match(Token.CLOSE_SQ_PAR);
			}
			else throw new RuntimeException("syntax error: non-ended list at line " + this.scanner.getLineno());  
		}
		return l;
	}

	/**
	 * Lt -> T  |  T ',' Lt
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @param l list of terms to fill
	 * @throws IOException
	 */
	private void mLt(Map<String,Variable> variables, LinkedList<Term> l) throws IOException {
		l.addLast(this.mT(variables));
		if (this.lookahead.getToken() == Token.COMMA) {
			this.match(Token.COMMA);
			this.mLt(variables, l);
		}
	}
	
	/**
	 * Spatsub -> Sub Sub |  Sub Spatsub
	 * 
	 * A simple pattern substitution consists of at least
	 * two substitutions (a closing substitution and at
	 * least one pumping substitution).
	 * 
	 * @param variables the set of variables that have
	 * been encountered so far
	 * @return the simple pattern substitution that has
	 * been read
	 * @throws IOException
	 * @throws IllegalArgumentException if a pumping
	 * substitution that is read does not have the
	 * correct form
	 */
	private SimplePatternSubstitution mSpatsub(
			Map<String, Variable> variables) throws IOException {
		
		List<Substitution> substitutions = new LinkedList<>();

		// A pattern substitution consists of at
		// least two substitutions.
		substitutions.add(this.mSub(variables));
		substitutions.add(this.mSub(variables));
		
		while (this.lookahead.getToken() == Token.OPEN_BRACE)
			substitutions.add(this.mSub(variables));

		// Returns null if substitutions
		// does not have the correct form.
		return SimplePatternSubstitution.getInstance(substitutions);
	}

	/**
	 * Sub -> '{' '}' | '{' Lm '}'
	 * 
	 * @param variables the set of variables that
	 * have been encountered so far
	 * @return the substitution that has been read
	 * @throws IOException
	 */
	private Substitution mSub(Map<String, Variable> variables) throws IOException {
		this.match(Token.OPEN_BRACE);
		Substitution sigma = new Substitution();

		if (this.lookahead.getToken() == Token.VAR)
			this.mLm(sigma, variables);

		this.match(Token.CLOSE_BRACE);
		return sigma;
	}

	/**
	 * Lm -> Map  |  Map ',' Lm
	 * 
	 * @param sigma the substitution to fill
	 * @param variables the set of variables that have been encountered so far
	 * @throws IOException
	 */
	private void mLm(Substitution sigma, Map<String, Variable> variables) throws IOException {
		this.mMap(sigma, variables);
		if (this.lookahead.getToken() == Token.COMMA) {
			this.match(Token.COMMA);
			this.mLm(sigma, variables);
		}
	}

	/**
	 * Map -> var '->' T
	 * 
	 * @param sigma the substitution to fill
	 * @param variables the set of variables that have been encountered so far
	 * @throws IOException
	 */
	private void mMap(Substitution sigma, Map<String, Variable> variables) throws IOException {
		String lexeme = this.lookahead.getAttribute().toString();

		this.match(Token.VAR);
		this.match(Token.ARROW);

		Variable x = variables.get(lexeme);
		if (x == null) {
			x = new Variable();
			variables.put(lexeme, x);
		}

		sigma.add(x,  this.mT(variables));
	}

	/**
	 * Rlp  -> F '.'  |  F ':-' Lf '.'
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the LP rule that has been read
	 * @throws IOException
	 */
	private RuleLp mRlp(Map<String,Variable> variables) throws IOException {
		Function head = this.mF(variables);
		LinkedList<Function> body = new LinkedList<Function>();
		if (this.lookahead.getToken() == Token.LPARROW) {
			this.match(Token.LPARROW);
			this.mLf(variables, body);
		}
		this.match(Token.DOT);

		Function[] b = new Function[body.size()];
		int index = 0;
		for (Function a: body)
			b[index++] = a;

		return new RuleLp(head, b);
	}

	/**
	 * Lf -> F  |  F ',' Lf
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @param l the list of functions to fill
	 * @throws IOException
	 */
	private void mLf(Map<String,Variable> variables, LinkedList<Function> l)  throws IOException {
		l.addLast(this.mF(variables));
		if (this.lookahead.getToken() == Token.COMMA) {
			this.match(Token.COMMA);
			this.mLf(variables, l);
		}
	}
	
	/**
	 * Rtrs -> F '->' F | var
	 * 
	 * @param variables the set of variables that have been encountered so far
	 * @return the TRS rule that has been read
	 * @throws IOException
	 */
	private RuleTrs mRtrs(Map<String,Variable> variables) throws IOException {
		Function left  = this.mF(variables);
		Term     right = null;
		
		this.match(Token.ARROW);
		
		if (this.lookahead.getToken() == Token.VAR) {
			String lexeme = this.lookahead.getAttribute().toString();
			
			this.match(Token.VAR);
			
			right = variables.get(lexeme);
			if (right == null) {
				right = new Variable();
				variables.put(lexeme, (Variable) right);
			}
		}
		else
			right = this.mF(variables);
		
		return new RuleTrs(left, right);
	}
}
