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

package fr.univreunion.nti.parse.xml;

import java.io.BufferedReader;
import java.io.IOException;

import fr.univreunion.nti.parse.Pair;
import fr.univreunion.nti.parse.Scanner;
import fr.univreunion.nti.parse.Token;

/**
 * A lexical analyzer for reading files storing
 * Term or String Rewrite Systems in the XML format.
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ScannerXml extends Scanner {

	/**
	 * Builds a new lexical analyzer for TRS/SRS
	 * in the XML format .
	 * 
	 * @param input the input to read
	 */
	public ScannerXml(BufferedReader input) {
		super(input);
	}

	/**
	 * Used to switch from the current automaton to the
	 * next one.
	 * 
	 * @return the start state of the next automaton
	 * @throws RuntimeException if a lexical error or a scanner error occurs
	 */
	private int fail() {
		if (this.start == 0) this.start = 1;
		else if (this.start == 1) this.start = 4;
		else if (this.start == 4) 
			throw new RuntimeException("lexical error at line " +  this.lineno);
		else
			throw new RuntimeException("scanner error at line " +  this.lineno);

		return this.start;
	}

	/**
	 * Checks that the given tag starts with the given prefix
	 * followed by a space or by the closing tag character '>'.
	 *  
	 * @param prefix the prefix
	 * @param tag the tag
	 * @return <code>true</code> if <code>tag</code> starts with
	 *   <code>prefix</code> followed by a space or by '>', and 
	 *   <code>false</code> otherwise
	 */
	private static boolean tagStartsWith(String prefix, String tag) {
		int l = prefix.length();

		if (!tag.startsWith(prefix) || l >= tag.length()) return false;

		// From here, we necessarily have l < tag.length().
		char tag_l = tag.charAt(l);
		return  (tag_l == '>' || isSpace(tag_l));
	}

	/**
	 * Reads the next token from the input.
	 * If a problem occurs while reading the input
	 * then an IOException is thrown.
	 * 
	 * @return the token that has been read
	 * @throws IOException
	 */
	public Pair nextToken() throws IOException {
		this.start = 0;

		int c = -1;
		int state = 0;
		StringBuffer lexbuf = new StringBuffer();

		while (true) {
			// Delimiters:
			if (state == 0) {
				c = this.input.read();
				if (c == -1) return new Pair(Token.DONE);
				else if (isEndOfLine(c)) this.lineno++;
				else if (!isSpace(c)) state = this.fail();
			}
			// Tags:
			else if (state == 1) {
				if (c == '<') {
					lexbuf.append((char)c);
					state = 2;
				}
				else state = this.fail();
			}
			else if (state == 2) {
				c = this.input.read();
				if (isSpace(c)) {
					lexbuf.append(' ');
					if (isEndOfLine(c)) this.lineno++;
				}
				else lexbuf.append((char)c);
				if (c == '>') state = 3; 
			}
			else if (state == 3) {
				String lexeme = lexbuf.toString();
				// Comments
				if (lexeme.startsWith("<!--")) {
					if (lexeme.endsWith("-->")) {
						lexbuf.delete(0, lexbuf.length());
						this.start = state = 0;
					}
					else
						state = 2;
				}
				// TAG <?xml
				else if ("<?xml?>".equals(lexeme))
					return new Pair(Token.XML_TAG);
				else if (tagStartsWith("<?xml", lexeme))
					if (lexeme.endsWith("?>"))
						return new Pair(Token.XML_TAG);
					else
						throw new RuntimeException("tag '<?xml' not ended by '?>' at line " + this.lineno);
				// TAG <?xml-stylesheet
				else if (tagStartsWith("<?xml-stylesheet", lexeme))
					if (lexeme.endsWith("?>"))
						return new Pair(Token.XML_STYLESHEET_TAG);
					else
						throw new RuntimeException("tag '<?xml-stylesheet' not ended by '?>' at line " + this.lineno);
				// TAG <problem
				else if (tagStartsWith("<problem", lexeme))
					return new Pair(Token.OPEN_PROBLEM_TAG);
				else if ("</problem>".equals(lexeme))
					return new Pair(Token.CLOSE_PROBLEM_TAG);
				// TAG <trs
				else if (tagStartsWith("<trs", lexeme))
					return new Pair(Token.OPEN_TRS_TAG);
				else if ("</trs>".equals(lexeme))
					return new Pair(Token.CLOSE_TRS_TAG);
				// TAG <rules
				else if (tagStartsWith("<rules", lexeme))
					return new Pair(Token.OPEN_RULES_TAG);
				else if ("</rules>".equals(lexeme))
					return new Pair(Token.CLOSE_RULES_TAG);
				// TAG <rule
				else if (tagStartsWith("<rule", lexeme))
					return new Pair(Token.OPEN_RULE_TAG);
				else if ("</rule>".equals(lexeme))
					return new Pair(Token.CLOSE_RULE_TAG);
				// TAG <lhs
				else if (tagStartsWith("<lhs", lexeme))
					return new Pair(Token.OPEN_LHS_TAG);
				else if ("</lhs>".equals(lexeme))
					return new Pair(Token.CLOSE_LHS_TAG);
				// TAG <rhs
				else if (tagStartsWith("<rhs", lexeme))
					return new Pair(Token.OPEN_RHS_TAG);
				else if ("</rhs>".equals(lexeme))
					return new Pair(Token.CLOSE_RHS_TAG);
				// TAG <var
				else if (tagStartsWith("<var", lexeme))
					return new Pair(Token.OPEN_VAR_TAG);
				else if ("</var>".equals(lexeme))
					return new Pair(Token.CLOSE_VAR_TAG);
				// TAG <funapp
				else if (tagStartsWith("<funapp", lexeme))
					return new Pair(Token.OPEN_FUNAPP_TAG);
				else if ("</funapp>".equals(lexeme))
					return new Pair(Token.CLOSE_FUNAPP_TAG);
				// TAG <name
				else if (tagStartsWith("<name", lexeme))
					return new Pair(Token.OPEN_NAME_TAG);
				else if ("</name>".equals(lexeme))
					return new Pair(Token.CLOSE_NAME_TAG);
				// TAG <arg
				else if (tagStartsWith("<arg", lexeme))
					return new Pair(Token.OPEN_ARG_TAG);
				else if ("</arg>".equals(lexeme))
					return new Pair(Token.CLOSE_ARG_TAG);
				// TAG <signature
				else if (tagStartsWith("<signature", lexeme))
					return new Pair(Token.OPEN_SIGN_TAG);
				else if ("</signature>".equals(lexeme))
					return new Pair(Token.CLOSE_SIGN_TAG);
				// TAG <funcsym
				else if (tagStartsWith("<funcsym", lexeme))
					return new Pair(Token.OPEN_FUNCSYM_TAG);
				else if ("</funcsym>".equals(lexeme))
					return new Pair(Token.CLOSE_FUNCSYM_TAG);
				// TAG <arity
				else if (tagStartsWith("<arity", lexeme))
					return new Pair(Token.OPEN_ARITY_TAG);
				else if ("</arity>".equals(lexeme))
					return new Pair(Token.CLOSE_ARITY_TAG);
				// TAG <stragegy
				else if (tagStartsWith("<strategy", lexeme))
					return new Pair(Token.OPEN_STRATEGY_TAG);
				else if ("</strategy>".equals(lexeme))
					return new Pair(Token.CLOSE_STRATEGY_TAG);
				// TAG <metainformation
				else if (tagStartsWith("<metainformation", lexeme))
					return new Pair(Token.OPEN_METAINFO_TAG);
				else if ("</metainformation>".equals(lexeme))
					return new Pair(Token.CLOSE_METAINFO_TAG);
				// TAG <originalfilename
				else if (tagStartsWith("<originalfilename", lexeme))
					return new Pair(Token.OPEN_FILENAME_TAG);
				else if ("</originalfilename>".equals(lexeme))
					return new Pair(Token.CLOSE_FILENAME_TAG);
				// TAG <author
				else if (tagStartsWith("<author", lexeme))
					return new Pair(Token.OPEN_AUTHOR_TAG);
				else if ("</author>".equals(lexeme))
					return new Pair(Token.CLOSE_AUTHOR_TAG);
				// TAG <date
				else if (tagStartsWith("<date", lexeme))
					return new Pair(Token.OPEN_DATE_TAG);
				else if ("</date>".equals(lexeme))
					return new Pair(Token.CLOSE_DATE_TAG);
				// TAG <comment
				else if (tagStartsWith("<comment", lexeme))
					return new Pair(Token.OPEN_COMMENT_TAG);
				else if ("</comment>".equals(lexeme))
					return new Pair(Token.CLOSE_COMMENT_TAG);
				// TAG unknown
				else
					throw new RuntimeException("line " + this.lineno + ": unknown tag " + lexeme);
			}
			// id + keywords:
			else if (state ==  4) {
				lexbuf.append((char)c);
				state = 5;
			}
			else if (state ==  5) {
				this.input.mark(1);
				c = this.input.read();
				if (c != '<' && !isSpace(c) && c != -1)
					lexbuf.append((char)c);
				else state = 6;
			}
			else if (state == 6) {
				this.input.reset();
				return new Pair(Token.ID, lexbuf.toString());
			}
			// Unknown state:
			else
				throw new RuntimeException("scanner error: unknown state " + state +
						" at line " + this.lineno);
		}
	}
}
