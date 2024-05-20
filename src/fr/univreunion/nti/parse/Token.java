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

package fr.univreunion.nti.parse;

/**
 * The value that a token can have.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public enum Token {
	// MISC.:
	ANONYMOUS_VAR,
	ARROW,
	COMMA,
	DOT,
	DONE,
	ID,
	INT,
	INNERMOST,
	OUTERMOST,
	LEFTMOST,
	RIGHTMOST,
	OPEN_PAR,
	CLOSE_PAR,
	OPEN_SQ_PAR,
	CLOSE_SQ_PAR,
	PIPE,
	RULES,
	STRING,
	STRATEGY,
	VAR,
	MODE,
	EQ,
	PLUS,
	MINUS,
	TIMES,
	DIV,
	
	// ARI-format:
	FORMAT,
	FUN,
	RULE,
	TRS,
	
	// XML TAGS:
	XML_TAG,
	XML_STYLESHEET_TAG,
	OPEN_PROBLEM_TAG,
	CLOSE_PROBLEM_TAG,
	OPEN_TRS_TAG,
	CLOSE_TRS_TAG,
	OPEN_RULES_TAG,
	CLOSE_RULES_TAG,
	OPEN_RULE_TAG,
	CLOSE_RULE_TAG,
	OPEN_LHS_TAG,
	CLOSE_LHS_TAG,
	OPEN_RHS_TAG,
	CLOSE_RHS_TAG,
	OPEN_VAR_TAG,
	CLOSE_VAR_TAG,
	OPEN_NAME_TAG,
	CLOSE_NAME_TAG,
	OPEN_FUNAPP_TAG,
	CLOSE_FUNAPP_TAG,
	OPEN_ARG_TAG,
	CLOSE_ARG_TAG,
	OPEN_SIGN_TAG,
	CLOSE_SIGN_TAG,
	OPEN_FUNCSYM_TAG,
	CLOSE_FUNCSYM_TAG,
	OPEN_ARITY_TAG,
	CLOSE_ARITY_TAG,
	OPEN_STRATEGY_TAG,
	CLOSE_STRATEGY_TAG,
	OPEN_METAINFO_TAG,
	CLOSE_METAINFO_TAG,
	OPEN_FILENAME_TAG,
	CLOSE_FILENAME_TAG,
	OPEN_AUTHOR_TAG,
	CLOSE_AUTHOR_TAG,
	OPEN_DATE_TAG,
	CLOSE_DATE_TAG,
	OPEN_COMMENT_TAG,
	CLOSE_COMMENT_TAG
}
