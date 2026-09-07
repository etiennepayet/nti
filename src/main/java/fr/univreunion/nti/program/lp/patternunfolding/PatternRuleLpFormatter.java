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

package fr.univreunion.nti.program.lp.patternunfolding;

import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Formats logic programming pattern rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleLpFormatter {

	private static final String ALPHA = "\uD835\uDEFC";
	private static final String THETA = "\uD835\uDEF3";

	/**
	 * Returns a string representation of the given pattern rule
	 * relatively to the provided set of variable symbols.
	 *
	 * @param patternRule a pattern rule
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of <code>patternRule</code>
	 */
	static String format(
			PatternRuleLp patternRule,
			Map<Variable, String> variables) {

		Function nonterminating = patternRule.getNonTerminatingTerm();

		return
				prefix(nonterminating) +
				patternRule.getLeft().toString(variables) +
				" :- " +
				formatRight(patternRule.getRight(), variables) +
				specialRuleDescription(patternRule, nonterminating);
	}

	/**
	 * Returns the prefix used for a special pattern rule.
	 *
	 * @param nonterminating a nonterminating term generated from
	 * a pattern rule, or <code>null</code> if the rule is not special
	 * @return the prefix used in the representation of a special
	 * pattern rule, or the empty string otherwise
	 */
	private static String prefix(Function nonterminating) {
		return nonterminating == null ? "" : "Pattern rule R = ";
	}

	/**
	 * Returns a string representation of the right-hand side of a
	 * pattern rule.
	 *
	 * @param right the right-hand side of a pattern rule, or
	 * <code>null</code> for an empty right-hand side
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of <code>right</code>,
	 * or <code>e*</code> if <code>right</code> is <code>null</code>
	 */
	private static String formatRight(
			SimplePatternTerm right,
			Map<Variable, String> variables) {

		return right == null ? "e*" : right.toString(variables);
	}

	/**
	 * Returns the description appended to the representation of
	 * a special pattern rule.
	 *
	 * @param patternRule a pattern rule
	 * @param nonterminating a nonterminating term generated from
	 * <code>patternRule</code>, or <code>null</code> if
	 * <code>patternRule</code> is not special
	 * @return the special-rule description, or the empty string if
	 * <code>patternRule</code> is not special
	 */
	private static String specialRuleDescription(
			PatternRuleLp patternRule,
			Function nonterminating) {

		if (nonterminating == null)
			return "";

		return
				" (R is special with " +
				ALPHA + "(R) = " + patternRule.getAlpha() +
				" and p(" + ALPHA + "(R))" + THETA + " = " + nonterminating +
				" where " + THETA +
				" maps all variables to the constant 0, see Def. 14 + Thm. 5 of [Payet, ICLP'25])";
	}

	/**
	 * Disables construction.
	 */
	private PatternRuleLpFormatter() {
	}
}
