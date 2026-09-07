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

package fr.univreunion.nti.program.trs.argument;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.pattern.PatternRule;
import fr.univreunion.nti.term.Variable;

/**
 * A nontermination proof argument in term rewriting. It is produced from a
 * pattern rule satisfying the criterion of E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025, adapted to term rewriting as in
 * E. Payet,
 * <a href="https://www.imn.htwk-leipzig.de/~waldmann/WST2025/proceedings/WST2025_paper_2.pdf"><i>Non-Termination
 * of Term Rewrite Systems Using Pattern Unfolding</i></a>, Proceedings of the
 * 20th International Workshop on Termination (WST 2025), 2025.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentIclp25 implements Argument {

	/**
	 * The pattern rule that provides this argument.
	 */
	private final PatternRule patternRule;

	/**
	 * Builds a nontermination argument produced when
	 * using the pattern-unfolding technique cited in this class documentation.
	 * 
	 * @param patternRule the pattern rule that provides this argument
	 */
	public ArgumentIclp25(PatternRule patternRule) {
		this.patternRule = patternRule;
	}

	/**
	 * Returns a detailed String representation of
	 * this argument (usually used while printing
	 * proofs in verbose mode).
	 * 
	 * @param indentation the number of single spaces
	 * to print at the beginning of each line of the
	 * detailed representation
	 * @return a detailed String representation of
	 * this argument
	 */
	@Override
	public String getDetails(int indentation) {
		return "";
	}

	/**
	 * Returns a String representation of the kind
	 * of witness provided by this argument.
	 * 
	 * @return a String representation of the kind
	 * of witness provided by this argument
	 */
	@Override
	public String getWitnessKind() {
		return "[Payet, ICLP'25]";
	}

	/**
	 * Returns a string representation of this argument.
	 * 
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		Map<Variable,String> variables = new HashMap<>();

		// The non-terminating term, as a String:
		String certificate = this.patternRule.getNonTerminatingTerm().toString(variables, false);

		// The alpha Greek letter (Unicode U+1D6FC), where
		// U+1D6FC = \uD835\uDEFC in UTF-16 (surrogate pair)
		String alpha = "\uD835\uDEFC";
		// The theta Greek letter (Unicode U+1D6F3), where
		// U+1D6F3 = \uD835\uDEF3 in UTF-16 (surrogate pair):
		String theta = "\uD835\uDEF3";
		// The alpha(R) string:
		String alphaR = alpha + "(R)";

		return
				"* Technique: [Payet, ICLP'25]\n" +
				"* Certificate: " + certificate + " is non-terminating\n" +
				"* Description:\n" + 
				"We adapt the technique of [Payet, ICLP'25] to\n" +
				"term rewriting (we transform the unfolding technique\n" +
				"of [Payet, TCS'08] so that it produces pattern rules).\n" +
				"Let IR be the analyzed TRS.\n" +
				"The following rule R is generated while computing\n" +
				"the pattern unfolding of IR using a set B of pattern\n" +
				"rules which are correct w.r.t. IR:\n" +
				"[iteration = " + this.patternRule.getIteration() + "] " +
				this.patternRule.getLeft().toString(variables) +
				" -> " +
				this.patternRule.getRight().toString(variables) +
				"\nNote that R is special (Def. 14 of [Payet, ICLP'25])\n" +
				"with " + alphaR + " = " +
				this.patternRule.getAlpha() +
				". Let p be the left-hand side of R.\n" +
				"By Thm. 5 of [Payet, ICLP'25], the term\n" +
				"p(" + alphaR + ")" + theta + " = " +
				certificate +
				"\nstarts an infinite rewrite sequence w.r.t. IR,\n" +
				"where the substitution " + theta +
				" maps all variables to\n" +
				"the constant 0.";
	}
}
