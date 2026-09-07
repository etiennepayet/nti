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
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A nontermination argument produced when searching for
 * a loop by unfolding. It embeds a looping term together
 * with the substitutions theta1 and theta2 of the
 * left-unification test. It also embeds the unfolded
 * rule that provides this argument, together with the
 * position in the right-hand side of this rule where
 * the left-unification test succeeds.
 *
 * <p>The unfolding technique is described by E. Payet in
 * <a href="https://doi.org/10.1016/j.tcs.2008.05.013"><i>Loop Detection in
 * Term Rewriting Using the Eliminating Unfoldings</i></a>, Theoretical
 * Computer Science 403(2--3), pp. 307--327, 2008, and
 * <a href="https://doi.org/10.1007/978-3-030-13838-7_2"><i>Guided
 * Unfoldings for Finding Loops in Standard Term Rewriting</i></a>, LOPSTR
 * 2018, LNCS 11408, pp. 22--37, 2019.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentLoopByUnfolding implements Argument {

	/**
	 * The unfolded rule that provides this argument.
	 */
	private final UnfoldedRuleTrs unfoldedRule;

	/**
	 * A boolean indicating whether the rewrite rule
	 * of this argument has to be displayed in a shallow
	 * way (i.e., stopping at subterms, not considering
	 * the class representative nor the schema of the
	 * subterms).
	 */
	private final boolean shallow;

	/**
	 * The position in the right-hand side of the
	 * rewrite rule where the left-unification
	 * test succeeds.
	 */
	private final Position p;

	/**
	 * The looping term of this argument.
	 */
	private final Term looping;

	/**
	 * The substitution theta1 of this argument.
	 */
	private final Substitution theta1;

	/**
	 * The substitution theta2 of this argument.
	 */
	private final Substitution theta2;

	/**
	 * Builds a nontermination argument produced when
	 * searching for a loop by unfolding.
	 *
	 * @param unfoldedRule the unfolded rule that provides this argument
	 * @param shallow a boolean indicating whether the
	 * rewrite rule has to be displayed in a shallow way
	 * (i.e., stopping at subterms, not considering the class
	 * representative nor the schema of the subterms)
	 * @param p the position in the right-hand side of the
	 * rewrite rule where the left-unification test succeeds
	 * @param looping the looping term of this argument
	 * @param theta1 the substitution theta1 of this argument
	 * @param theta2 the substitution theta2 of this argument
	 */
	public ArgumentLoopByUnfolding(UnfoldedRuleTrs unfoldedRule, boolean shallow,
			Position p, Term looping,
			Substitution theta1, Substitution theta2) {

		this.unfoldedRule = unfoldedRule;
		this.shallow = shallow;

		this.p = p;
		this.looping = looping;
		this.theta1 = theta1;
		this.theta2 = theta2;
	}

	/**
	 * Returns the unfolded rule that provides this argument
	 *
	 * @return the unfolded rule that provides this argument
	 */
	public UnfoldedRuleTrs getUnfoldedRule() {
		return this.unfoldedRule;
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
		String spaces = " ".repeat(Math.max(0, indentation));
		StringBuilder details = new StringBuilder(spaces);
		details.append("Here is the successful unfolding. Let IR be the TRS under analysis.\n");

		int n = this.unfoldedRule.getIteration();
		ParentTrs parent = this.unfoldedRule.getParent();
		if (parent != null) {
			details.append(parent.toString(indentation)).append("\n");
			details.append(spaces).append("==> L").append(n)
					.append(" = ").append(this.unfoldedRule);
		}
		else
			details.append(spaces).append("L").append(n)
					.append(" = ").append(this.unfoldedRule);
		details.append(" is in U_IR^").append(n).append(".");

		return details.toString();
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
		return "loop";
	}

	/**
	 * Returns a string representation of this argument.
	 *
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		Map<Variable,String> variables = new HashMap<>();

		// We remove the tuple symbols (see the dependency pair framework)
		// from the rule that provides this argument.
		Term left = this.unfoldedRule.getLeft();
		Term right = this.unfoldedRule.getRight();
		String certificate = this.looping.toFunction().toString(variables, false);

		// The theta Greek letter (Unicode U+1D6F3), where
		// U+1D6F3 = \uD835\uDEF3 in UTF-16 (surrogate pair):
		String theta = "\uD835\uDEF3";

		return
				"* Technique: [Payet, LOPSTR'18]\n" +
				"* Certificate: " + certificate + " is non-terminating\n" +
				"* Description:\n" +
				"The following rule R was generated while unfolding\n" +
				"the dependency pairs of the analyzed TRS:\n" +
				"[iteration = " + this.unfoldedRule.getIteration() + "] " +
				left.toString(variables, this.shallow) +
				" -> " +
				right.toString(variables, this.shallow) +
				"\nLet l be the left-hand side and r be the right-hand side of R." +
				"\nConsider the position p = " + p + " in r and the substitutions\n" +
				theta + "1 = " + this.theta1.toString(variables) + " and " +
				theta + "2 = " + this.theta2.toString(variables) + "." +
				"\nWe have r|p = " +
				right.get(p, this.shallow).toString(variables, this.shallow) +
				"\nand " + theta + "2(" + theta + "1(l)) = " + theta + "1(r|p), " +
				"i.e., l semi-unifies with r|p." +
				"\nSo, the term " + theta + "1(l) = " + certificate +
				"\nstarts an infinite rewrite sequence w.r.t. the analyzed TRS.";
	}
}
