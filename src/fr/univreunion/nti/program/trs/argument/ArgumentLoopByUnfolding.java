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
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentLoopByUnfolding implements Argument {

	/**
	 * The unfolded rule that provides this argument.
	 */
	private final UnfoldedRuleTrs U;

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
	 * @param U the unfolded rule that provides this argument
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
	public ArgumentLoopByUnfolding(UnfoldedRuleTrs U, boolean shallow,
			Position p, Term looping,
			Substitution theta1, Substitution theta2) {

		this.U = U;
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
		return this.U;
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
		StringBuffer s = new StringBuffer();
		
		for (int i = 0; i < indentation; i++) s.append(" ");
		s.append("Here is the successful unfolding. Let IR be the TRS under analysis.\n");
		
		int n = this.U.getIteration();
		
		ParentTrs parent;
		if ((parent = this.U.getParent()) != null) {
			s.append(parent.toString(indentation) + "\n");
			for (int i = 0; i < indentation; i++) s.append(" ");
			s.append("==> L" + n + " = " + this.U);
		}
		else {
			for (int i = 0; i < indentation; i++) s.append(" ");
			s.append("L" + n + " = " + this.U);
		}
		s.append(" is in U_IR^" + n + ".");
		
		return s.toString();
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
		// return "single loop";
		return "loop";
	}
	
	/**
	 * Returns a string representation of this argument.
	 * 
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		Map<Variable,String> variables = new HashMap<Variable,String>();
		
		// We remove the tuple symbols (see the dependency pair framework)
		// from the rule that provides this argument.
		Term left = this.U.getLeft(); //.toFunction();
		Term right = this.U.getRight(); //.toFunction();
		String certificate = this.looping.toFunction().toString(variables, false);

		return
				// "* Certificate: " + certificate + " from a " + this.getWitnessKind() +
				// "\n* Description:\n" + 
				"* Certificate: " + certificate + " is non-terminating\n" +
				"* Description:\n" + 
				"The following rule R was generated while unfolding\n" +
				"the dependency pairs of the analyzed TRS:\n" +
				"[iteration = " + this.U.getIteration() + "] " +
				left.toString(variables, this.shallow) +
				" -> " +
				right.toString(variables, this.shallow) +
				"\nLet l be the left-hand side and r be the right-hand side of R." +
				"\nLet p = " + p +
				", theta1 = " + this.theta1.toString(variables) +
				" and theta2 = " + this.theta2.toString(variables) + "." +
				"\nWe have r|p = " +
				right.get(p, this.shallow).toString(variables, this.shallow) +
				"\nand theta2(theta1(l)) = theta1(r|p), " +
				"i.e., l semi-unifies with r|p." +
				// "\nHence, theta1(R) forms a single loop (Def. 3.5 of " +
				// "\n[Payet, Non-termination in TRS and LP])." + 
				"\nSo, the term theta1(l) = " + certificate +
				"\nstarts an infinite rewrite sequence w.r.t. the analyzed TRS.";
	}
}
