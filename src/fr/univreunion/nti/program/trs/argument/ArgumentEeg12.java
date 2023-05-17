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
import fr.univreunion.nti.program.trs.nonloop.PatternRule;
import fr.univreunion.nti.program.trs.nonloop.PatternTerm;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A nontermination argument produced when searching for a
 * non-loop witness using the technique presented in the
 * paper [Emmes, Enger, Giesl, IJCAR'12]. It embeds
 * <code>m</code>, <code>b</code>... of Theorem 8 of
 * [Emmes, Enger, Giesl, IJCAR'12].
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentEeg12 implements Argument {

	/**
	 * The pattern rule that provides this argument.
	 */
	private PatternRule R;

	/**
	 * The integer <code>m</code> used in Theorem 8.
	 */
	private final int m;

	/**
	 * The integer <code>b</code> used in Theorem 8.
	 */
	private final int b;
	
	/**
	 * The position <code>pi</code> used in Theorem 8.
	 */
	private final Position pi;

	/**
	 * The substitution <code>sigma'</code> used in Theorem 8.
	 */
	private final Substitution sigmaPrime;

	/**
	 * The substitution <code>mu'</code> used in Theorem 8.
	 */
	private final Substitution muPrime;

	/**
	 * Builds a nontermination argument produced when
	 * searching for a non-loop witness.
	 * 
	 * @param R the pattern rule that provides this argument
	 * @param m the integer <code>m</code> used in Theorem 8
	 * @param b the integer <code>b</code> used in Theorem 8
	 * @param pi the position <code>pi</code> used in Theorem 8
	 * @param sigmaPrime the substitution <code>sigma'</code>
	 * used in Theorem 8
	 * @param muPrime the substitution <code>mu'</code> used
	 * in Theorem 8
	 */
	public ArgumentEeg12(PatternRule R, int m, int b, Position pi,
			Substitution sigmaPrime, Substitution muPrime) {

		this.R = R;
		this.m = m;
		this.b = b;
		this.pi = pi;
		this.sigmaPrime = sigmaPrime;
		this.muPrime = muPrime;
	}

	/**
	 * Returns the pattern rule that provides this argument
	 * 
	 * @return the pattern rule that provides this argument
	 */
	public PatternRule getPatternRule() {
		return this.R;
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
		
		s.append(this.R.getParent().toString(indentation) + "\n");
		
		int n = this.R.getIteration();
		
		for (int i = 0; i < indentation; i++) s.append(" ");
		s.append("==> P" + n + " = ");
		s.append(this.R);		
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
		return "[Emmes, Enger, Giesl, IJCAR'12]";
	}
	
	/**
	 * Returns a string representation of this argument.
	 * 
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		// The string associated to each variable to be printed.
		Map<Variable,String> variables = new HashMap<Variable,String>();

		// The left-hand side of R.
		PatternTerm left = this.R.getLeftPatternTerm();
		Term l = left.getBaseTerm().toFunction();
		Substitution mu = left.getClosing(); 
		String leftString =
				l.toString(variables, false) +
				left.getPumping().toString(variables) + "^n" +
				mu.toString(variables);

		// The right-hand side of R.
		PatternTerm right = this.R.getRightPatternTerm();
		String rightString =
				right.getBaseTerm().toFunction().toString(variables, false) +
				right.getPumping().toString(variables) + "^n" +
				right.getClosing().toString(variables);

		// The term that starts an infinite derivation.
		String certificate = l.apply(mu).toString(variables, false);
		
		
		return
				// "* Certificate: " + certificate + " from " + this.getWitnessKind() +
				// "\n* Description:\n" +
				"* Certificate: " + certificate + " is non-terminating\n" +
				"* Description:\n" + 
				"The following pattern rule was generated by the strategy" +
				"\npresented in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12]:\n" +
				"[iteration = " + this.R.getIteration() + "] " +
				leftString + " -> " + rightString +
				"\nWe apply Theorem 8 of [Emmes, Enger, Giesl, IJCAR'12]\n" +
				"on this rule with m = " +
				this.m + ", b = " + this.b + ", pi = " + this.pi +
				",\nsigma' = " + this.sigmaPrime.toString(variables) +
				" and mu' = " + this.muPrime.toString(variables) + 
				".\nHence the term " + certificate + ", obtained from" +
				"\ninstantiating n with 0 in the left-hand side of" +
				"\nthe rule, starts an infinite rewrite sequence w.r.t." +
				"\nthe analyzed TRS.";
	}
}
