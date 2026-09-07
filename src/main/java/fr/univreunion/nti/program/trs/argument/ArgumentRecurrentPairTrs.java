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

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.recurrentpair.FormattedRecurrentPairCertificate;
import fr.univreunion.nti.program.recurrentpair.RecurrentPair;
import fr.univreunion.nti.program.recurrentpair.RecurrentPairFormatter;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.comp.UnfoldedRuleTrsComp;

/**
 * A nontermination proof argument in term rewriting.
 * It is produced by a recurrent pair.
 *
 * <p>Recurrent pairs are defined by E. Payet in
 * <a href="https://doi.org/10.1007/s10817-023-09693-z"><i>Non-Termination
 * in Term Rewriting and Logic Programming</i></a>, Journal of Automated
 * Reasoning 68, article 4, 2024, and generalized in
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10"><i>Recurrent Pairs
 * Revisited</i></a>, LOPSTR 2025, LNCS 16117, pp. 154--164, 2026.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentRecurrentPairTrs implements Argument {

	/**
	 * The recurrent pair that provides this argument.
	 */
	private final RecurrentPair recPair;

	/**
	 * The unfolded rule that provides this argument.
	 */
	private final UnfoldedRuleTrsComp unfolded;

	/**
	 * Builds a nontermination argument.
	 *
	 * @param recPair the recurrent pair that
	 * provides this argument
	 * @param unfolded the unfolded rule that
	 * provides this argument
	 */
	public ArgumentRecurrentPairTrs(RecurrentPair recPair,
			UnfoldedRuleTrsComp unfolded) {

		this.recPair = recPair;
		this.unfolded = unfolded;
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
		StringBuilder details = new StringBuilder();

		appendIndentation(details, indentation);
		details.append("Here is the successful unfolding. Let IR be the TRS under analysis.\n");

		int n = this.unfolded.getIteration();

		ParentTrs parent;
		if ((parent = this.unfolded.getParent()) != null) {
			details.append(parent.toString(indentation)).append("\n");
			appendIndentation(details, indentation);
			details.append("==> L").append(n).append(" = ").append(this.unfolded);
		}
		else {
			appendIndentation(details, indentation);
			details.append("L").append(n).append(" = ").append(this.unfolded);
		}
		details.append(" is in U_IR^").append(n).append(".");

		return details.toString();
	}

	/**
	 * Appends the requested indentation to the provided builder.
	 *
	 * @param builder the builder receiving indentation
	 * @param indentation the number of single spaces to append
	 */
	private static void appendIndentation(
			StringBuilder builder, int indentation) {

		builder.repeat(" ", Math.max(0, indentation));
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
		return "recurrent pair";
	}

	/**
	 * Returns a string representation of this argument.
	 *
	 * @return a string representation of this argument
	 */
	@Override
	public String toString() {
		FormattedRecurrentPairCertificate certificate =
				RecurrentPairFormatter.formatCertificate(this.recPair);

		return
				"* Technique: [Payet, LOPSTR'18 + JAR'24 + LOPSTR'25]\n" +
				"* Certificate: " + certificate.nonTerminatingTerm() +
				" is non-terminating\n" +
				"* Description:\n" +
				"The following recurrent pair (Def. 3 of [Payet, LOPSTR'25])\n" +
				"was generated while unfolding the dependency pairs of\n" +
				"the analyzed TRS [iteration = " +
				this.unfolded.getIteration() + "]:\n" +
				certificate.certificateBody() +
				"\nSo, by Corollary 1 of [Payet, LOPSTR'25], the term\n" +
				"c1[s,c2^m2[s]] = " + certificate.nonTerminatingTerm() +
				"\nstarts an infinite rewrite sequence w.r.t.\nthe analyzed TRS.";
	}
}
