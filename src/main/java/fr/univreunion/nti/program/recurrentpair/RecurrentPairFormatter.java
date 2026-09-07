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

package fr.univreunion.nti.program.recurrentpair;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Formats recurrent-pair certificates.
 */
public final class RecurrentPairFormatter {

	/**
	 * The fixed recurrent-pair certificate equations.
	 */
	private static final String CERTIFICATE_EQUATIONS = """

			We have:
			u1 = c1[x,c2^m1[y]], v1 = c1[c2^n1[x],c2^n2[y]]
			u2 = c1[x,c2^m2[s]], v2 = c1[c2^n3[t],c2^n4[x]]
			for:""";

	/**
	 * This class cannot be instantiated.
	 */
	private RecurrentPairFormatter() {}

	/**
	 * Returns a String representation of the provided recurrent pair.
	 *
	 * @param recurrentPair the recurrent pair to format
	 * @return a String representation of the provided recurrent pair
	 */
	public static String formatDetailedCertificate(RecurrentPair recurrentPair) {
		FormattedRecurrentPairCertificate certificate =
				formatCertificate(recurrentPair);

		return certificate.certificateBody() +
				"\nNonterminating term = " +
				certificate.nonTerminatingTerm();
	}

	/**
	 * Returns the formatted reusable certificate parts of the provided
	 * recurrent pair.
	 *
	 * @param recurrentPair the recurrent pair to format
	 * @return the formatted reusable certificate parts
	 */
	public static FormattedRecurrentPairCertificate formatCertificate(
			RecurrentPair recurrentPair) {

		Map<Variable,String> variables = new HashMap<>();
		RecurrentPairFormatContext context = new RecurrentPairFormatContext(
				recurrentPair.data(),
				variables);
		String nonTerminatingTerm = context.formatNonTerminatingTerm();

		return new FormattedRecurrentPairCertificate(
				formatCertificateBody(context),
				nonTerminatingTerm);
	}

	/**
	 * Returns the body of a recurrent-pair certificate.
	 *
	 * @param context the recurrent-pair formatting context
	 * @return the recurrent-pair certificate body
	 */
	private static String formatCertificateBody(
			RecurrentPairFormatContext context) {

		return formatFiniteChains(context) +
				CERTIFICATE_EQUATIONS +
				formatContextsAndTerms(context) +
				formatParameters(context.data());
	}

	/**
	 * Returns a String representation of the recurrent pair's finite chains.
	 *
	 * @param context the recurrent-pair formatting context
	 * @return the formatted finite chains
	 */
	private static String formatFiniteChains(
			RecurrentPairFormatContext context) {

		RecurrentPairData data = context.data();

		return
				"u1 -> v1 = " + context.format(data.u1()) +
				" -> " + context.format(data.v1()) +
				"\nu2 -> v2 = " + context.format(data.u2()) +
				" -> " + context.format(data.v2());
	}

	/**
	 * Returns a String representation of the recurrent pair's contexts
	 * and terms.
	 *
	 * @param context the recurrent-pair formatting context
	 * @return the formatted contexts and terms
	 */
	private static String formatContextsAndTerms(
			RecurrentPairFormatContext context) {

		RecurrentPairData data = context.data();

		return
				"\nc1 = " + context.format(data.c1()) +
				"\nc2 = " + context.format(data.c2()) +
				formatSAndT(context);
	}

	/**
	 * Returns a String representation of the recurrent pair's parameters.
	 *
	 * @param data the recurrent-pair certificate components to format
	 * @return the formatted parameters
	 */
	private static String formatParameters(RecurrentPairData data) {
		return "\n(m1,m2) = (" +
				data.m1() + "," + data.m2() + ")" +
				" and (n1,n2,n3,n4) = (" +
				data.n1() + "," +
				data.n2() + "," +
				data.n3() + "," +
				data.n4() + ")";
	}

	/**
	 * Returns the formatted values of s and t.
	 *
	 * @param context the recurrent-pair formatting context
	 * @return the formatted values of s and t
	 */
	private static String formatSAndT(
			RecurrentPairFormatContext context) {

		RecurrentPairData data = context.data();

		return (data.s() == data.t() ?
				"\ns = t = " + context.format(data.s()) :
				"\ns = " + context.format(data.s()) +
				"\nt = " + context.format(data.t()));
	}

	/**
	 * The mutable variable-name table used while rendering one certificate.
	 *
	 * @param data the recurrent-pair certificate components to format
	 * @param variables the variables already printed in the certificate
	 */
	private record RecurrentPairFormatContext(
			RecurrentPairData data,
			Map<Variable,String> variables) {

		/**
		 * Returns the provided term rendered with this context's variable names.
		 *
		 * @param term the term to render
		 * @return the rendered term
		 */
		String format(Term term) {
			return term.toString(this.variables, false);
		}

		/**
		 * Returns this recurrent pair's generated nonterminating term.
		 *
		 * @return the formatted generated nonterminating term
		 */
		String formatNonTerminatingTerm() {
			return format(this.data.nonTerminatingTerm());
		}
	}
}
