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

package fr.univreunion.nti.program.lp.binaryunfolding;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.recurrentpair.RecurrentPair;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Formats recurrent pairs as logic-program nontermination witnesses.
 */
final class RecurrentPairLpFormatter {

	/**
	 * This class cannot be instantiated.
	 */
	private RecurrentPairLpFormatter() {}

	/**
	 * Returns a String representation of the provided recurrent pair
	 * as a logic-program nontermination witness.
	 *
	 * @param recurrentPair the recurrent pair to format
	 * @return a String representation of the provided recurrent pair
	 * as a logic-program nontermination witness
	 */
	static String format(RecurrentPair recurrentPair) {
		Map<Variable,String> variables = newVariableNames();
		return
				"Recurrent pair: <[" +
				formatFiniteChains(recurrentPair, variables) +
				", " + formatContextsAndTerms(recurrentPair, variables) +
				", " + formatParameters(recurrentPair) +
				", " + formatNonTerminatingQuery(recurrentPair) +
				"> (Def.3 + Cor. 1 of [Payet, LOPSTR'25])";
	}

	/**
	 * Returns a fresh map of variable names for a witness rendering.
	 *
	 * @return a fresh map of variable names
	 */
	private static Map<Variable,String> newVariableNames() {
		return new HashMap<>();
	}

	/**
	 * Returns a string representation of both finite chains.
	 *
	 * @param recurrentPair a recurrent pair
	 * @param variables the variable names used in the string representation
	 * @return a string representation of both finite chains
	 */
	private static String formatFiniteChains(
			RecurrentPair recurrentPair,
			Map<Variable,String> variables) {

		return formatFirstFiniteChain(recurrentPair, variables) +
				", " + formatSecondFiniteChain(recurrentPair, variables);
	}

	/**
	 * Returns a string representation of the first finite chain.
	 *
	 * @param recurrentPair a recurrent pair
	 * @param variables the variable names used in the string representation
	 * @return a string representation of the first finite chain
	 */
	private static String formatFirstFiniteChain(
			RecurrentPair recurrentPair,
			Map<Variable,String> variables) {

		return formatBinaryRule(
				recurrentPair.getLeft1(),
				recurrentPair.getRight1(),
				variables);
	}

	/**
	 * Returns a string representation of the second finite chain.
	 *
	 * @param recurrentPair a recurrent pair
	 * @param variables the variable names used in the string representation
	 * @return a string representation of the second finite chain
	 */
	private static String formatSecondFiniteChain(
			RecurrentPair recurrentPair,
			Map<Variable,String> variables) {

		return formatBinaryRule(
				recurrentPair.getLeft2(),
				recurrentPair.getRight2(),
				variables);
	}

	/**
	 * Returns a string representation of the contexts and terms of
	 * a recurrent pair.
	 *
	 * @param recurrentPair a recurrent pair
	 * @param variables the variable names used in the string representation
	 * @return a string representation of the contexts and terms
	 */
	private static String formatContextsAndTerms(
			RecurrentPair recurrentPair,
			Map<Variable,String> variables) {

		return formatComponent("c1", recurrentPair.getContextC1(), variables) +
				", " + formatComponent(
						"c2", recurrentPair.getContextC2(), variables) +
				", " + formatComponent("s", recurrentPair.getS(), variables) +
				", " + formatComponent("t", recurrentPair.getT(), variables);
	}

	/**
	 * Returns a string representation of the numeric parameters of
	 * a recurrent pair.
	 *
	 * @param recurrentPair a recurrent pair
	 * @return a string representation of the numeric parameters
	 */
	private static String formatParameters(RecurrentPair recurrentPair) {
		return formatMParameters(recurrentPair) +
				", " + formatNParameters(recurrentPair);
	}

	/**
	 * Returns a string representation of the m parameters.
	 *
	 * @param recurrentPair a recurrent pair
	 * @return a string representation of the m parameters
	 */
	private static String formatMParameters(RecurrentPair recurrentPair) {
		return "(m1,m2) = " + formatTuple(
				recurrentPair.getM1(),
				recurrentPair.getM2());
	}

	/**
	 * Returns a string representation of the n parameters.
	 *
	 * @param recurrentPair a recurrent pair
	 * @return a string representation of the n parameters
	 */
	private static String formatNParameters(RecurrentPair recurrentPair) {
		return "(n1,n2,n3,n4) = " + formatTuple(
				recurrentPair.getN1(),
				recurrentPair.getN2(),
				recurrentPair.getN3(),
				recurrentPair.getN4());
	}

	/**
	 * Returns a string representation of the generated nonterminating query.
	 *
	 * @param recurrentPair a recurrent pair
	 * @return a string representation of the generated nonterminating query
	 */
	private static String formatNonTerminatingQuery(RecurrentPair recurrentPair) {
		return "non-terminating query = " +
				recurrentPair.getNonTerminatingTerm();
	}

	/**
	 * Returns a string representation of a binary logic program rule.
	 *
	 * @param head the head of the rule
	 * @param body the single body atom of the rule
	 * @param variables the variable names used in the string representation
	 * @return a string representation of the rule
	 */
	private static String formatBinaryRule(
			Function head,
			Term body,
			Map<Variable,String> variables) {
		return head.toString(variables, false) +
				" :- " + body.toString(variables, false);
	}

	/**
	 * Returns a string representation of a named component of a
	 * recurrent pair.
	 *
	 * @param name the name of the component
	 * @param component the component to format
	 * @param variables the variable names used in the string representation
	 * @return a string representation of the named component
	 */
	private static String formatComponent(
			String name,
			Term component,
			Map<Variable,String> variables) {
		return name + " = " + component.toString(variables, false);
	}

	/**
	 * Returns a string representation of a tuple of integers.
	 *
	 * @param values the tuple values
	 * @return a string representation of the tuple
	 */
	private static String formatTuple(int... values) {
		StringBuilder result = new StringBuilder("(");

		for (int i = 0; i < values.length; i++) {
			if (0 < i)
				result.append(",");

			result.append(values[i]);
		}

		return result.append(")").toString();
	}
}
