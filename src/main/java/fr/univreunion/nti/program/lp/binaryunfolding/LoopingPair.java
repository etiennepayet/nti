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

import java.util.LinkedList;
import java.util.List;
import java.util.StringJoiner;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.program.lp.SoP;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A looping pair, as defined by E. Payet and F. Mesnard in
 * <a href="https://doi.org/10.1145/1119479.1119481"><i>Non-Termination
 * Inference of Logic Programs</i></a>, ACM Transactions on Programming
 * Languages and Systems 28(2), pp. 256--289, 2006. It is
 * a pair of the form (BinSeq, tau) where BinSeq is
 * a sequence of binary logic program rules and tau
 * is a DN set of positions for BinSeq.
 * <p>
 * Looping pairs are used for inferring loops.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LoopingPair implements NonTerminationWitness {

	/**
	 * The binary sequence of this pair, i.e., a
	 * sequence of binary logic program rules.
	 */
	private final List<BinaryRuleLp> binarySequence;

	/**
	 * The set of positions of this pair. This set
	 * of positions is supposed to be DN for the
	 * binary sequence of this pair.
	 */
	private final SoP tau;

	/**
	 * Constructs a looping pair whose binary sequence
	 * consists of the given rules and whose set of
	 * positions is the given one (this method does not
	 * check that the given set of positions is DN for
	 * the given binary sequence).
	 * <p>
	 * The given binary sequence is expected to be non-empty: looping
	 * pairs are extended and checked through the first rule of their
	 * binary sequence.
	 *
	 * @param binarySequence the rules of the constructed pair
	 * @param tau the set of positions of the constructed pair
	 */
	public LoopingPair(List<BinaryRuleLp> binarySequence, SoP tau) {
		this.binarySequence = new LinkedList<>(binarySequence);
		this.tau = tau;
	}

	/**
	 * Suppose this pair has the form <code>(BinSeq, tau)</code>.
	 * It is expected that <code>BinSeq</code> is non-empty.
	 * <p>
	 * If the body atom of the given binary rule <code>rule</code> is
	 * <code>tau</code>-more general than the head of the first
	 * rule of <code>BinSeq</code>, then a new looping pair
	 * <code>(BinSeq', tau')</code> is constructed and returned:
	 * <code>BinSeq'=[rule].BinSeq</code> and <code>tau'</code>
	 * is a set of positions that is DN for <code>BinSeq'</code>.
	 * If the body atom of <code>rule</code> is not <code>tau</code>-more
	 * general than the head of the first rule of <code>BinSeq</code>,
	 * then this looping pair is returned.
	 *
	 * @param rule a binary logic program rule
	 * @return a new looping pair if the body atom of <code>rule</code> is
	 * <code>tau</code>-more general than the head of the first rule of
	 * <code>BinSeq</code> and this looping pair otherwise
	 */
	@Override
	public LoopingPair add(BinaryRuleLp rule) {
		BinaryRuleLp firstRule = getFirstRule();
		if (rule.getBodyPredicateSymbol() ==
				firstRule.getHeadPredicateSymbol() &&
				rule.isTauPluggableInto(firstRule, this.tau)) {
			List<BinaryRuleLp> extendedBinarySequence =
					buildSequenceWithPrependedRule(rule);
			return new LoopingPair(extendedBinarySequence,
					new SoP(rule, this.binarySequence, this.tau));
		}
		return this;
	}

	/**
	 * Builds a new binary sequence obtained by prepending the given rule
	 * to the binary sequence of this looping pair.
	 *
	 * @param rule the binary rule prepended to this binary sequence
	 * @return a new binary sequence starting with <code>rule</code>
	 */
	private List<BinaryRuleLp> buildSequenceWithPrependedRule(
			BinaryRuleLp rule) {
		LinkedList<BinaryRuleLp> extendedBinarySequence =
				new LinkedList<>(this.binarySequence);
		extendedBinarySequence.addFirst(rule);
		return extendedBinarySequence;
	}

	/**
	 * Checks whether this pair is a witness of the existence of a
	 * loop for the given mode.
	 * <p>
	 * This method only uses the first rule of this pair's binary
	 * sequence. It succeeds when the head predicate symbol of this
	 * rule is the predicate symbol of <code>mode</code>, and when
	 * each argument position selected by <code>mode</code> is either
	 * distinguished by this pair's set of positions or already ground
	 * in the head of the rule. In that case, the returned atomic query
	 * is obtained by grounding the head using <code>mode</code> and
	 * this pair's set of positions.
	 *
	 * @param mode a mode for which a loop is to be
	 * found
	 * @return a (non-<code>null</code>) atomic
	 * query starting a loop corresponding to
	 * <code>mode</code> or <code>null</code>, if this
	 * pair is not a witness of the existence of a
	 * loop for <code>mode</code>
	 */
	@Override
	public Function provesNonTerminationOf(Mode mode) {
		if (this.binarySequence.isEmpty())
			return null;

		BinaryRuleLp rule = getFirstRule();
		Function head = rule.getHead();
		FunctionSymbol headPredicateSymbol = head.getRootSymbol();
		if (headPredicateSymbol == mode.getPredSymbol() &&
				coversAllModeArguments(rule, headPredicateSymbol, mode))
			return head.ground(mode, this.tau);

		return null;
	}

	/**
	 * Returns <code>true</code> if this looping pair covers all the
	 * argument positions selected by the given mode for the head of the
	 * given rule.
	 *
	 * @param rule the rule whose head is checked
	 * @param headPredicateSymbol the predicate symbol of the head of
	 * <code>rule</code>
	 * @param mode the mode whose argument positions are checked
	 * @return <code>true</code> if each argument position of
	 * <code>mode</code> is either distinguished by this pair's set of
	 * positions or already ground in the head of <code>rule</code>,
	 * and <code>false</code> otherwise
	 */
	private boolean coversAllModeArguments(
			BinaryRuleLp rule,
			FunctionSymbol headPredicateSymbol,
			Mode mode) {
		for (Integer argumentIndex: mode)
			if (!this.tau.isInDomain(headPredicateSymbol, argumentIndex) &&
					!rule.isGroundHeadArgument(argumentIndex))
				return false;
		return true;
	}

	/**
	 * Returns the first rule of the binary sequence of this looping pair.
	 *
	 * @return the first rule of this pair's binary sequence
	 */
	private BinaryRuleLp getFirstRule() {
		return this.binarySequence.getFirst();
	}

	/**
	 * Returns the body predicate required of a rule which can extend this pair.
	 *
	 * @return the head predicate of the first rule in this pair
	 */
	FunctionSymbol getRequiredBodyPredicateSymbol() {
		return this.getFirstRule().getHeadPredicateSymbol();
	}

	/**
	 * Returns a short String representation of this witness.
	 *
	 * @return a short String representation of this witness
	 */
	@Override
	public String getShortDescription() {
		return "(extracted from a looping pair [Payet and Mesnard, TOPLAS'06])";
	}

	/**
	 * Returns a string representation of this looping pair.
	 *
	 * @return a string representation of this looping pair
	 */
	@Override
	public String toString() {
		return "Looping pair: binseq = <" + formatBinarySequence() +
				">, DN set of positions = " + this.tau +
				" (see [Payet and Mesnard, TOPLAS'06])";
	}

	/**
	 * Returns a string representation of the binary sequence of this
	 * looping pair.
	 *
	 * @return a string representation of this pair's binary sequence
	 */
	private String formatBinarySequence() {
		StringJoiner joiner = new StringJoiner(", ");
		for (BinaryRuleLp rule: this.binarySequence)
			joiner.add(rule.toString());

		return joiner.toString();
	}
}
