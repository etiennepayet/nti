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

import fr.univreunion.nti.program.recurrentpair.RecurrentPair;
import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;

/**
 * A logic-program recurrent pair for proving the existence of a binary chain,
 * as defined in Sect. 5 of E. Payet,
 * <a href="https://doi.org/10.1007/s10817-023-09693-z"><i>Non-Termination
 * in Term Rewriting and Logic Programming</i></a>, Journal of Automated
 * Reasoning 68, article 4, 2024.
 *
 * <p>The accepted form also includes the extension of E. Payet,
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10"><i>Recurrent Pairs
 * Revisited</i></a>, LOPSTR 2025, LNCS 16117, pp. 154--164, 2026.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RecurrentPairLp implements NonTerminationWitness {

	/**
	 * The pending rule R2 used to complete this recurrent pair, or
	 * <code>null</code> if this recurrent pair is already complete.
	 */
	private final BinaryRuleLp pendingSecondRule;

	/**
	 * A recurrent pair constructed from R1 and R2.
	 */
	private final RecurrentPair recurrentPair;

	/**
	 * Builds an incomplete recurrent pair containing
	 * only the rule R2.
	 * <p>
	 * This recurrent pair will have to be completed
	 * later using method <code>add</code>.
	 * 
	 * @param secondRule the rule R2 of this recurrent pair
	 * @throws IllegalArgumentException if <code>secondRule</code>
	 * is <code>null</code>
	 */
	public RecurrentPairLp(BinaryRuleLp secondRule) {
		if (secondRule == null)
			throw new IllegalArgumentException(
					"construction of a recurrent pair with a null rule");

		this.pendingSecondRule = secondRule;
		this.recurrentPair = null;
	}

	/**
	 * Constructs a complete recurrent pair.
	 * <p>
	 * This internal constructor assumes that the provided abstract
	 * recurrent pair is non-<code>null</code>.
	 *
	 * @param recurrentPair the abstract recurrent pair built from R1
	 * and R2
	 */
	private RecurrentPairLp(RecurrentPair recurrentPair) {

		this.pendingSecondRule = null;
		this.recurrentPair = recurrentPair;
	}

	/**
	 * Tries to build a complete recurrent pair from the provided binary
	 * rules.
	 *
	 * @param firstRule the rule R1
	 * @param secondRule the rule R2
	 * @return the recurrent pair built from the provided rules, or
	 * <code>null</code> if no such pair can be built
	 */
	private static RecurrentPairLp tryBuildFrom(
			BinaryRuleLp firstRule,
			BinaryRuleLp secondRule) {
		RecurrentPair recurrentPair =
				tryBuildRecurrentPair(firstRule, secondRule);
		if (recurrentPair == null) return null;
		return new RecurrentPairLp(recurrentPair);
	}

	/**
	 * Tries to build an abstract recurrent pair from the provided binary
	 * rules.
	 *
	 * @param firstRule the rule R1
	 * @param secondRule the rule R2
	 * @return the abstract recurrent pair built from the provided rules,
	 * or <code>null</code> if no such pair can be built
	 */
	private static RecurrentPair tryBuildRecurrentPair(
			BinaryRuleLp firstRule,
			BinaryRuleLp secondRule) {
		Function firstHead = firstRule.getHead();
		Term firstBody = firstRule.getBody(0);
		Function secondHead = secondRule.getHead();
		Term secondBody = secondRule.getBody(0);
		return RecurrentPair.tryBuild(firstHead, firstBody,
				secondHead, secondBody);
	}

	/**
	 * Builds a complete recurrent pair from this
	 * one and the provided binary rule.
	 * <p>
	 * An incomplete recurrent pair contains only R2. In that case,
	 * this method tries to complete it as <code>(R1, R2)</code>,
	 * where <code>R1</code> is the provided rule. If this recurrent
	 * pair is already complete, or if no complete recurrent pair can be
	 * built from the provided rule, then this recurrent pair is returned.
	 *
	 * @param firstRule a binary logic program rule
	 * @return a new recurrent pair or this
	 * recurrent pair
	 * @throws IllegalArgumentException if <code>firstRule</code>
	 * is <code>null</code>
	 */
	@Override
	public RecurrentPairLp add(BinaryRuleLp firstRule) {

		if (firstRule == null)
			throw new IllegalArgumentException(
					"construction of a recurrent pair with a null rule");

		return tryCompleteWith(firstRule);
	}

	/**
	 * Tries to complete this recurrent pair.
	 * <p>
	 * If this recurrent pair is already complete, then it is returned
	 * unchanged. Otherwise, this method tries to complete the pending
	 * rule R2 as <code>(R1, R2)</code>, where <code>R1</code> is the
	 * provided rule.
	 *
	 * @param firstRule the candidate rule R1
	 * @return the completed recurrent pair if it can be built, and
	 * this recurrent pair otherwise
	 */
	private RecurrentPairLp tryCompleteWith(BinaryRuleLp firstRule) {
		BinaryRuleLp secondRule = this.pendingSecondRule;
		if (secondRule == null ||
				firstRule.getBodyPredicateSymbol() !=
						secondRule.getHeadPredicateSymbol() ||
				secondRule.getBodyPredicateSymbol() !=
						firstRule.getHeadPredicateSymbol())
			return this;

		RecurrentPairLp completedPair =
				tryBuildFrom(firstRule, secondRule);
		if (completedPair != null) return completedPair;
		return this;
	}

	/**
	 * Returns <code>true</code> if this recurrent pair is complete,
	 * i.e., if it contains a recurrent pair built from R1 and R2.
	 *
	 * @return <code>true</code> if this recurrent pair is complete,
	 * and <code>false</code> otherwise
	 */
	boolean isComplete() {
		return this.recurrentPair != null;
	}

	/**
	 * Returns the head predicate required of a rule which can complete this
	 * recurrent pair.
	 *
	 * @return the body predicate of the pending second rule, or
	 * <code>null</code> if this pair is complete
	 */
	FunctionSymbol getRequiredHeadPredicateSymbol() {
		BinaryRuleLp secondRule = this.pendingSecondRule;
		return secondRule == null ?
				null : secondRule.getBodyPredicateSymbol();
	}

	/**
	 * Returns the body predicate required of a rule which can complete this
	 * recurrent pair.
	 *
	 * @return the head predicate of the pending second rule, or
	 * <code>null</code> if this pair is complete
	 */
	FunctionSymbol getRequiredBodyPredicateSymbol() {
		BinaryRuleLp secondRule = this.pendingSecondRule;
		return secondRule == null ?
				null : secondRule.getHeadPredicateSymbol();
	}

	/**
	 * Checks whether this pair is a witness for the existence of a
	 * binary chain for the given mode.
	 * <p>
	 * This method succeeds only if this recurrent pair is complete,
	 * provides a nonterminating term, and this term has the predicate
	 * symbol of <code>mode</code>. Moreover, every argument position
	 * selected by <code>mode</code> must be ground in that term.
	 * 
	 * @param mode a mode for which a binary chain
	 * is to be found
	 * @return a (non-<code>null</code>) atomic
	 * query starting a binary chain corresponding
	 * to <code>mode</code> or <code>null</code>,
	 * if this pair is not a witness of the
	 * existence of a binary chain for
	 * <code>mode</code>
	 */
	@Override
	public Function provesNonTerminationOf(Mode mode) {
		RecurrentPair completePair = this.recurrentPair;
		if (completePair == null)
			return null;

		Function nonterminating = completePair.getNonTerminatingTerm();
		if (nonterminating == null)
			return null;

		if (nonterminating.getRootSymbol() != mode.getPredSymbol())
			return null;

		if (isGroundOnModeArguments(nonterminating, mode))
			return nonterminating;

		return null;
	}

	/**
	 * Returns <code>true</code> if all argument positions selected by
	 * the given mode are ground in the given term.
	 *
	 * @param term the term whose arguments are checked
	 * @param mode the mode whose argument positions are checked
	 * @return <code>true</code> if every argument position selected by
	 * <code>mode</code> is ground in <code>term</code>, and
	 * <code>false</code> otherwise
	 */
	private boolean isGroundOnModeArguments(Function term, Mode mode) {
		for (int argumentIndex: mode)
			if (!term.get(argumentIndex).isGround())
				return false;
		return true;
	}

	/**
	 * Returns a short String representation of this witness.
	 * 
	 * @return a short String representation of this witness
	 */
	@Override
	public String getShortDescription() {
		return "(extracted from a recurrent pair [Payet, JAR'24+LOPSTR'25])";
	}

	/**
	 * Returns a string representation of this
	 * recurrent pair.
	 * 
	 * @return a string representation of this
	 * recurrent pair
	 */
	@Override
	public String toString() {
		if (isComplete())
			return RecurrentPairLpFormatter.format(this.recurrentPair);

		return super.toString();
	}
}
