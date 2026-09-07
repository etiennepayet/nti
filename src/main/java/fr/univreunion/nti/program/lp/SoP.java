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

package fr.univreunion.nti.program.lp;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A set of positions with associated terms.
 * <p>
 * This class computes DN sets of positions used when constructing
 * looping pairs.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class SoP {

	/**
	 * The mappings p -> <[0,arity(p)-1] -> Term>.
	 */
	private final Map<FunctionSymbol,Term[]> mappings = new HashMap<>();

	/**
	 * Creates a DN set of positions for the given binary sequence.
	 *
	 * @param binarySequence a binary sequence (i.e., a sequence of binary
	 * logic program rules)
	 */
	public SoP(List<BinaryRuleLp> binarySequence) {
		// A DN set of positions has to satisfy DN1--DN4.
		for (BinaryRuleLp rule: binarySequence) enforceDN1(rule);
		for (BinaryRuleLp rule: binarySequence) enforceDN2(rule);
		for (BinaryRuleLp rule: binarySequence) enforceDN3(rule);
		enforceDN4(binarySequence);
	}

	/**
	 * Constructs a DN set of positions for the given binary rule and
	 * binary sequence.
	 * <p>
	 * The given set of positions is assumed to be DN for the given
	 * previous binary sequence. This constructor copies it and only computes
	 * the increment that makes the new set of positions DN for the
	 * rule prepended to the sequence. The constructed set of positions
	 * is included in the given one.
	 *
	 * @param rule a binary logic program rule
	 * @param previousBinarySequence the binary sequence for which
	 * <code>tau</code> is already DN, without <code>rule</code>
	 * @param tau a set of positions supposed to be DN for
	 * <code>previousBinarySequence</code>
	 */
	public SoP(
			BinaryRuleLp rule,
			List<BinaryRuleLp> previousBinarySequence,
			SoP tau) {
		copyMappingsFrom(tau);
		// Now this set of positions satisfies DN1--DN2 for previousBinarySequence.
		// It also has to satisfy DN1--DN2 for rule.
		enforceDN1(rule);
		enforceDN2(rule);
		// This set of positions has to satisfy DN3--DN4 for rule and
		// previousBinarySequence.
		List<BinaryRuleLp> extendedBinarySequence =
				buildSequenceWithPrependedRule(rule, previousBinarySequence);
		enforceDN3ForRulesWhoseBodyPredicateIs(
				rule.getHeadPredicateSymbol(), extendedBinarySequence);
		enforceDN4(extendedBinarySequence);
	}

	/**
	 * Copies all mappings from the given set of positions into this one.
	 *
	 * @param tau the set of positions whose mappings are copied
	 */
	private void copyMappingsFrom(SoP tau) {
		for (Map.Entry<FunctionSymbol, Term[]> predicateMapping:
				tau.mappings.entrySet())
			mappings.put(
					predicateMapping.getKey(),
					predicateMapping.getValue().clone());
	}

	/**
	 * Builds a new binary sequence obtained by prepending the given rule
	 * to the given binary sequence.
	 *
	 * @param rule the binary rule prepended to the sequence
	 * @param binarySequence the binary sequence after <code>rule</code>
	 * @return a new binary sequence starting with <code>rule</code>
	 */
	private List<BinaryRuleLp> buildSequenceWithPrependedRule(
			BinaryRuleLp rule,
			List<BinaryRuleLp> binarySequence) {
		List<BinaryRuleLp> extendedBinarySequence =
				new ArrayList<>(binarySequence);
		extendedBinarySequence.addFirst(rule);
		return extendedBinarySequence;
	}

	/**
	 * Initializes the range of this set of positions to be max for the
	 * given predicate symbol, i.e., each argument position
	 * of the given predicate symbol is associated to a
	 * fresh variable.
	 *
	 * @param predicateSymbol a predicate symbol
	 * @return the variables associated to each argument
	 * position of <code>predicateSymbol</code>
	 */
	private Term[] initializeMaxRange(FunctionSymbol predicateSymbol) {
		Term[] predicateRange = new Term[predicateSymbol.getArity()];
		for (int argumentIndex = 0;
				argumentIndex < predicateRange.length;
				argumentIndex++)
			predicateRange[argumentIndex] = new Variable();
		mappings.put(predicateSymbol, predicateRange);
		return predicateRange;
	}

	/**
	 * Returns the range associated to the given predicate symbol, creating
	 * the max range first when no mapping exists yet.
	 *
	 * @param predicateSymbol a predicate symbol
	 * @return the range associated to <code>predicateSymbol</code>
	 */
	private Term[] rangeFor(FunctionSymbol predicateSymbol) {
		Term[] predicateRange = mappings.get(predicateSymbol);
		if (predicateRange == null)
			predicateRange = initializeMaxRange(predicateSymbol);
		return predicateRange;
	}

	/**
	 * Ensures that a range exists for the given predicate symbol.
	 *
	 * @param predicateSymbol a predicate symbol
	 */
	private void ensureRangeFor(FunctionSymbol predicateSymbol) {
		rangeFor(predicateSymbol);
	}

	/**
	 * Removes the given argument indexes from the domain of the given
	 * predicate range.
	 *
	 * @param predicateRange the range associated to a predicate symbol
	 * @param argumentIndexes the argument indexes to remove from the domain
	 * @return <code>true</code> if at least one argument index was requested for
	 * removal from the domain and <code>false</code> otherwise
	 */
	private boolean removeFromDomain(
			Term[] predicateRange,
			Iterable<Integer> argumentIndexes) {
		boolean domainChanged = false;

		for (Integer argumentIndex: argumentIndexes) {
			predicateRange[argumentIndex] = null;
			domainChanged = true;
		}

		return domainChanged;
	}

	/**
	 * Enforces DN1 on this set of positions for
	 * the given rule.
	 *
	 * @param rule a binary logic program rule
	 */
	private void enforceDN1(BinaryRuleLp rule) {
		Term[] headRange = rangeFor(rule.getHeadPredicateSymbol());

		removeFromDomain(headRange, rule.findDN1ViolatingHeadArgumentIndexes());
	}

	/**
	 * Enforces DN2 on this set of positions for
	 * the given rule.
	 *
	 * @param rule a binary logic program rule
	 */
	private void enforceDN2(BinaryRuleLp rule) {
		Term[] headRange = rangeFor(rule.getHeadPredicateSymbol());

		Term[] dn2Values = rule.computeDN2RequiredValues(this);
		System.arraycopy(dn2Values, 0, headRange, 0, dn2Values.length);
	}

	/**
	 * Enforces DN3 on this set of positions for
	 * the given rule.
	 *
	 * @param rule a binary logic program rule
	 */
	private void enforceDN3(BinaryRuleLp rule) {
		Term[] bodyRange = rangeFor(rule.getBodyPredicateSymbol());

		removeFromDomain(bodyRange, rule.findDN3ViolatingBodyArgumentIndexes(this));
	}

	/**
	 * Enforces DN3 on this set of positions for each rule in the given
	 * binary sequence whose body predicate symbol is the given predicate
	 * symbol.
	 *
	 * @param predicateSymbol the selected body predicate symbol
	 * @param binarySequence the binary sequence whose rules are filtered
	 */
	private void enforceDN3ForRulesWhoseBodyPredicateIs(
			FunctionSymbol predicateSymbol,
			List<BinaryRuleLp> binarySequence) {
		for (BinaryRuleLp rule: binarySequence)
			if (rule.getBodyPredicateSymbol() == predicateSymbol)
				enforceDN3(rule);
	}

	/**
	 * Enforces DN4 on this set of positions for
	 * the given binary sequence.
	 *
	 * @param binarySequence a binary sequence
	 */
	private void enforceDN4(List<BinaryRuleLp> binarySequence) {
		boolean domainChanged;

		do {
			domainChanged = false;
			for (BinaryRuleLp rule: binarySequence) {
				Term[] headRange = rangeFor(rule.getHeadPredicateSymbol());
				ensureRangeFor(rule.getBodyPredicateSymbol());

				if (removeFromDomain(
						headRange,
						rule.findDN4ViolatingHeadArgumentIndexes(this)))
					domainChanged = true;
			}
		}
		while (domainChanged);
	}

	/**
	 * Checks that the given argument index belongs to the argument range of
	 * the given predicate symbol.
	 *
	 * @param predicateSymbol the predicate symbol whose arity defines the range
	 * @param argumentIndex the argument index to check
	 * @throws IndexOutOfBoundsException unless
	 * {@code 0 <= argumentIndex && argumentIndex < predicateSymbol.getArity()}
	 */
	private static void validateArgumentIndex(
			FunctionSymbol predicateSymbol, int argumentIndex)
			throws IndexOutOfBoundsException {
		if (predicateSymbol != null &&
				(argumentIndex < 0 ||
				argumentIndex >= predicateSymbol.getArity()))
			throw new IndexOutOfBoundsException();
	}

	/**
	 * Returns {@code true} if {@code argumentIndex} is in the domain of the
	 * mapping associated with {@code predicateSymbol}, and {@code false}
	 * otherwise. A predicate symbol for which no mapping exists has an empty
	 * domain.
	 *
	 * @param predicateSymbol the predicate symbol whose mapping is queried
	 * @param argumentIndex the argument position to query
	 * @return {@code true} if {@code argumentIndex} is in the domain of the
	 * mapping for {@code predicateSymbol}, and {@code false} otherwise
	 * @throws IndexOutOfBoundsException unless
	 * {@code 0 <= argumentIndex && argumentIndex < predicateSymbol.getArity()}
	 */
	public boolean isInDomain(FunctionSymbol predicateSymbol, int argumentIndex)
			throws IndexOutOfBoundsException
	{
		validateArgumentIndex(predicateSymbol, argumentIndex);

		Term[] predicateRange = mappings.get(predicateSymbol);

		if (predicateRange == null)
			return false;

		return predicateRange[argumentIndex] != null;
	}

	/**
	 * Returns the term associated with {@code argumentIndex} in the mapping for
	 * {@code predicateSymbol}. If no mapping exists for the predicate symbol,
	 * or if the argument position is not in its mapping domain, {@code null} is
	 * returned.
	 *
	 * @param predicateSymbol the predicate symbol whose mapping is queried
	 * @param argumentIndex the argument position to query
	 * @return the term associated with {@code argumentIndex}, or {@code null}
	 * if that position has no mapping
	 * @throws IndexOutOfBoundsException unless
	 * {@code 0 <= argumentIndex && argumentIndex < predicateSymbol.getArity()}
	 */
	public Term getMappedTerm(FunctionSymbol predicateSymbol, int argumentIndex)
			throws IndexOutOfBoundsException
	{
		validateArgumentIndex(predicateSymbol, argumentIndex);

		Term[] predicateRange = mappings.get(predicateSymbol);

		if (predicateRange == null)
			return null;

		return predicateRange[argumentIndex];
	}

	/**
	 * Returns a String representation of the mapping of a predicate symbol.
	 *
	 * @param predicateSymbol the mapped predicate symbol
	 * @param predicateRange the range associated to
	 * <code>predicateSymbol</code>
	 * @param variables the variable names already used while printing this
	 * set of positions
	 * @return a String representation of the mapping of
	 * <code>predicateSymbol</code>
	 */
	private String formatPredicateMapping(
			FunctionSymbol predicateSymbol,
			Term[] predicateRange,
			Map<Variable,String> variables) {
		List<String> mappedArgumentEntries = new ArrayList<>();
		for (int argumentIndex = 0;
				argumentIndex < predicateRange.length;
				argumentIndex++)
			if (predicateRange[argumentIndex] != null)
				mappedArgumentEntries.add(argumentIndex + "->" +
						predicateRange[argumentIndex].toString(
								variables, false));

		return predicateSymbol + "/" +
				predicateSymbol.getArity() +
				"->{" +
				String.join(", ", mappedArgumentEntries) +
				"}";
	}

	/**
	 * Returns a String representation of this set of
	 * positions with associated terms.
	 *
	 * @return a String representation of this set of
	 * positions with associated terms
	 */
	@Override
	public String toString() {
		// A set of pairs (V,s) where s is
		// the symbol associated to variable V.
		Map<Variable,String> variables = new HashMap<>();
		List<String> predicateMappingEntries = new ArrayList<>();

		for (Map.Entry<FunctionSymbol, Term[]> predicateMapping:
				mappings.entrySet()) {
			predicateMappingEntries.add(formatPredicateMapping(
					predicateMapping.getKey(),
					predicateMapping.getValue(),
					variables));
		}

		return "<" + String.join(", ", predicateMappingEntries) + ">";
	}
}
