/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech.dependencypair.processor;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.term.FunctionSymbol;

/**
 * Computes the usable rules of an unfiltered dependency-pair problem, as
 * defined by Hirokawa and Middeldorp.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 * @see <a href="https://doi.org/10.1007/978-3-540-25979-4_18">
 * Dependency Pairs Revisited, Definition 20</a>
 */

final class UsableRules {

	/**
	 * This class cannot be instantiated.
	 */
	private UsableRules() {}

	/**
	 * Computes the usable rules of the specified problem in their original TRS
	 * order.
	 *
	 * @param problem a dependency-pair problem
	 * @return the usable rules, or an empty optional if the computation was
	 * interrupted
	 */
	static Optional<List<RuleTrs>> collect(DependencyPairProblem problem) {
		Trs trs = problem.getTRS();
		Set<FunctionSymbol> usableSymbols = new HashSet<>();

		for (RuleTrs pair : problem.getDependencyPairs())
			addDefinedSymbols(
					pair.getRight().getFunSymbols(), trs, usableSymbols);

		if (!closeUsableSymbols(trs, usableSymbols))
			return Optional.empty();

		List<RuleTrs> usableRules = new ArrayList<>();
		for (RuleTrs rule : trs) {
			if (Thread.currentThread().isInterrupted())
				return Optional.empty();
			if (usableSymbols.contains(rule.getLeft().getRootSymbol()))
				usableRules.add(rule);
		}

		return Optional.of(List.copyOf(usableRules));
	}

	/** Returns whether the specified TRS contains a generalized rule. */
	static boolean containsGeneralizedRule(Trs trs) {
		for (RuleTrs rule : trs)
			if (rule.isGeneralized())
				return true;
		return false;
	}

	/** Selects the term pairs produced by the specified usable rules. */
	static List<PairOfTerms> selectPairs(
			Collection<PairOfTerms> pairs, List<RuleTrs> rules) {

		Set<RuleTrs> selectedRules = new HashSet<>(rules);
		List<PairOfTerms> selectedPairs = new ArrayList<>();
		for (PairOfTerms pair : pairs)
			if (selectedRules.contains(pair.rule()))
				selectedPairs.add(pair);
		return selectedPairs;
	}

	/** Closes usable symbols transitively through right-hand sides. */
	private static boolean closeUsableSymbols(
			Trs trs, Set<FunctionSymbol> usableSymbols) {

		boolean changed;
		do {
			changed = false;
			for (RuleTrs rule : trs) {
				if (Thread.currentThread().isInterrupted())
					return false;
				if (usableSymbols.contains(rule.getLeft().getRootSymbol()) &&
						addDefinedSymbols(
								rule.getRight().getFunSymbols(), trs, usableSymbols))
					changed = true;
			}
		}
		while (changed);
		return true;
	}

	/** Adds the specified defined symbols to the target set. */
	private static boolean addDefinedSymbols(
			Set<FunctionSymbol> symbols,
			Trs trs,
			Set<FunctionSymbol> target) {

		boolean changed = false;
		for (FunctionSymbol symbol : symbols)
			if (trs.isDefined(symbol) && target.add(symbol))
				changed = true;
		return changed;
	}
}
