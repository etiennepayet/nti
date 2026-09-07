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

package fr.univreunion.nti.program.trs;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.dependencypair.DependencyGraph;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairCollector;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.family.Family;
import fr.univreunion.nti.program.trs.family.FdGraph;
import fr.univreunion.nti.program.trs.prooftech.TrsTerminationProver;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;

/**
 * A term rewrite system (TRS).
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Trs extends Program implements Iterable<RuleTrs> {

	/**
	 * The rules of this TRS.
	 */
	protected final LinkedList<RuleTrs> rules = new LinkedList<>();

	/**
	 * The rewriting strategy (standard, innermost, ...)
	 * considered for this TRS.
	 */
	private final String strategy;

	/**
	 * The set of defined symbols of this TRS =
	 * {root(l) | l -> r in this TRS}.
	 */
	private final Set<FunctionSymbol> definedSymbols = new HashSet<>();

	/**
	 * The graph for computing descendants.
	 * Used for forward unfoldings in non-termination proofs.
	 */
	private FdGraph graphForward;

	/**
	 * The graph for computing ascendants.
	 * Used for backward unfoldings in non-termination proofs.
	 */
	private FdGraph graphBackward;

	/**
	 * The set of dependency pairs of this TRS.
	 */
	private final DependencyPairs dependencyPairs;

	/**
	 * The estimated dependency graph of this TRS, built on first access.
	 */
	private DependencyGraph dependencyGraph;

	/**
	 * Builds a term rewrite system (TRS).
	 *
	 * @param name the name of this TRS
	 * @param rules the rules of this TRS
	 * @param strategy the rewriting strategy considered for this TRS
	 * (only FULL i.e., standard rewriting, is supported for the moment)
	 * @throws IllegalArgumentException if a given rule is {@code null}
	 * or the provided strategy is not FULL
	 */
	public Trs(String name, Collection<RuleTrs> rules, String strategy) {

		super(name);

		// First, we build the rules of this TRS.
		for (RuleTrs rule : rules)
			if (rule != null) {
				// Add this rule to this TRS.
				this.rules.add(rule);
				// Complete the set D of defined symbols of this TRS.
				this.definedSymbols.add(rule.getLeft().getRootSymbol());
			}
			else
				throw new IllegalArgumentException("construction of a TRS with a null rule");

		// Then, we set the strategy.
		if (!"FULL".equals(strategy))
			throw new IllegalArgumentException(
					"unsupported strategy: only FULL (standard rewriting) is supported for the moment");
		this.strategy = strategy;

		// Finally, we build the dependency pairs of this TRS. The estimated
		// dependency graph is built lazily because actions such as printing do
		// not need it and its construction can be very expensive.
		this.dependencyPairs = new DependencyPairCollector().collectFrom(this);
		this.dependencyGraph = null;
	}

	/**
	 * Deep copy constructor.
	 * <p>
	 * If the specified <code>dependencyPairsCopy</code>
	 * is not <code>null</code>, then it is
	 * filled so that each dependency pair of
	 * <code>source</code> is mapped to its copy.
	 *
	 * @param source the TRS to copy
	 * @param dependencyPairsCopy a structure mapping each
	 * dependency pair of <code>source</code> to its
	 * copy
	 */
	private Trs(Trs source, Map<RuleTrs, RuleTrs> dependencyPairsCopy) {

		super(source.getName());

		// We copy the rules of source.
		for (RuleTrs rule : source)
			this.rules.add(rule.deepCopy());

		// We copy the strategy and the defined
		// symbols of source.
		this.strategy = source.strategy;
		this.definedSymbols.addAll(source.definedSymbols);

		// We copy the dependency pairs of source, and
		// we add the copies to the provided map
		// (if not null).
		LinkedList<RuleTrs> dependencyPairCopies = new LinkedList<>();
		for (RuleTrs rule : source.dependencyPairs) {
			RuleTrs ruleCopy = rule.deepCopy();
			if (dependencyPairsCopy != null) dependencyPairsCopy.put(rule, ruleCopy);
			dependencyPairCopies.add(ruleCopy);
		}
		this.dependencyPairs = new DependencyPairs(dependencyPairCopies);

		// The estimated dependency graph of this new object is built lazily.
		this.dependencyGraph = null;
	}

	/**
	 * Shallow copy constructor, i.e., the rules
	 * are deeply copied but the dependency pairs
	 * and the estimated dependency graph are set
	 * to <code>null</code>.
	 *
	 * @param source the TRS to copy
	 */
	private Trs(Trs source) {

		super(source.getName());

		// We copy the rules of source.
		for (RuleTrs rule : source)
			this.rules.add(rule.deepCopy());

		// We copy the strategy and the defined
		// symbols of source.
		this.strategy = source.strategy;
		this.definedSymbols.addAll(source.definedSymbols);

		// We do not copy and do not compute the dependency
		// pairs and the estimated dependency graph.
		this.dependencyPairs = null;
		this.dependencyGraph = null;
	}


	/**
	 * Returns a deep copy of this TRS.
	 * <p>
	 * If the specified <code>dependencyPairsCopy</code>
	 * is not <code>null</code>, then it is
	 * filled so that each dependency pair of
	 * this TRS is mapped to its copy.
	 *
	 * @param dependencyPairsCopy a structure mapping each
	 * dependency pair to its copy
	 * @return a deep copy of this TRS
	 */
	public Trs copy(Map<RuleTrs, RuleTrs> dependencyPairsCopy) {
		return new Trs(this, dependencyPairsCopy);
	}

	/**
	 * Returns a shallow copy of this TRS, i.e., the
	 * rules are deeply copied but the dependency pairs
	 * and the estimated dependency graph are not
	 * (the resulting TRS has undefined dependency pairs
	 * and estimated dependency graph).
	 *
	 * @return a shallow copy of this TRS
	 */
	public Trs shallowCopy() {
		return new Trs(this);
	}

	/**
	 * Returns the rewriting strategy
	 * (standard, innermost, ...)
	 * considered for this TRS.
	 *
	 * @return the rewriting strategy
	 * considered for this TRS
	 */
	public String getStrategy() {
		return this.strategy;
	}

	/**
	 * Returns the size of this TRS.
	 *
	 * @return the size of this TRS
	 */
	@Override
	public int size() {
		return this.rules.size();
	}

	/**
	 * Returns the depth of this TRS i.e., the
	 * maximal depth of the rules of this TRS.
	 *
	 * @return the depth of this TRS
	 */
	public int depth() {
		int max = -1;

		for (RuleTrs rule : this.rules) {
			int d = rule.depth();
			if (d > max) max = d;
		}

		return max;
	}

	/**
	 * Returns an iterator over the rules of this TRS.
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<RuleTrs> iterator() {
		return this.rules.iterator();
	}

	/**
	 * Returns {@code true} iff the provided symbol
	 * is defined in this TRS.
	 *
	 * @param f a function symbol
	 * @return {@code true} iff the provided symbol
	 * is defined in this TRS
	 */
	public boolean isDefined(FunctionSymbol f) {
		return this.definedSymbols.contains(f);
	}

	/**
	 * Returns {@code true} iff the root symbol of
	 * the provided term is defined in this TRS.
	 *
	 * @param t a term
	 * @return {@code true} iff the root symbol of the
	 * provided term is defined in this TRS
	 */
	public boolean isRootDefined(Term t) {
		return this.isDefined(t.getRootSymbol());
	}

	/**
	 * Computes the set of descendants of the given term
	 * w.r.t. this TRS.
	 *
	 * @param t the term whose descendants have
	 * to be computed
	 * @return the set of descendants of <code>t</code>
	 * w.r.t. this TRS
	 *
	 */
	public Family descendants(Term t) {
		if (this.graphForward == null)
			this.createGraphForward();

		return this.graphForward.getFamily(t);
	}

	/**
	 * Computes the set of ascendants of the given term
	 * w.r.t. this TRS.
	 *
	 * @param t the term whose ascendants have
	 * to be computed
	 * @return the set of ascendants of <code>t</code>
	 * w.r.t. this TRS
	 *
	 */
	public Family ascendants(Term t) {
		if (this.graphBackward == null)
			this.createGraphBackward();

		return this.graphBackward.getFamily(t);
	}

	/**
	 * Builds the graph for forward analysis.
	 */
	private void createGraphForward() {
		// We add edges of the form l -> r where
		// l -> r is a rule of this TRS.
		this.graphForward = new FdGraph(this);

		for (RuleTrs rule : this)
			this.graphForward.addEdge(rule.getLeft(), rule.getRight());

		this.graphForward.closeTransitively();
	}

	/**
	 * Builds the graph for backward analysis.
	 */
	private void createGraphBackward() {
		// We add edges of the form r -> l where
		// l -> r is a rule of this TRS.
		this.graphBackward = new FdGraph(this);

		for (RuleTrs rule : this)
			this.graphBackward.addEdge(rule.getRight(), rule.getLeft());

		this.graphBackward.closeTransitively();
	}

	/**
	 * Returns the estimated dependency graph of this TRS.
	 * The graph is built on the first call and then retained. A shallow TRS copy
	 * has no dependency pairs and therefore returns {@code null}.
	 *
	 * @return the estimated dependency graph of this TRS, or {@code null} for a
	 * shallow copy
	 */
	public synchronized DependencyGraph getDependencyGraph() {
		if (this.dependencyGraph == null && this.dependencyPairs != null)
			this.dependencyGraph = new DependencyGraph(this, this.dependencyPairs);

		return this.dependencyGraph;
	}

	/**
	 * Runs a termination proof for this program.
	 *
	 * @param context the context of the analysis
	 * @return the computed proof
	 */
	@Override
	public Proof proveTermination(AnalysisContext context) {
		return new TrsTerminationProver(this).prove(context);
	}

	/**
	 * Returns the rules of this TRS as a collection
	 * of pairs of terms.
	 *
	 * @return the rules of this TRS as a collection
	 * of pairs of terms
	 */
	public Collection<PairOfTerms> toPairsOfTerms() {

		// The collection to return at the end.
		Collection<PairOfTerms> pairs = new LinkedList<>();

		for (RuleTrs rule : this.rules)
			pairs.add(new PairOfTerms(rule, rule.getLeft(), rule.getRight()));

		return pairs;
	}

	/**
	 * Returns a String representation of this TRS.
	 *
	 * @return a String representation of this TRS
	 */
	@Override
	public String toString() {
		StringBuilder s = new StringBuilder("** BEGIN rewrite system: ");
		s.append(this.getName());

		// The rewriting strategy considered for this TRS.
		s.append("\n* Strategy = ");
		s.append(this.strategy);
		s.append("\n");

		// The rules of the TRS.
		int nbRules = this.rules.size();
		s.append("* ");
		s.append(nbRules);
		s.append(" rule(s)");
		if (0 < nbRules) s.append(":");
		s.append('\n');
		for (RuleTrs rule : this.rules) {
			s.append(rule);
			s.append("\n");
		}

		// Ending message.
		s.append("\n** END rewrite system: ");
		s.append(this.getName());

		return s.toString();
	}

	/**
	 * Returns a String representation of some statistics
	 * about this program.
	 *
	 * @return a String representation of some statistics
	 * about this program
	 */
	@Override
	public String toStringStat() {
		return new TrsStatisticsFormatter().format(this);
	}
}
