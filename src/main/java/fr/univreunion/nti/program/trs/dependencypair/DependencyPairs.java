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

package fr.univreunion.nti.program.trs.dependencypair;

import java.util.Collection;
import java.util.Deque;
import java.util.Iterator;
import java.util.LinkedList;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;

/**
 * A collection of dependency pairs of a TRS.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DependencyPairs implements Iterable<RuleTrs> {

	/**
	 * The dependency pairs of this collection.
	 */
	private final Deque<RuleTrs> rules = new LinkedList<>();

	/**
	 * Builds a collection of dependency pairs consisting
	 * of the specified rules.
	 *
	 * @param rules the rules of this collection
	 */
	public DependencyPairs(Collection<? extends RuleTrs> rules) {
		this.rules.addAll(rules);
	}

	/**
	 * Deep copy constructor.
	 *
	 * @param dependencyPairs the dependency pairs to copy
	 */
	private DependencyPairs(DependencyPairs dependencyPairs) {
		for (RuleTrs rule : dependencyPairs)
			this.rules.add(rule.deepCopy());
	}

	/**
	 * Returns a deep copy of this collection.
	 */
	public DependencyPairs copy() {
		return new DependencyPairs(this);
	}

	/**
	 * Returns the number of rules in this collection.
	 */
	public int size() {
		return this.rules.size();
	}

	/**
	 * Returns <code>true</code> iff this collection
	 * contains the specified element.
	 *
	 * @param rule element whose presence in this collection
	 * is to be tested
	 * @return <code>true</code> iff this collection
	 * contains the specified element
	 */
	public boolean contains(RuleTrs rule) {
		return this.rules.contains(rule);
	}

	/**
	 * Returns an iterator over the rules of this collection.
	 */
	@Override
	public Iterator<RuleTrs> iterator() {
		return this.rules.iterator();
	}

	/**
	 * Returns a <code>Deque</code> consisting of the rules
	 * of this collection.
	 */
	public Deque<RuleTrs> toDeque() {
		return new LinkedList<>(this.rules);
	}

	/**
	 * Returns the dependency pairs of this collection
	 * as a collection of pairs of terms.
	 *
	 * @return the dependency pairs of this collection
	 * as a collection of pairs of terms
	 */
	public Collection<PairOfTerms> toPairsOfTerms() {

		// The collection to return at the end.
		Collection<PairOfTerms> pairs = new LinkedList<>();

		for (RuleTrs rule : this.rules)
			pairs.add(new PairOfTerms(rule, rule.getLeft(), rule.getRight()));

		return pairs;
	}

	/**
	 * Returns a String representation of this collection.
	 */
	@Override
	public String toString() {
		return this.rules.toString();
	}
}
