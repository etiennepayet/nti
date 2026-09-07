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

package fr.univreunion.nti.program.trs.reducpair;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A strict partial order on function symbols.
 * <p>
 * Used for defining lexicographic path orders, Knuth-Bendix orders...
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LexOrder {

	/**
	 * A data structure that maps any function symbol
	 * <code>f</code> to the set of function symbols
	 * <code>g</code> which are such that
	 * <code>f &gt; g</code>.
	 */
	private Relation order;

	/** Source read by this order until its first speculative mutation. */
	private final LexOrder speculativeSource;

	/**
	 * Builds an empty order.
	 */
	public LexOrder() {
		this.order = new Relation();
		this.speculativeSource = null;
	}

	/**
	 * Copy constructor.
	 *
	 * @param source the order to copy
	 */
	public LexOrder(LexOrder source) {
		this(source, false);
	}

	/**
	 * Builds a speculative view which materializes a deep copy of its source
	 * only if it is mutated.
	 *
	 * @param source the order read by the speculative view
	 */
	private LexOrder(LexOrder source, boolean deferCopy) {
		this.order = deferCopy ? null : new Relation(source.currentOrder());
		this.speculativeSource = deferCopy ? source : null;
	}

	/**
	 * Returns a speculative view of the specified order. For internal use by
	 * recursive order-completion attempts that only add precedence edges.
	 *
	 * @param source the order to view
	 * @return a speculative view of <code>source</code>
	 */
	public static LexOrder speculativeViewOf(LexOrder source) {
		return new LexOrder(source, true);
	}

	/**
	 * Adds the materialized precedence relation of this speculative view to the
	 * specified target. Does nothing if this view was never mutated. This is a
	 * monotonic union: it does not propagate removals performed with
	 * {@link #clear()}.
	 *
	 * @param target the order receiving this view's changes
	 */
	public void commitTo(LexOrder target) {
		if (this.order != null)
			target.addAll(this);
	}

	private Relation currentOrder() {
		LexOrder source = this;
		while (source.order == null)
			source = source.speculativeSource;
		return source.order;
	}

	private void materialize() {
		if (this.order == null)
			this.order = new Relation(this.speculativeSource.currentOrder());
	}

	/**
	 * Adds <code>f &gt; g</code> to this order.
	 *
	 * @param f a function symbol
	 * @param g a function symbol
	 * @return <code>true</code> if adding <code>f &gt; g</code>
	 * to this order succeeded and <code>false</code> otherwise
	 */
	public boolean add(FunctionSymbol f, FunctionSymbol g) {
		if (f == g) return false;

		if (this.currentOrder().contains(g, f)) return false;
		this.materialize();
		this.order.addPrecedence(f, g);

		return true;
	}

	/**
	 * Order union. Adds the specified order to this order.
	 * This operation may transform this order
	 * into an inconsistent order (i.e., an order where
	 * <code>f &gt; g</code> and <code>g &gt; f</code> occur,
	 * for some function symbols <code>f</code> and
	 * <code>g</code>).
	 *
	 * @param other the order to add to this order
	 */
	public void addAll(LexOrder other) {
		this.materialize();
		this.order.addAll(other.currentOrder());
	}

	/**
	 * Removes all the bindings <code>f &gt; g</code>
	 * from this order.
	 */
	public void clear() {
		this.materialize();
		this.order.clear();
	}

	/**
	 * Returns a string representation of this order.
	 */
	@Override
	public String toString() {
		StringBuilder s = new StringBuilder();
		this.currentOrder().appendTo(s);
		return s.toString();
	}

	/** An owned precedence relation, compact while it contains at most 8 edges. */
	private static final class Relation {
		private static final int MAX_COMPACT_EDGES = 8;
		private static final FunctionSymbol[] EMPTY_EDGES = new FunctionSymbol[0];

		/** Alternating source and target symbols, grouped in map/set iteration order. */
		private FunctionSymbol[] edges = EMPTY_EDGES;
		private int edgeCount;
		private Map<FunctionSymbol, Set<FunctionSymbol>> fallback;

		private Relation() {
		}

		private Relation(Relation source) {
			this.edgeCount = source.edgeCount;
			if (source.fallback == null)
				this.edges = source.edgeCount == 0 ? EMPTY_EDGES : source.edges.clone();
			else
				this.fallback = deepCopyOf(source.fallback);
		}

		private boolean contains(FunctionSymbol source, FunctionSymbol target) {
			if (this.fallback != null) {
				Set<FunctionSymbol> successors = this.fallback.get(source);
				return successors != null && successors.contains(target);
			}

			for (int index = 0; index < 2 * this.edgeCount; index += 2)
				if (this.edges[index] == source && this.edges[index + 1] == target)
					return true;
			return false;
		}

		private void addPrecedence(FunctionSymbol f, FunctionSymbol g) {
			if (this.fallback != null) {
				addGenericPrecedence(this.fallback, f, g);
				return;
			}

			FunctionSymbol[] closure = new FunctionSymbol[this.edgeCount + 1];
			int filledTargets = insertByBucket(closure, 0, g);
			int predecessorCount = 0;
			for (int index = 0; index < 2 * this.edgeCount; index += 2) {
				FunctionSymbol source = this.edges[index];
				FunctionSymbol target = this.edges[index + 1];
				if (source == g)
					filledTargets = insertByBucket(
							closure, filledTargets, target);
				if (source != f && target == f)
					closure[closure.length - ++predecessorCount] = source;
			}

			for (int targetIndex = 0; targetIndex < filledTargets; targetIndex++)
				this.addDirectEdge(f, closure[targetIndex]);
			for (int predecessorIndex = closure.length - 1;
					predecessorIndex >= closure.length - predecessorCount;
					predecessorIndex--)
				for (int targetIndex = 0; targetIndex < filledTargets; targetIndex++)
					this.addDirectEdge(closure[predecessorIndex], closure[targetIndex]);
		}

		private void addAll(Relation other) {
			if (other.fallback != null) {
				for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> entry :
						other.fallback.entrySet())
					for (FunctionSymbol target : entry.getValue())
						this.addDirectEdge(entry.getKey(), target);
			}
			else
				for (int index = 0; index < 2 * other.edgeCount; index += 2)
					this.addDirectEdge(other.edges[index], other.edges[index + 1]);
		}

		private void clear() {
			if (this.fallback == null)
				this.edgeCount = 0;
			else
				this.fallback.clear();
		}

		private void appendTo(StringBuilder result) {
			if (this.fallback != null) {
				appendGenericTo(this.fallback, result);
				return;
			}
			if (this.edgeCount == 0) {
				result.append("{}");
				return;
			}

			boolean firstSource = true;
			int index = 0;
			while (index < 2 * this.edgeCount) {
				FunctionSymbol source = this.edges[index];
				if (firstSource) firstSource = false;
				else result.append(", ");
				result.append(source).append(" > [");
				boolean firstTarget = true;
				while (index < 2 * this.edgeCount && this.edges[index] == source) {
					if (firstTarget) firstTarget = false;
					else result.append(", ");
					result.append(this.edges[index + 1]);
					index += 2;
				}
				result.append(']');
			}
		}

		private int endOfRow(int start, FunctionSymbol source) {
			int index = start;
			while (index < 2 * this.edgeCount && this.edges[index] == source)
				index += 2;
			return index;
		}

		private void addDirectEdge(FunctionSymbol source, FunctionSymbol target) {
			if (this.fallback != null) {
				this.fallback.computeIfAbsent(source, ignored -> new HashSet<>()).add(target);
				return;
			}
			if (this.contains(source, target)) return;
			if (this.edgeCount == MAX_COMPACT_EDGES) {
				this.promote();
				this.addDirectEdge(source, target);
				return;
			}

			if (this.edges.length == 0)
				this.edges = new FunctionSymbol[2 * MAX_COMPACT_EDGES];
			int insertion = this.insertionIndex(source, target);
			System.arraycopy(
					this.edges, insertion, this.edges, insertion + 2,
					2 * this.edgeCount - insertion);
			this.edges[insertion] = source;
			this.edges[insertion + 1] = target;
			this.edgeCount++;
		}

		private int insertionIndex(FunctionSymbol source, FunctionSymbol target) {
			int sourceBucket = bucket(source);
			int index = 0;
			while (index < 2 * this.edgeCount) {
				FunctionSymbol currentSource = this.edges[index];
				int currentBucket = bucket(currentSource);
				if (currentSource == source) {
					int targetBucket = bucket(target);
					while (index < 2 * this.edgeCount && this.edges[index] == source &&
							bucket(this.edges[index + 1]) <= targetBucket)
						index += 2;
					return index;
				}
				if (currentBucket > sourceBucket) return index;
				index = this.endOfRow(index, currentSource);
			}
			return index;
		}

		private void promote() {
			Map<FunctionSymbol, Set<FunctionSymbol>> promoted = new HashMap<>();
			for (int index = 0; index < 2 * this.edgeCount; index += 2)
				promoted.computeIfAbsent(
						this.edges[index],
						ignored -> new HashSet<>()).add(
								this.edges[index + 1]);
			this.fallback = promoted;
			this.edges = EMPTY_EDGES;
			this.edgeCount = 0;
		}

		private static int insertByBucket(
				FunctionSymbol[] symbols, int count, FunctionSymbol symbol) {
			int insertion = 0;
			int symbolBucket = bucket(symbol);
			while (insertion < count &&
					bucket(symbols[insertion]) <= symbolBucket)
				insertion++;
			System.arraycopy(
					symbols, insertion, symbols, insertion + 1,
					count - insertion);
			symbols[insertion] = symbol;
			return count + 1;
		}

		private static int bucket(FunctionSymbol symbol) {
			if (symbol == null) return 0;
			int hash = symbol.hashCode();
			return (hash ^ hash >>> 16) & 15;
		}

		private static Map<FunctionSymbol, Set<FunctionSymbol>> deepCopyOf(
				Map<FunctionSymbol, Set<FunctionSymbol>> source) {
			Map<FunctionSymbol, Set<FunctionSymbol>> copy = new HashMap<>();
			for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> entry : source.entrySet())
				copy.put(entry.getKey(), new HashSet<>(entry.getValue()));
			return copy;
		}

		private static void addGenericPrecedence(
				Map<FunctionSymbol, Set<FunctionSymbol>> relation,
				FunctionSymbol f,
				FunctionSymbol g) {
			Set<FunctionSymbol> successorsOfG = relation.get(g);
			Set<FunctionSymbol> successorsOfF =
					relation.computeIfAbsent(f, ignored -> new HashSet<>());
			Set<FunctionSymbol> transitiveSuccessorsOfG = new HashSet<>();
			transitiveSuccessorsOfG.add(g);
			if (successorsOfG != null) transitiveSuccessorsOfG.addAll(successorsOfG);
			successorsOfF.addAll(transitiveSuccessorsOfG);
			for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> entry : relation.entrySet())
				if (entry.getKey() != f && entry.getValue().contains(f))
					entry.getValue().addAll(transitiveSuccessorsOfG);
		}

		private static void appendGenericTo(
				Map<FunctionSymbol, Set<FunctionSymbol>> relation,
				StringBuilder result) {
			boolean firstSource = true;
			for (Map.Entry<FunctionSymbol, Set<FunctionSymbol>> entry : relation.entrySet()) {
				if (firstSource) firstSource = false;
				else result.append(", ");
				result.append(entry.getKey()).append(" > [");
				boolean firstTarget = true;
				for (FunctionSymbol target : entry.getValue()) {
					if (firstTarget) firstTarget = false;
					else result.append(", ");
					result.append(target);
				}
				result.append(']');
			}
			if (firstSource) result.append("{}");
		}
	}

}
