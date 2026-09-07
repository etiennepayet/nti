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

package fr.univreunion.nti.term;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

/**
 * A function or predicate or tuple symbol.
 * <p>
 * An object of this class is immutable.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class FunctionSymbol {

	/**
	 * The symbols that are generated. This data structure
	 * is shared by all the threads that perform termination
	 * or nontermination proofs concurrently.
	 */
	private static final LinkedList<FunctionSymbol> SYMBOL_TABLE = new LinkedList<>();

	/**
	 * An index of the symbols in {@link #SYMBOL_TABLE} by name,
	 * arity and tuple property.
	 */
	private static final Map<SymbolKey, FunctionSymbol> SYMBOL_INDEX = new HashMap<>();

	/**
	 * The name of this symbol.
	 */
	private final String name;

	/**
	 * The arity of this symbol.
	 */
	private final int arity;

	/**
	 * A boolean indicating whether this symbol is
	 * a tuple symbol (used in the dependency pair
	 * framework).
	 */
	private final boolean tupleSymbol;

	/**
	 * The index of this symbol in the symbol table.
	 */
	private final int index;

	/**
	 * Searches for a symbol with the provided name, arity
	 * and tuple property in the symbol table.
	 * <p>
	 * This method is synchronized because it reads the
	 * symbol table, which is shared by all the proving
	 * threads.
	 *
	 * @param name the name of the symbol to search for
	 * @param arity the arity of the symbol to search for
	 * @param tupleSymbol a boolean indicating whether the
	 * symbol to search for is a tuple symbol
	 * @return a symbol in the symbol table with the provided
	 * name, arity and tuple property, or <code>null</code>
	 * if no such symbol exists
	 */
	private static synchronized FunctionSymbol lookup(String name, int arity, boolean tupleSymbol) {
		return SYMBOL_INDEX.get(new SymbolKey(name, arity, tupleSymbol));
	}

	/**
	 * If a symbol with the specified name, arity and tuple property
	 * does not already exist, then creates one and inserts it in the
	 * symbol table. Otherwise, just returns the existing symbol.
	 * <p>
	 * This method is synchronized because it reads the symbol table
	 * and writes elements into it, and this table is shared by all
	 * the proving threads.
	 *
	 * @param name the name of the symbol
	 * @param arity the arity of the symbol
	 * @param tupleSymbol a boolean indicating whether the symbol
	 * is a tuple symbol (used in the dependency pair framework)
	 * @return a symbol with the specified name, arity and tuple
	 * property
	 */
	private static synchronized FunctionSymbol addSymbol(String name, int arity, boolean tupleSymbol) {
		SymbolKey key = new SymbolKey(name, arity, tupleSymbol);
		return SYMBOL_INDEX.computeIfAbsent(key, ignored -> {
			// If the symbol does not exist yet, we create it
			// and insert it into the symbol table. The map inserts
			// it into the symbol index after this function returns.
			FunctionSymbol symbol =
					new FunctionSymbol(name, arity, tupleSymbol, SYMBOL_TABLE.size());
			SYMBOL_TABLE.add(symbol);
			return symbol;
		});
	}

	/**
	 * Returns the canonical non-tuple symbol with the specified
	 * name and arity, creating it if no such symbol exists yet.
	 *
	 * @param name the name of the symbol
	 * @param arity the arity of the symbol
	 * @return the canonical non-tuple symbol with the specified
	 * name and arity
	 */
	public static synchronized FunctionSymbol intern(String name, int arity) {
		return addSymbol(name, arity, false);
	}

	/**
	 * Returns the canonical non-tuple symbol with the
	 * specified name and arity, if such a symbol exists.
	 * This method does not create a new symbol.
	 *
	 * @param name the name of the symbol
	 * @param arity the arity of the symbol
	 * @return a non-tuple symbol with the specified
	 * name and arity, or <code>null</code> if such a
	 * symbol does not exist
	 */
	public static synchronized FunctionSymbol get(String name, int arity) {
		return lookup(name, arity, false);
	}

	/**
	 * Constructs a symbol with the given name, arity, tuple property
	 * and index in the symbol table. The name must be
	 * non-<code>null</code> and the arity must be non-negative.
	 *
	 * @param name the name of the symbol
	 * @param arity the arity of the symbol
	 * @param tupleSymbol a boolean indicating whether the symbol
	 * is a tuple symbol (used in the dependency pair framework)
	 * @param index the index of the symbol in the symbol table
	 * @throws IllegalArgumentException if <code>name</code> is
	 * <code>null</code> or <code>arity</code> is negative
	 */
	protected FunctionSymbol(String name, int arity, boolean tupleSymbol, int index) {
		if (name == null || arity < 0)
			throw new IllegalArgumentException(
					"a function symbol must have a non-null name" +
					"and a positive arity");

		this.name = name;
		this.arity = arity;
		this.tupleSymbol = tupleSymbol;
		this.index = index;
	}

	/**
	 * Returns the function symbol corresponding to this
	 * symbol.
	 *
	 * @return the function symbol corresponding to this
	 * symbol
	 */
	public FunctionSymbol toFunctionSymbol() {
		// If this symbol is not a function symbol
		// then we search for the function symbol
		// corresponding to this symbol, and we
		// create it if it does not already exist.
		if (this.isTupleSymbol())
			return addSymbol(this.name, this.arity, false);

		// If this symbol is already a function symbol
		// then we return it directly.
		return this;
	}

	/**
	 * Returns the tuple symbol corresponding to this
	 * symbol.
	 *
	 * @return the tuple symbol corresponding to this
	 * symbol
	 */
	public FunctionSymbol toTupleSymbol() {
		// If this symbol is already a tuple symbol
		// then we return it directly.
		if (this.isTupleSymbol())
			return this;

		// Otherwise, we search for the tuple symbol
		// corresponding to this symbol, and we create
		// it if it does not already exist.
		return addSymbol(this.name, this.arity, true);
	}

	/**
	 * Returns the arity of this function symbol.
	 *
	 * @return the arity of this function symbol
	 */
	public int getArity() {
		return this.arity;
	}

	/**
	 * Returns the name of this function symbol.
	 *
	 * @return the name of this function symbol
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * Returns <code>true</code> iff this symbol is a
	 * tuple symbol.
	 *
	 * @return <code>true</code> iff this symbol is a
	 * tuple symbol
	 */
	public boolean isTupleSymbol() {
		return this.tupleSymbol;
	}

	/**
	 * Returns <code>true</code> iff this symbol is a
	 * hat symbol.
	 *
	 * @return <code>true</code> iff this symbol is a
	 * hat symbol
	 */
	public boolean isHatSymbol() {
		return false;
	}

	/**
	 * Returns <code>true</code> iff this function
	 * symbol is less than the specified one.
	 *
	 * @param other a function symbol to be compared to
	 * this object
	 * @return <code>true</code> iff this function
	 * symbol is less than the specified one
	 */
	public boolean lt(FunctionSymbol other) {
		return this.index < other.index;
	}

	/**
	 * Returns a string representation of this symbol.
	 *
	 * @return a string representation of this symbol
	 */
	@Override
	public String toString() {
		return (this.tupleSymbol ? this.name + "^#" : this.name);
	}

	/**
	 * Returns a String representation of some statistics
	 * about the symbol table.
	 * <p>
	 * This method is synchronized because it reads the
	 * symbol table, which is shared by all the proving
	 * threads.
	 *
	 * @return a String representation of some statistics
	 * about the symbol table
	 */
	public static synchronized String toStringStat() {
		SymbolStatistics statistics = computeStatistics();

		StringBuilder result = new StringBuilder();
		result.append(statistics.count()).append(" function symbol(s)");
		if (statistics.count() > 0) {
			result.append(" -- arity: min=").append(statistics.minimumArity());
			result.append(" max=").append(statistics.maximumArity());
			result.append(" avg=").append(statistics.averageArity());
		}

		return result.toString();
	}

	/**
	 * Computes statistics for the ordinary symbols in the symbol table.
	 * Tuple symbols and internal symbols whose names start with a space are
	 * excluded.
	 *
	 * @return the computed symbol statistics
	 */
	private static SymbolStatistics computeStatistics() {
		int symbolCount = 0;
		int aritySum = 0;
		int minArity = -1;
		int maxArity = -1;
		for (FunctionSymbol symbol : SYMBOL_TABLE) {
			if (!symbol.getName().startsWith(" ") && !symbol.isTupleSymbol()) {
				symbolCount++;
				int arity = symbol.getArity();
				aritySum += arity;
				if (minArity < 0 || arity < minArity)
					minArity = arity;
				if (maxArity < arity)
					maxArity = arity;
			}
		}

		float averageArity = symbolCount == 0
				? 0.0f
				: ((float) aritySum) / symbolCount;
		return new SymbolStatistics(
				symbolCount, minArity, maxArity, averageArity);
	}

	/**
	 * Aggregate arities for the ordinary symbols in the symbol table.
	 */
	private record SymbolStatistics(
			int count,
			int minimumArity,
			int maximumArity,
			float averageArity) {}

	/**
	 * Lookup key for a canonical function symbol.
	 */
	private record SymbolKey(String name, int arity, boolean tupleSymbol) {}
}
