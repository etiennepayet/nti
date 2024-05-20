/*
 * Copyright 2022 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.term;

import java.util.LinkedList;

/**
 * A function or predicate or tuple symbol.
 * 
 * An object of this class is immutable.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class FunctionSymbol {

	/**
	 * The symbols that are generated. This data structure
	 * is shared by all the threads that perform termination
	 * or non-termination proofs concurrently.
	 */
	private static final LinkedList<FunctionSymbol> SYMBOL_TABLE =
			new LinkedList<FunctionSymbol>();

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
	 * 
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
	private synchronized static FunctionSymbol lookup(String name, int arity, boolean tupleSymbol) {
		for (FunctionSymbol f : SYMBOL_TABLE)
			if (f.getArity() == arity && f.getName().equals(name) && f.isTupleSymbol() == tupleSymbol)
				return f;

		return null;
	}

	/**
	 * If a symbol with the specified name, arity and tuple property
	 * does not already exist, then creates one and inserts it in the
	 * symbol table. Otherwise, just returns the existing symbol.
	 * 
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
	private synchronized static FunctionSymbol addSymbol(String name, int arity, boolean tupleSymbol) {
		FunctionSymbol f = lookup(name, arity, tupleSymbol);

		if (f == null) {
			// If the symbol does not exist yet, we create it
			// and insert it into the symbol table.
			f = new FunctionSymbol(name, arity, tupleSymbol, SYMBOL_TABLE.size());
			SYMBOL_TABLE.add(f);
		}

		return f;
	}

	/**
	 * Static factory method. Builds a symbol with the specified
	 * name and arity if such a symbol does not already exist.
	 * Otherwise, just returns the existing symbol.
	 * 
	 * @param name the name of the symbol
	 * @param arity the arity of the symbol
	 * @return a symbol with the specified name and arity
	 */
	public synchronized static FunctionSymbol getInstance(String name, int arity) {
		return addSymbol(name, arity, false);
	}
	
	/**
	 * Returns the non-tuple symbol with the provided
	 * name and arity, if such a symbol exists,
	 * otherwise returns <code>null</code>.
	 * 
	 * @param name the name of the symbol
	 * @param arity the arity of the symbol
	 * @return a non-tuple symbol with the specified
	 * name and arity, or <code>null</code> if such a
	 * symbol does not exist
	 */
	public synchronized static FunctionSymbol get(String name, int arity) {
		return lookup(name, arity, false);
	}

	/**
	 * Constructs a symbol with the given name, arity, tuple property
	 * and index in the symbol table. The name must be
	 * non-<code>null</code> and the arity must be positive.
	 * 
	 * @param name the name of the symbol
	 * @param arity the arity of the symbol
	 * @param tupleSymbol a boolean indicating whether the symbol
	 * is a tuple symbol (used in the dependency pair framework)
	 * @param index the index of the symbol in the symbol table
	 * @throws IllegalArgumentException if <code>name</code> is
	 * <code>null</code> or <code>arity</code> is not positive
	 */
	private FunctionSymbol(String name, int arity, boolean tupleSymbol, int index) {
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
		// corresponding to this symbol and we
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
		// corresponding to this symbol and we create
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
	 * @return <code>false</code>, always, as this symbol
	 * is not a tuple symbol
	 */
	public boolean isTupleSymbol() {
		return this.tupleSymbol;
	}

	/**
	 * Returns <code>true</code> iff this function
	 * symbol is less than the specified one.
	 * 
	 * @param f a function symbol to be compared to
	 * this object
	 * @return <code>true</code> iff this function
	 * symbol is less than the specified one
	 */
	public boolean lt(FunctionSymbol f) {
		return this.index < f.index;
	}
	
	/**
	 * Returns a string representation of this symbol.
	 * 
	 * @return a string representation of this symbol
	 */
	@Override
	public String toString() {
		return (this.tupleSymbol ? this.name + "^#" : this.name); // + "/" + this.arity;
	}
	
	/**
	 * Returns a string representation of the symbol table.
	 * 
	 * This method is synchronized because it reads the
	 * symbol table, which is shared by all the proving
	 * threads.
	 * 
	 * @return a string representation of the symbol table
	 */
	public synchronized static String toStringSymbolTable() {
		StringBuffer s = new StringBuffer();
		for (FunctionSymbol f : SYMBOL_TABLE) {
			s.append(f.index);
			s.append(": ");
			s.append(f.name);
			s.append("/");
			s.append(f.arity);
			if (f.isTupleSymbol()) s.append(" [tuple symbol]");
			s.append("\n");
		}
		return s.toString();
	}
	
	/**
	 * Returns a String representation of some statistics
	 * about the symbol table.
	 * 
	 * This method is synchronized because it reads the
	 * symbol table, which is shared by all the proving
	 * threads.
	 * 
	 * @return a String representation of some statistics
	 * about the symbol table
	 */
	public synchronized static  String toStringStat() {
		int nbSymb = 0;
		int sumArity = 0;
		int minArity = -1, maxArity = -1;
		for (FunctionSymbol f : SYMBOL_TABLE) {
			if (!f.getName().startsWith(" ") && !f.isTupleSymbol()) {
				nbSymb++;
				int arity = f.getArity();
				sumArity += arity;
				if (minArity < 0 || arity < minArity)
					minArity = arity;
				if (maxArity < arity)
					maxArity = arity;
			}
		}
		
		StringBuffer s = new StringBuffer(nbSymb);
		s.append(" function symbol(s)");
		if (nbSymb > 0) {
			s.append(" -- arity: min=" + minArity);
			s.append(" max=" + maxArity);
			s.append(" avg=" + (((float)sumArity) / nbSymb));
		}
		
		return s.toString();
	}
}
