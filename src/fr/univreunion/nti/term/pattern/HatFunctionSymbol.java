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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.term.pattern;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Hole;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A hat function symbol, i.e., a function symbol
 * of the form <code>\hat{c}</code> where 
 * <code>c</code> is a 1-context.
 * 
 * It is used for building and handling simple
 * pattern terms. Its arity is always 1.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class HatFunctionSymbol extends FunctionSymbol {

	/**
	 * The hat symbols that are generated. This data structure
	 * is shared by all the threads that perform termination
	 * or nontermination proofs concurrently.
	 */
	private static final LinkedList<HatFunctionSymbol> SYMBOL_TABLE = new LinkedList<>();

	/**
	 * The 1-context of this symbol, where the hole
	 * \square_1 is replaced by a variable. 
	 */
	private final Term simpleContext;

	/**
	 * The variable that replaces the hole \square_1
	 * in the simple context of this symbol.
	 */
	private final Variable x;

	/**
	 * Searches for a hat symbol with the provided simple
	 * context in the symbol table.
	 * 
	 * <b>It is supposed that <code>simpleContext</code>
	 * is a simple context (NOT CHECKED).</b>
	 * 
	 * @param simpleContext a 1-context
	 * @return a hat symbol in the symbol table with the
	 * provided simple context, or <code>null</code> if
	 * no such symbol exists
	 */
	private static HatFunctionSymbol lookup(Term simpleContext) {
		for (HatFunctionSymbol f : SYMBOL_TABLE)
			if (f.simpleContext.isVariantOf(simpleContext))
				return f;

		return null;
	}

	/**
	 * If a hat symbol with the specified simple context does not
	 * already exist, then creates one and inserts it in the symbol
	 * table. Otherwise, just returns the existing symbol.
	 * 
	 * <b>It is supposed that <code>simpleContext</code>
	 * is a 1-context whose hole is <code>x</code> and
	 * that <code>simpleContext</code> is non-empty
	 * i.e., <code>simpleContext != x</code>
	 * (NOT CHECKED)</b>.
	 * 
	 * @param simpleContext a 1-context
	 * @param x the hole of <code>simpleContext</code>
	 * @return a hat symbol
	 */
	private static HatFunctionSymbol addSymbol(Term simpleContext, Variable x) {
		HatFunctionSymbol f = lookup(simpleContext);

		if (f == null) {
			// If the symbol does not exist yet, we create it
			// and insert it into the symbol table.
			f = new HatFunctionSymbol(simpleContext, x);
			SYMBOL_TABLE.add(f);
		}

		return f;
	}

	/**
	 * Static factory method. Builds a hat symbol from the
	 * specified 1-context if such a symbol does not already
	 * exist. Otherwise, just returns the existing symbol.
	 * 
	 * <b>It is supposed that <code>simpleContext</code>
	 * is a 1-context whose hole is <code>x</code>
	 * (NOT CHECKED).</b>
	 * 
	 * Moreover, <code>simpleContext</code> must be
	 * non-empty, i.e., <code>simpleContext != x</code>.
	 * 
	 * @param simpleContext a 1-context
	 * @param x the hole of <code>simpleContext</code>
	 * @return a hat symbol
	 * @throws IllegalArgumentException if
	 * <code>simpleContext == x</code>
	 */
	public static HatFunctionSymbol getInstance(Term simpleContext, Variable x) {
		if (simpleContext == x)
			throw new IllegalArgumentException(
					"a hat function symbol must have a non-empty simple context");
		
		return addSymbol(simpleContext, x);
	}

	/**
	 * Constructs a hat symbol.
	 * 
	 * <b>It is supposed that <code>simpleContext</code>
	 * is a 1-context whose hole is <code>x</code> and
	 * that <code>simpleContext</code> is non-empty
	 * i.e., <code>simpleContext != x</code>
	 * (NOT CHECKED)</b>.
	 * 
	 * @param simpleContext a 1-context
	 * @param x the hole of <code>simpleContext</code>
	 */
	private HatFunctionSymbol(Term simpleContext, Variable x) {
		// This does not insert this symbol into
		// the symbol table of the super class:		
		super("hat", 1, false, -1); 

		Map<Term, Term> copies = new HashMap<>();
		// 0x25A1 is the UFT-16 encoding of the white square character.
		copies.put(x, new Hole('\u25A1' + "")); 
		this.simpleContext = simpleContext.deepCopy(copies);
		this.x = (Variable) x.deepCopy(copies);
	}

	/**
	 * Returns <code>true</code> iff this symbol is a
	 * hat symbol.
	 * 
	 * @return <code>true</code> always
	 */
	@Override
	public boolean isHatSymbol() {
		return true;
	}

	/**
	 * Returns the 1-context of this symbol, where
	 * the hole \square_1 is replaced by a variable.
	 * 
	 * @return the 1-context of this symbol
	 */
	public Term getSimpleContext() {
		return this.simpleContext;
	}

	/**
	 * Returns the variable that replaces the hole
	 * \square_1 in the simple context of this symbol.
	 * 
	 * @return the variable that replaces the hole
	 * \square_1 in the simple context of this symbol 
	 */
	public Variable getVariable() {
		return this.x;
	}

	/**
	 * Returns a string representation of this hat symbol.
	 * 
	 * @return a string representation of this hat symbol
	 */
	@Override
	public String toString() {
		return "hat[" + this.simpleContext + "]";
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
		int k = 0;
		for (HatFunctionSymbol f : SYMBOL_TABLE) {
			s.append(k++);
			s.append(": ");
			s.append(f.simpleContext);
			s.append("\n");
		}
		return s.toString();
	}
}
