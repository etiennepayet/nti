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

package fr.univreunion.nti.program.trs.family;

import java.util.HashSet;
import java.util.Set;

import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Members of a term family (ascendants or descendants).
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Family {

	/**
	 * The term to which this family refers.
	 */
	private final Term root;

	/**
	 * The families of <code>t_1,...,t_m</code> when
	 * <code>root</code> has the form <code>f(t_1,...,t_m)</code>.
	 */
	private final Family[] arguments;

	/**
	 * The symbols that are reachable from <code>root</code>.
	 */
	private final Set<FunctionSymbol> reachable = new HashSet<FunctionSymbol>();

	/**
	 * <code>true</code> if and only if a variable is
	 * reachable from <code>root</code>.
	 */
	private boolean varReachable = false;

	/**
	 * Builds a family for the specified term.
	 * 
	 * @param t the term for which a family is built
	 * @throws NullPointerException if <code>t</code>
	 * is <code>null</code>
	 */
	public Family(Term t) {
		this.root = t.deepCopy();
		this.arguments = new Family[t.getRootSymbol().getArity()];
	}

	/**
	 * Adds all of the symbols in the specified set
	 * to the set of symbols which are reachable from
	 * the root term of this family, if they are not
	 * already present.
	 * 
	 * @param symbols some reachable symbols to be added
	 * to this family
	 * @throws NullPointerException if <code>symbols</code>
	 * is <code>null</code> or contains <code>null</code> 
	 */
	public void addAll(Set<FunctionSymbol> symbols) {
		for (FunctionSymbol f : symbols) {
			if (f == null)
				throw new NullPointerException(
						"cannot add null to a set of reachable elements");
			if (f == Variable.VARIABLE_ROOT_SYMBOL) 
				this.varReachable = true;
			this.reachable.add(f);
		}
	}

	/**
	 * Sets the family of the <code>i</code>-th argument
	 * of the root to the given family.
	 * 
	 * @param i the index of an argument of the root
	 * @param family a family
	 * @throws NullPointerException if the specified family
	 * is <code>null</code>
	 * @throws IndexOutOfBoundsException if the specified
	 * index is invalid
	 */
	public void add(int i, Family family) {
		if (family == null)
			throw new IllegalArgumentException(
					"cannot add null to a family");

		this.arguments[i] = family;
	}

	/**
	 * Returns <code>true</code> if and only if the specified
	 * symbol is reachable from the root term of this family.
	 * 
	 * @param f a symbol
	 * @return <code>true</code> if and only if the specified
	 * symbol is reachable from the root term of this family
	 */
	public boolean isReachable(FunctionSymbol f) {
		return this.reachable.contains(f);
	}

	/**
	 * Returns <code>true</code> if and only if a variable is
	 * reachable from the root term of this family.
	 * 
	 * @return <code>true</code> if and only if a variable is
	 * reachable from the root term of this family
	 */
	public boolean isVarReachable() {
		return this.varReachable;
	}

	/**
	 * Returns <code>true</code> iff this family
	 * contains the specified term.
	 * 
	 * @param t term whose presence in this family
	 * is to be tested
	 * @return <code>true</code> iff this family
	 * contains the specified term
	 */
	public boolean contains(Term t) {
		if (this.root instanceof Variable || t instanceof Variable)
			return true;

		if (this.isVarReachable() || this.isReachable(t.getRootSymbol()))
			return true;

		if (this.root.getRootSymbol() != t.getRootSymbol())
			return false;

		for (int i = 0; i < this.arguments.length; i++) {
			Family this_i = this.arguments[i];
			Position p = new Position(i);

			if (this_i != null && !this_i.contains(t.get(p))) return false;
		}

		return true;
	}

	/**
	 * Returns <code>true</code> iff the intersection of
	 * this family with the specified one is not empty.
	 * 
	 * @param F a family
	 * @return <code>true</code> iff the intersection of
	 * this family with the specified one is not empty
	 */
	public boolean intersects(Family F) {
		if (this.root instanceof Variable || F.root instanceof Variable)
			return true;

		if (this.isVarReachable() || F.isVarReachable())
			return true;

		if (this.isReachable(F.root.getRootSymbol()) || 
				F.isReachable(this.root.getRootSymbol()))
			return true;

		for (FunctionSymbol f : this.reachable)
			if (F.isReachable(f))
				return true;

		if (this.root.getRootSymbol() != F.root.getRootSymbol())
			return false;

		for (int i = 0; i < this.arguments.length; i++) {
			Family this_i = this.arguments[i];
			Family F_i = F.arguments[i];

			if (this_i != null || F_i != null) {
				if (this_i == null || F_i == null)
					return false;
				if (!this_i.intersects(F_i)) return false;
			}
		}

		return true;
	}
	
	/**
	 * Returns a String representation of this family.
	 * 
	 * @return a String representation of this family
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer();

		int n = this.arguments.length;
		if (n > 0) s.append('(');
		for (Family family : this.arguments) {
			s.append(family == null ? "null" : family.toString());
			if (1 < n--) s.append(",");
		}
		if (this.arguments.length > 0) s.append(')');

		return this.root.getRootSymbol() + s.toString() +
				":" + this.reachable.toString() + ":" +
				(this.varReachable ? "var_reach" : "var_not_reach");
	}
}
