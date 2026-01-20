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

package fr.univreunion.nti.program.lp;

import java.util.LinkedList;
import java.util.Map;
import java.util.HashMap;
import java.util.Set;

import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A set of positions with associated terms.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class SoP {

	/**
	 * The mappings p -> <[0,arity(p)-1] -> Term>.
	 */
	private final HashMap<FunctionSymbol,Term[]> mappings = new HashMap<FunctionSymbol,Term[]>();

	/**
	 * Creates a set of positions that is DN for the given
	 * binary sequence.
	 *  
	 * @param binseq a binary sequence (ie a sequence of binary
	 * logic program rules)
	 */
	public SoP(LinkedList<BinaryRuleLp> binseq) {
		// this set of positions has to satisfy DN1--DN4:
		for (BinaryRuleLp R: binseq) satisfyDN1(R);
		for (BinaryRuleLp R: binseq) satisfyDN2(R);
		for (BinaryRuleLp R: binseq) satisfyDN3(R);
		satisfyDN4(binseq);
	}

	/**
	 * Constructs a set of positions that is DN for the given
	 * binary rule and the given binary sequence. The given
	 * set of positions is supposed to be DN for the given
	 * binary sequence and the construction of the new set of 
	 * positions only computes the increment that makes the
	 * new set of positions DN for the given rule and sequence.
	 * The constructed set of positions is "included" in the
	 * given one.
	 *  
	 * @param R a binary logic program rule
	 * @param binseq a binary sequence (ie a sequence of binary
	 * logic program rules)
	 * @param tau a set of positions supposed to be DN for 
	 * <code>binseq</code>
	 */
	public SoP(BinaryRuleLp R, LinkedList<BinaryRuleLp> binseq, SoP tau) {
		// first, make this object a clone of tau:
		int n;
		Term[] map_p_tau, map_p_this;
		Set<FunctionSymbol> keys = tau.mappings.keySet();
		for (FunctionSymbol p: keys) {
			map_p_tau  = tau.mappings.get(p);
			n = map_p_tau.length;
			map_p_this = new Term[n];
			for (int i = 0; i < n; i++)
				map_p_this[i] = map_p_tau[i];
			this.mappings.put(p, map_p_this);
		}
		// now this set of positions satisfies DN1--DN2 for binseq;
		// it also has to satisfy DN1--DN2 for R:
		satisfyDN1(R);
		satisfyDN2(R);
		// this set of positions has to satisfy DN3--DN4 for R and binseq:
		FunctionSymbol p = R.getHeadPredSymbol();
		LinkedList<BinaryRuleLp> binseqWithR = new LinkedList<BinaryRuleLp>(binseq);
		binseqWithR.addFirst(R);
		for (BinaryRuleLp RR: binseqWithR)
			if (RR.getBodyPredSymbol() == p)
				satisfyDN3(RR);
		satisfyDN4(binseqWithR);
	}

	/**
	 * Sets this set of positions to be max for the
	 * given predicate symbol, ie each argument position
	 * of the given predicate symbol is associated to a
	 * fresh variable.
	 * 
	 * @param p a predicate symbol
	 * @return the variables associated to each argument
	 * position of <code>p</code>
	 */
	private Term[] setMax(FunctionSymbol p) {
		Term[] map_p = new Term[p.getArity()];
		for (int i = 0; i < map_p.length; i++)
			map_p[i] = new Variable();
		this.mappings.put(p, map_p);
		return map_p;
	}

	/**
	 * Sets this set of positions to satisfy DN1 for
	 * the given rule.
	 * 
	 * @param R a binary logic program rule
	 */
	private void satisfyDN1(BinaryRuleLp R) {
		FunctionSymbol p = R.getHeadPredSymbol();
		Term[] map_p = this.mappings.get(p);
		if (map_p == null) map_p = setMax(p);

		LinkedList<Integer> DN1 = R.violateDN1();
		for (Integer i: DN1) map_p[i] = null;
	}

	/**
	 * Sets this set of positions to satisfy DN2 for
	 * the given rule.
	 * 
	 * @param R a binary logic program rule
	 */
	private void satisfyDN2(BinaryRuleLp R) {
		FunctionSymbol p = R.getHeadPredSymbol();
		Term[] map_p = this.mappings.get(p);
		if (map_p == null) map_p = setMax(p);

		Term[] DN2 = R.violateDN2(this);
		for (int i = 0; i < DN2.length; i++)
			map_p[i] = DN2[i];
	}

	/**
	 * Sets this set of positions to satisfy DN3 for
	 * the given rule.
	 * 
	 * @param R a binary logic program rule
	 */
	private void satisfyDN3(BinaryRuleLp R) {
		FunctionSymbol q = R.getBodyPredSymbol();
		Term[] map_q = this.mappings.get(q);
		if (map_q == null) map_q = setMax(q);

		LinkedList<Integer> DN3 = R.violateDN3(this);
		for (Integer i: DN3) map_q[i] = null;
	}

	/**
	 * Sets this set of positions to satisfy DN4 for
	 * the given binary sequence.
	 * 
	 * @param binseq a binary sequence
	 */
	private void satisfyDN4(LinkedList<BinaryRuleLp> binseq) {
		boolean doAgain;

		do {
			doAgain = false;
			for (BinaryRuleLp R: binseq) {
				FunctionSymbol p = R.getHeadPredSymbol();
				Term[] map_p = this.mappings.get(p);
				if (map_p == null) map_p = setMax(p);
				FunctionSymbol q = R.getBodyPredSymbol();
				if (this.mappings.get(q) == null) setMax(q);

				LinkedList<Integer> DN4 = R.violateDN4(this);
				for (Integer i: DN4) map_p[i] = null;
				if (!DN4.isEmpty()) doAgain = true;
			}
		}
		while (doAgain);
	}
	
	/**
	 * Returns <code>true</code> if the given integer
	 * <code>i</code> is in the domain of <code>this(p)</code>
	 * for the given predicate symbol <code>p</code> and
	 * <code>false</code> otherwise. If <code>i</code> is not
	 * in <code>[0,arity(p)-1]</code>, then an
	 * IndexOutOfBoundsException is thrown.
	 * 
	 * @param p the given predicate symbol
	 * @param i the given argument position of <code>p</code>
	 * @return <code>true</code> if <code>i</code> is in the
	 * domain of <code>this(p)</code> and <code>false</code> otherwise
	 * @throws IndexOutOfBoundsException
	 */
	public boolean inDomain(FunctionSymbol p, int i)
			throws IndexOutOfBoundsException
	{
		Term[] range = mappings.get(p);

		if (range == null)
			return false;

		if (i < 0 || i >= range.length)
			throw new IndexOutOfBoundsException();

		return range[i] != null;
	}
	
	/**
	 * Returns <code>this(p)(i)</code> for the given predicate
	 * symbol <code>p</code> and argument position <code>i</code>.
	 * If <code>i</code> is not distinguished by <code>this(p)</code>,
	 * then <code>null</code> is returned. If <code>i</code> is not
	 * in <code>[0,arity(p)-1]</code>, then an IndexOutOfBoundsException
	 * is thrown.
	 * 
	 * @param p the given predicate symbol
	 * @param i the given argument position of <code>p</code>
	 * @return <code>this(p)(i)</code>
	 * @throws IndexOutOfBoundsException if <code>i</code> is not
	 * in <code>[0,arity(p)-1]</code>
	 */
	public Term get(FunctionSymbol p, int i)
			throws IndexOutOfBoundsException
	{
		Term[] range = mappings.get(p);

		if (range == null)
			return null;

		if (i < 0 || i >= range.length)
			throw new IndexOutOfBoundsException();

		return range[i];
	}
	
	/**
	 * Returns a String representation of this set of
	 * positions with associated terms.
	 *
	 * @return a String representation of this set of
	 * positions with associated terms
	 */
	public String toString() {
		// A set of pairs (V,s) where s is
		// the symbol associated to variable V.
		HashMap<Variable,String> variables = new HashMap<Variable,String>();
		
		StringBuffer s = new StringBuffer("<");

		Set<Map.Entry<FunctionSymbol, Term[]>> entries = this.mappings.entrySet();
		int k = entries.size();
		for (Map.Entry<FunctionSymbol, Term[]> e : entries) {
			FunctionSymbol p = e.getKey();
			Term[] range_p = e.getValue();
			
			LinkedList<String> dom_p = new LinkedList<String>();
			for (int i = 0; i < range_p.length; i++)
				if (range_p[i] != null)
					dom_p.add(i + "->" + range_p[i].toString(variables, false));
			s.append(p);
			s.append("/");
			s.append(p.getArity());
			s.append("->{");
			int l = dom_p.size();
			for (String s_p: dom_p) {
					s.append(s_p);
					if (--l > 0) s.append(", ");
			}
			s.append("}");
			if (--k > 0) s.append(", ");
		}

		s.append(">");
		return s.toString();
	}
}
