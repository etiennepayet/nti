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

import java.util.Collection;
import java.util.Map;

import fr.univreunion.nti.program.trs.Trs;

/**
 * A hole in a context.
 *
 * <p>The homeomorphic-embedding operation follows T. Arts and J. Giesl,
 * <a href="https://doi.org/10.1016/S0304-3975(99)00207-8">Termination of
 * Term Rewriting Using Dependency Pairs</a>, Theoretical Computer Science
 * 236(1--2), 133--178, 2000.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Hole extends Variable {

	/**
	 * A string representation for this hole.
	 */
	private final String representation;
	
	/**
	 * Builds a hole with the provided string representation.
	 * 
	 * @param representation a string representation for this hole
	 */
	public Hole(String representation) {
		this.representation = representation;
	}
	
	/**
	 * An auxiliary, internal, method which returns a
	 * deep copy of this term i.e., a copy where each
	 * subterm is also copied, except the variables
	 * not occurring in the specified collection.
	 * <p>
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied. 
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param varsToBeCopied a collection of variables
	 * that must be copied
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return a deep copy of this term
	 */
	@Override
	protected Term deepCopyAux(
			Collection<Variable> varsToBeCopied,
			Map<Term, Term> copies) {

		if (varsToBeCopied == null || varsToBeCopied.contains(this))
			return copies.computeIfAbsent(this,
					term -> new Hole(this.representation));

		return this;
	}
	
	/**
	 * An internal method which returns
	 * <code>REN(CAP(this term))</code>.
	 * <p>
	 * See [Arts &amp; Giesl, TCS'00] for a definition
	 * of <code>REN</code> and <code>CAP</code>.
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * @param trs the TRS whose defined symbols are used
	 * for computing the result
	 * @param root a boolean indicating whether the term
	 * at root position has to be replaced with a variable
	 * if its root symbol is defined in <code>trs</code>
	 * @return <code>REN(CAP(this term))</code>
	 */
	@Override
	protected Term rencap(Trs trs, boolean root) {
		return new Hole(this.representation);
	}
	
	/**
	 * An auxiliary, internal, method which returns a string
	 * representation of this term relatively to the given
	 * set of variable symbols.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * <p>
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 * Moreover, this term is supposed to be the schema of
	 * its class representative.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return a string representation of this term
	 */
	@Override
	protected String toStringAux(Map<Variable, String> variables, boolean shallow) {
		return this.representation;
	}
}
