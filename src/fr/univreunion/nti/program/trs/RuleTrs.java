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

package fr.univreunion.nti.program.trs;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.Rule;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;


/**
 * A term rewrite system rule.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class RuleTrs extends Rule {

	/**
	 * The left-hand side of this rule.
	 */
	protected Function left;

	/**
	 * The right-hand side of this rule
	 * (a function or a variable).
	 */
	protected Term right;

	/**
	 * Builds a TRS rule.
	 * 
	 * Called by the parser when reading the analyzed file.
	 * 
	 * @param left the left-hand side of the rule 
	 * @param right the right-hand side of the rule
	 * @param numberInFile the appearance number of the rule
	 * in the analyzed file
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 */
	public RuleTrs(Function left, Term right, Integer numberInFile) {
		super(numberInFile);
		
		if (right instanceof Variable || right instanceof Function) {
			this.left = left;
			this.right = right;
		}
		else
			throw new IllegalArgumentException(
					"construction of a TRS rule from an illegal RHS: " + right);
	}
	
	/**
	 * Builds a TRS rule. The appearance number of the rule
	 * is set to <code>null</code>.
	 * 
	 * @param left the left-hand side of the rule 
	 * @param right the right-hand side of the rule
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 */
	public RuleTrs(Function left, Term right) {
		this(left, right, null);
	}

	/**
	 * Returns a deep copy of this rule i.e., a rule
	 * whose left-hand and right-hand sides are deep
	 * copies of those of this rule.
	 * 
	 * The returned rule has an empty set of predecessors
	 * and an empty set of successors (those of this rule
	 * are not copied).
	 * 
	 * @return a deep copy of this rule
	 */
	public RuleTrs deepCopy() {
		return this.deepCopy(new HashMap<Term,Term>());
	}

	/**
	 * Returns a deep copy of this rule i.e., a rule whose
	 * left-hand and right-hand sides are deep copies of
	 * those of this rule.
	 * 
	 * The returned rule has an empty set of predecessors
	 * and an empty set of successors (those of this rule
	 * are not copied).
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * the term <code>s</code>, a subterm of this rule
	 * @return a deep copy of this rule
	 */
	public RuleTrs deepCopy(Map<Term,Term> copies) {
		return new RuleTrs(
				(Function) this.left.deepCopy(copies),
				this.right.deepCopy(copies),
				this.getNumberInFile());
	}

	/**
	 * Returns the left-hand side of this rule.
	 * 
	 * @return the left-hand side of this rule
	 */
	public Function getLeft() {
		return this.left;
	}

	/**
	 * Returns the right-hand side of this rule.
	 * 
	 * @return the right-hand side of this rule
	 */
	public Term getRight() {
		return this.right;
	}

	/**
	 * Checks whether this rule is a "generalized"
	 * rewrite rule i.e., a rule where extra
	 * variables occur in the right-hand side.
	 * 
	 * @return <code>true</code> iff this rule is
	 * a "generalized" rewrite rule 
	 */
	public boolean isGeneralized() {
		for (Position p : this.right) {
			Term r_p = this.right.get(p);
			if (r_p instanceof Variable) {
				if (!this.left.contains((Variable) r_p))
					return true;
			}
		}

		return false;
	}

	/**
	 * Returns the depth of this rule (max depth of
	 * its left-hand side and its right-hand side).
	 * 
	 * @return the depth of this rule
	 */
	public int depth() {
		int depth_l = this.left.depth();
		int depth_r = this.right.depth();
		return (depth_l > depth_r ? depth_l : depth_r);
	}

	/**
	 * Returns <code>true</code> iff this rule is connectable
	 * to the specified rule w.r.t. the specified TRS i.e.,
	 * the right-hand side of this rule is connectable to the
	 * left-hand side of the specified rule w.r.t. the
	 * specified TRS.
	 *  
	 * @param R a rule
	 * @param IR a TRS
	 * @return <code>true</code> iff this rule is connectable
	 * to the specified rule w.r.t. the specified TRS
	 */
	public boolean isConnectableTo(RuleTrs R, Trs IR) {
		return this.right.isConnectableTo(R.left, IR);
	}

	/**
	 * Returns a String representation of this rule
	 * relatively to the given set of variable symbols.
	 * 
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this rule: it stops at
	 * variable positions i.e., it does not consider the
	 * parent of a variable position.
	 * 
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this rule.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this rule
	 * @return a String representation of this rule
	 */
	public String toString(Map<Variable,String> variables, boolean shallow) {
		return
				this.left.toString(variables, shallow) +
				" -> " +
				this.right.toString(variables, shallow);
	}

	/**
	 * Returns a String representation of this rule.
	 * 
	 * @return a String representation of this rule
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<Variable,String>(), false);
	}
}
