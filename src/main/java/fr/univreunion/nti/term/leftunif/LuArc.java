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

package fr.univreunion.nti.term.leftunif;

import java.util.Map;

import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * An arc between two nodes in a DAG.
 * 
 * Used in the left-unification algorithm
 * by Kapur et al., TCS 1991.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class LuArc {

	/**
	 * The cost of this arc (number of applications of rho).
	 */
	private final int cost;
	
	/**
	 * The direction of this arc (<code>true</code> for
	 * left-to-right, <code>false</code> for right-to-left).
	 */
	private final boolean dir;
	
	/**
	 * The target term of this arc.
	 */
	private final Term target;
	
	/**
	 * Indicates whether this arc is marked for deletion.
	 */
	private boolean deletion = false;
	
	/**
	 * Builds an arc in a DAG.
	 * 
	 * @param cost a cost for this arc
	 * @param dir a direction for this arc
	 * (<code>true</code> for left-to-right,
	 * <code>false</code> for right-to-left)
	 * @param target a target term for this arc
	 */
	public LuArc(int cost, boolean dir, Term target) {
		this.cost = cost;
		this.dir = dir;
		this.target = target;
	}
	
	/**
	 * Returns the cost of this arc.
	 * 
	 * @return the cost of this arc
	 */
	public int getCost() {
		return this.cost;
	}
	
	/**
	 * Returns the direction of this arc.
	 * 
	 * @return the direction of this arc
	 */
	public boolean getDir() {
		return this.dir;
	}
	
	/**
	 * Returns the target of this arc.
	 * 
	 * @return the target of this arc
	 */
	public Term getTarget() {
		return this.target;
	}
	
	/**
	 * Returns <code>true</code> iff this arc
	 * is marked for deletion.
	 * 
	 * @return <code>true</code> iff this arc
	 * is marked for deletion
	 */
	public boolean isMarkedForDeletion() {
		return this.deletion;
	}
	
	/**
	 * Marks this arc for deletion.
	 */
	public void markForDeletion() {
		this.deletion = true;
	}
	
	/**
	 * Returns a string representation of this arc relatively
	 * to the given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of this arc
	 */
	public String toString(Map<Variable,String> variables) {
		return "[cost=" + this.cost + ", dir=" + this.dir +
				", target=" + this.target.toString(variables, false) +
				" @" + Integer.toHexString(this.target.hashCode()) +
				(this.deletion ? ", marked" : ", not marked") +
				"]";
	}
}
