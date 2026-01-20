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

import fr.univreunion.nti.term.Function;

/**
 * An object that witnesses the existence
 * of an infinite derivation.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public interface NonTerminationWitness {
	
	/**
	 * Adds the provided binary rule to this witness.
	 * 
	 * @param R a rule to be added to this witness
	 * @return the witness resulting from adding the
	 * provided rule to this witness
	 */
	public NonTerminationWitness add(BinaryRuleLp R);
	
	/**
	 * Checks whether this object is a nontermination
	 * witness of the given mode.
	 * 
	 * @param m a mode whose nontermination is to be proved
	 * @return a (non-<code>null</code>) nonterminating
	 * atomic query corresponding to <code>m</code> or
	 * <code>null</code>, if this object is not a 
	 * nontermination witness of <code>m</code>
	 */
	public Function provesNonTerminationOf(Mode m);
		
	/**
	 * Returns a short String representation of this witness.
	 * 
	 * @return a short String representation of this witness
	 */
	public String getShortDescription();
}
