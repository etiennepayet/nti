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

package fr.univreunion.nti.program.lp.loop;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.term.Function;

/**
 * An object that witnesses the existence of a loop.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public interface LoopWitness {
	
	/**
	 * Adds the provided binary rule to this witness.
	 * 
	 * @param R a rule to be added to this witness
	 * @return the witness resulting from adding the
	 * provided rule to this witness
	 */
	public LoopWitness add(BinaryRuleLp R);
	
	/**
	 * Checks whether this object is a witness of the
	 * loopingness of the given mode.
	 * 
	 * @param m a mode whose loopingness is to be proved
	 * @return a (non-<code>null</code>) looping atomic
	 * query corresponding to <code>m</code> or
	 * <code>null</code>, if this object is not a witness
	 * of the loopingness of <code>m</code>
	 */
	public Function provesLoopingnessOf(Mode m);
	
	/**
	 * Returns a String representation of the kind
	 * of loopingness witnessed by this object.
	 * 
	 * @return a String representation of the kind
	 * of loopingness witnessed by this object
	 */
	public String getLoopKind();
	
	/**
	 * Returns a short String representation of this witness.
	 * 
	 * @return a short String representation of this witness
	 */
	public String getShortDescription();
}
