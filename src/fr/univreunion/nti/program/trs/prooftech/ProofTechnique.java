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

package fr.univreunion.nti.program.trs.prooftech;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;

/**
 * A technique for proving termination or non-termination of
 * term rewrite systems.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public interface ProofTechnique {

	/**
	 * Runs this technique on the specified TRS
	 * and builds a proof.
	 * 
	 * @param IR a TRS whose termination or
	 * non-termination has to be proved
	 * @return the proof that is built by this
	 * technique
	 */
	public Proof run(Trs IR);
}
