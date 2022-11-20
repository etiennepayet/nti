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

import fr.univreunion.nti.Blackboard;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argument.ArgumentGeneralized;

/**
 * A technique for proving non-termination of term rewrite systems (TRS).
 * It consists in searching for a generalized rule in the TRS i.e.,
 * a rewrite rule whose right-hand side contains a variable that does
 * not occur in the left-hand side.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class TechGeneralizedRule implements ProofTechnique {

	/**
	 * Runs this technique on the specified TRS
	 * and builds a proof.
	 * 
	 * @param IR a TRS whose termination or
	 * non-termination has to be proved
	 * @return the proof that is built by this
	 * technique
	 */
	@Override
	public Proof run(Trs IR) {
		// The proof that will be returned.
		Proof proof = new Proof();

		proof.printlnIfVerbose("## Searching for a generalized rewrite rule");
		proof.printlnIfVerbose("(a rule whose right-hand side contains a variable");
		proof.printlnIfVerbose("that does not occur in the left-hand side)...");

		int i = 1;
		for (RuleTrs R : IR) {
			if (R.isGeneralized()) {
				proof.printlnIfVerbose("Found a generalized rewrite rule!");
				proof.setResult(Proof.ProofResult.NO);
				proof.setArgument(new ArgumentGeneralized(R));
				Blackboard.getInstance().incGeneratedRules(i);
				return proof;
			}
			i++;
		}

		proof.printlnIfVerbose("No generalized rewrite rule found!");
		return proof;
	}
}
