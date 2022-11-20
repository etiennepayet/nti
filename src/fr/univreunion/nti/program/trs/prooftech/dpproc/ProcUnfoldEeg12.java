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

package fr.univreunion.nti.program.trs.prooftech.dpproc;

import java.util.Collection;
import java.util.LinkedList;

import fr.univreunion.nti.Blackboard;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.DpProblem;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;

/**
 * A complete DP processor for proving that a provided
 * DP problem is infinite using the technique presented
 * in [Emmes, Enger, Giesl, IJCAR'12].
 * 
 * It consists in searching for a nontermination witness
 * by unfolding the dependency pairs with the TRS of the
 * provided problem.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ProcUnfoldEeg12 extends Processor {

	/**
	 * The maximum number of generated unfolded rules.
	 * If the number of generated unfolded rules is
	 * greater than this bound, then the proof is
	 * aborted.
	 */
	private final static int NB_UNF = 200;
	
	/**
	 * The maximum number of iterations of
	 * the unfolding operator.
	 */
	private final static int NB_ITE = Integer.MAX_VALUE / 2;
	
	
	/**
	 * The parameters for running this processor.
	 */
	private final Parameters parameters;
	
	/**
	 * Builds a DP processor for proving infiniteness
	 * of DP problems using the technique presented
	 * in [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * Argument filterings are not used by this
	 * processor.
	 * 
	 * @param parameters the parameters for running
	 * this processor
	 */
	public ProcUnfoldEeg12(Parameters parameters) {
		super(false);
		
		this.parameters = parameters;
	}

	/**
	 * Runs this processor on the provided DP problem,
	 * without using the provided argument filtering.
	 * 
	 * The returned result indicates whether the provided
	 * DP problem could be proved infinite.
	 * 
	 * @param prob a DP problem to solve using this processor
	 * @param filtering an argument filtering for solving
	 * <code>prob</code>
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return the <code>Result</code> of this processor
	 */
	@Override
	public ResultDp run(DpProblem prob,
			ArgFiltering filtering, int indentation) {
		
		// The proof of the returned result.
		Proof proof = new Proof();

		// Let us introduce ourselves.
		proof.printlnIfVerbose(this.toString(), indentation);

		// From now, we need to print 2 more single spaces
		// at the beginning of each line of the proof.
		indentation += 2;

		// The TRS of the problem to solve.
		Trs IR = prob.getTRS();
		IR.initForUnfoldingNL(); // We initialize IR before unfolding it.

		// Some data structures used for unfolding.
		LinkedList<UnfoldedRuleTrs> X = new LinkedList<UnfoldedRuleTrs>();
		LinkedList<UnfoldedRuleTrs> unfolded = new LinkedList<UnfoldedRuleTrs>();

		// We track the number of iterations of the unfolding operator.
		int i = 0; // The current number of iterations.
		boolean stopIte = (NB_ITE < i); // Do we stop the proof because of the number of iterations?

		// We also track the number of generated unfolded rules.
		int generated = 0 ; // The current number of generated unfolded rules.
		boolean stopUnf = (NB_UNF < generated); // Do we stop the proof because of the number of unfolded rules?

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();
		// The blackboard where this processor can write data
		// when building the proof.
		Blackboard blackboard = Blackboard.getInstance();

		// The main loop of the processor.
		while (!currentThread.isInterrupted() &&
				!stopIte && !stopUnf && (i == 0 || !unfolded.isEmpty())) {

			proof.printIfVerbose("# Iteration " + i + ": ", indentation);

			if (i == 0)
				// At the first iteration, we have to initialize the
				// set of unfolded rules: we initialize it to the
				// pattern rules occurring in the provided problem.
				// We also check whether a pattern rule is a
				// nontermination witness.
				for (UnfoldedRuleTrs R : IR.getPatternRules(prob.getDependencyPairs().iterator())) {
					if (currentThread.isInterrupted()) break;

					Collection<? extends UnfoldedRuleTrs> U_R = R.elimAndProve(this.parameters, IR, proof);
					int g = U_R.size();
					generated += g;
					blackboard.incGeneratedRules(g);
					unfolded.addAll(U_R);
					if (proof.isSuccess() || (stopUnf = (NB_UNF < generated))) break;
				}
			else {
				X.clear();
				X.addAll(unfolded);
				unfolded.clear();
				for (UnfoldedRuleTrs R : X) {
					if (currentThread.isInterrupted()) break;

					// We unfold R and check whether nontermination
					// can be proved from the new unfolded rules.
					Collection<? extends UnfoldedRuleTrs> U_R = R.unfold(this.parameters, IR, i, proof);
					int g = U_R.size();
					generated += g;
					blackboard.incGeneratedRules(g);
					unfolded.addAll(U_R);
					if (proof.isSuccess() || (stopUnf = (NB_UNF < generated))) break;
				}
			}

			// We build a small message indicating the
			// number of unfolded rules generated during
			// this iteration.
			int unfSize = unfolded.size();
			String msgNbGenerated =
					unfSize + " unfolded " +
							(1 < unfSize ? "rules" : "rule") +
							" generated.";

			if (proof.isSuccess()) {
				proof.printlnIfVerbose("success, nontermination proved, " + msgNbGenerated);
				proof.printlnIfVerbose(proof.getArgument().getDetails(indentation));
				return ResultDp.getInfiniteInstance(proof);
			}

			proof.printlnIfVerbose("nontermination not proved, " + msgNbGenerated);

			i++;

			if (stopIte = (NB_ITE < i))
				proof.printlnIfVerbose(
						"Too many iterations of the unfolding operator! Aborting!", indentation);
			else if (stopUnf)
				proof.printlnIfVerbose("Too many unfolded rules! Aborting!", indentation);
		}

		// Here, nontermination could not be proved.
		proof.printlnIfVerbose("Could not prove nontermination!", indentation);
		return ResultDp.getFailedInstance(proof);
	}
	
	/**
	 * Checks whether the provided filter instantiator
	 * is suitable for this processor.
	 * 
	 * For internal use only.
	 * 
	 * Always returns <code>false</code> as this processor
	 * does not use argument filterings.
	 * 
	 * @param it a filter instantiator
	 * @return always <code>false</code>
	 */
	@Override
	protected boolean isSuitable(FilterInstantiator it) {
		return false;
	}

	/**
	 * Returns a String representation of this object.
	 */
	@Override
	public String toString() {
		return "## DP Processor: the technique of [Emmes, Enger, Giesl, IJCAR'12] + unfolding (" +
				this.parameters + "). ";
	}
}
