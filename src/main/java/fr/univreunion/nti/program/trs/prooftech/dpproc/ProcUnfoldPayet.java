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
 * DP problem is infinite using the techniques of Payet
 * (search for loops + recurrent pairs by unfolding).
 * 
 * It consists in searching for a nontermination witness
 * by unfolding the dependency pairs with the TRS of the
 * provided problem.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ProcUnfoldPayet extends Processor {

	/**
	 * The maximum number of generated unfolded rules.
	 * If the number of generated unfolded rules is
	 * greater than this bound, then the proof is
	 * aborted.
	 */
	private static final int NB_UNF = Integer.MAX_VALUE / 2;
	
	/**
	 * The maximum number of iterations of
	 * the unfolding operator.
	 */
	private static final int NB_ITE = Integer.MAX_VALUE / 2;
	
	
	/**
	 * The parameters for running this processor.
	 */
	private final Parameters parameters;

	/**
	 * Builds a processor for searching for loops
	 * and recurrent pairs by unfolding.
	 * 
	 * Argument filterings are not used by this
	 * processor.
	 * 
	 * @param parameters the parameters for running
	 * this processor
	 */
	public ProcUnfoldPayet(Parameters parameters) {
		super(false);
		
		this.parameters = parameters;
	}

	/**
	 * Returns a copy of this processor.
	 * 
	 * @return a copy of this processor
	 */
	@Override
	public Processor copy() {
		// We return a new processor which embeds a copy
		// of the set of parameters of this object.
		return new ProcUnfoldPayet(this.parameters.copy());
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

		// The TRS of the problem to solve.
		Trs IR = prob.getTRS();

		// The maximum depth of a generated unfolded rule.
		Integer generatedMaxDepth = null;

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();

		int originallyFixedMaxDepth = this.parameters.getMaxDepth();
		if (originallyFixedMaxDepth < 0) {
			// If the max depth for the unfolded rules is specified
			// as unlimited, then we incrementally increase the max
			// depth, starting from the depth of IR.
			int m = IR.depth() - 1;
			do {
				m++;
				this.parameters.setMaxDepth(m);
				generatedMaxDepth = this.runWithFixedDepth(prob, proof, indentation + 2);
			}
			while (!currentThread.isInterrupted() &&
					generatedMaxDepth != null && generatedMaxDepth == m);
			// At the end of the analysis, we reset the max depth
			// to its original value.
			this.parameters.setMaxDepth(originallyFixedMaxDepth);
		}
		else
			// Otherwise, we run the analysis with the specified
			// max depth only.
			generatedMaxDepth = this.runWithFixedDepth(prob, proof, indentation + 2);

		return (generatedMaxDepth == null ?
				ResultDp.getInfiniteInstance(proof) :
					ResultDp.getFailedInstance(proof));
	}

	/**
	 * Runs this processor on the provided DP problem
	 * using a fixed maximum depth embedded in the
	 * parameters.
	 * 
	 * If variable unfolding is disabled and nontermination
	 * has not been detected, then also tries with variable
	 * unfolding enabled.
	 * 
	 * Returns either <code>null</code> (meaning that this
	 * processor succeeded in proving that the provided
	 * problem is infinite) or the maximum depth of an
	 * unfolded rule generated by this processor (meaning
	 * that this processor did not succeed in proving
	 * infiniteness).
	 * 
	 * @param prob a DP problem to solve using this processor
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return <code>null</code> or the maximum depth of an
	 * unfolded rule generated by this processor
	 */
	private Integer runWithFixedDepth(DpProblem prob,
			Proof proof, int indentation) {

		// The value to return at the end.
		Integer generatedMaxDepth = null;

		// We try to prove nontermination by unfolding the
		// dependency pairs of the specified problem.
		generatedMaxDepth = this.runWithFixedDepthAndVar(prob, proof, indentation);

		// If nontermination was not detected and variable
		// unfolding was OFF, then we try with variable
		// unfolding on.
		if (!Thread.currentThread().isInterrupted() &&
				generatedMaxDepth != null &&
				!this.parameters.isVariableUnfoldingEnabled()) {

			this.parameters.setVariableUnfolding(true);
			generatedMaxDepth = this.runWithFixedDepthAndVar(prob, proof, indentation);
			// At the end of the analysis, we reset the 'variable unfolding'
			// flag to its initial value.
			this.parameters.setVariableUnfolding(false);
		}

		return generatedMaxDepth;
	}

	/**
	 * Runs this processor on the provided DP problem using
	 * a fixed maximum depth and a fixed variable unfolding
	 * behavior, both embedded in the parameters.
	 * 
	 * Returns either <code>null</code> (meaning that this
	 * processor succeeded in proving that the provided
	 * problem is infinite) or the maximum depth of an
	 * unfolded rule generated by this processor (meaning
	 * that this processor did not succeed in proving
	 * infiniteness).
	 * 
	 * @param prob a DP problem to solve using this processor
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return <code>null</code> or the maximum depth of an
	 * unfolded rule generated by this processor
	 */
	private Integer runWithFixedDepthAndVar(DpProblem prob,
			Proof proof, int indentation) {

		// The TRS of the problem to solve.
		Trs IR = prob.getTRS();
		IR.initForUnfolding(); // We initialize IR before unfolding it.

		proof.printlnIfVerbose("# max_depth=" + this.parameters.getMaxDepth() +
				", unfold_variables=" + this.parameters.isVariableUnfoldingEnabled() +
				":",
				indentation);
		// From now, we need to print 2 more single spaces
		// at the beginning of each line of the proof.
		indentation += 2;

		// The maximum depth of an unfolded rule generated by this
		// processor. This is the value that is returned at the end
		// if this processor fails to prove infiniteness.
		Integer generatedMaxDepth = -1;

		// Some data structures used for unfolding.
		LinkedList<UnfoldedRuleTrs> X = new LinkedList<>();
		LinkedList<UnfoldedRuleTrs> unfolded = new LinkedList<>();

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
				// syntactic loops occurring in the provided problem.
				// We also check whether a syntactic loop is a
				// nontermination witness.
				for (UnfoldedRuleTrs R : IR.getSyntacticLoops(prob.getDependencyPairs())) {
					if (currentThread.isInterrupted()) break;

					Collection<? extends UnfoldedRuleTrs> U_R =
							R.elimAndProve(this.parameters, IR, proof);
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
					Collection<? extends UnfoldedRuleTrs> U_R =
							R.unfold(this.parameters, IR, i, proof);
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
				// Here, we have found a loop or a recurrent pair.
				proof.printlnIfVerbose("success, " + proof.getArgument().getWitnessKind()
						+ " found, " + msgNbGenerated);
				proof.printlnIfVerbose(proof.getArgument().getDetails(indentation));
				return null;
			}

			// Here, we have not found anything.
			proof.printlnIfVerbose("infiniteness not proved, " + msgNbGenerated);

			// We update the maximum depth of a generated rule.
			generatedMaxDepth = getMaxDepth(unfolded, generatedMaxDepth);

			i++;

			if (stopIte = (NB_ITE < i))
				proof.printlnIfVerbose(
						"Too many iterations of the unfolding operator! Aborting!", indentation);
			else if (stopUnf)
				proof.printlnIfVerbose("Too many unfolded rules! Aborting!", indentation);
		}

		// Here, nontermination could not be proved.
		proof.printlnIfVerbose("Could not prove infiniteness!", indentation);

		return generatedMaxDepth;
	}

	/**
	 * Computes the maximum depth of a rule in
	 * the specified collection. Returns the
	 * max between this value and the provided
	 * <code>maxDepth</code>.
	 * 
	 * @param unfolded a collection a rules whose
	 * maximum depth is to be computed
	 * @param maxDepth a value to be compared to
	 * the maximum depth of a rule in the specified
	 * collection
	 * @return the max between the maximum depth
	 * and the provided <code>maxDepth</code>
	 */
	private static int getMaxDepth(Collection<UnfoldedRuleTrs> unfolded, int maxDepth) {
		for (UnfoldedRuleTrs U : unfolded) {
			int m = U.depth();
			if (maxDepth < m) maxDepth = m;
		}

		return maxDepth;
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
		return
				"## DP Processor: [Payet, LOPSTR'18 + JAR'24 + LOPSTR'25] (" +
				this.parameters + "). ";
	}
}
