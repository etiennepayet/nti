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

import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import fr.univreunion.nti.Options;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.DpProbCollection;
import fr.univreunion.nti.program.trs.DpProblem;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.prooftech.dpproc.Processor;
import fr.univreunion.nti.program.trs.prooftech.dpproc.ResultDp;

/**
 * A technique for proving termination and nontermination of term
 * rewrite systems. It is an implementation of the dependency pair
 * framework. It consists in applying some specific dependency pair
 * processors in a specific order.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class TechDpFramework implements ProofTechnique {

	/**
	 * The indentation for introducing and closing
	 * a DP problem.
	 */
	private static final int PROB = 2;
	
	/**
	 * The indentation for introducing and closing
	 * a DP processor.
	 */
	private static final int PROC = 4;
	
	/**
	 * The indentation for displaying elements
	 * about the work of a processor.
	 */
	private static final int PROC_BODY = 6;
	
	
	/**
	 * The processors to apply for proving termination.
	 */
	private final List<Processor> procForTerm = new LinkedList<Processor>();

	/**
	 * The processors to apply for proving nontermination.
	 */
	private final List<Processor> procForNonTerm = new LinkedList<Processor>();

	/**
	 * Builds a termination/nontermination proof technique
	 * which consists in applying the specified DP processors.
	 * 
	 * @param procForTerm the DP processors to apply for
	 * proving termination
	 * @param procForNonTerm the DP processors to apply for
	 * proving nontermination
	 */
	public TechDpFramework(List<Processor> procForTerm,
			List<Processor> procForNonTerm) {

		if (procForTerm != null) this.procForTerm.addAll(procForTerm);
		if (procForNonTerm != null) this.procForNonTerm.addAll(procForNonTerm);
	}

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

		proof.printlnIfVerbose("## Applying the DP framework...");

		// We compute the initial DP problems to solve.
		DpProbCollection initialProblems = IR.getInitialDPProblems();

		if (initialProblems.isEmpty()) {
			// First, we check the SCCs.
			proof.printlnIfVerbose("The TRS under analysis terminates because the set of SCCs");
			proof.printlnIfVerbose("of its estimated dependency graph is empty.");
			proof.setArgument("The set of SCCs of the estimated dependency graph is empty.");
			proof.setResult(Proof.ProofResult.YES);
		}
		else {
			// Then, we try to prove finiteness.
			int n = initialProblems.size();
			proof.printlnIfVerbose("## " + n +
					" initial DP problem" + (n > 1 ? "s" : "") + " to solve.");

			proof.printIfVerbose("## First, we try to decompose ");
			proof.printIfVerbose(n > 1 ? "these problems" : "this problem");
			proof.printlnIfVerbose(" into smaller problems.");

			// We process the DP problems sequentially.
			ResultDp result = this.proveTermination(initialProblems);
			proof.merge(result.getProof());

			// Method 'proveTermination' returns either a 
			// finite or a decomposed result (see below).
			if (result.isFinite()) {
				// Here, all the DP problems were proved finite.
				String msg = "All the DP problems were proved finite.\n" +
						"As all the involved DP processors are sound,\n" +
						"the TRS under analysis terminates.";

				proof.printlnIfVerbose("## " + msg);

				proof.setArgument(msg);
				proof.setResult(Proof.ProofResult.YES);
			}
			else if (result.isDecomposed()){
				// Here, some DP problems could not be proved finite.
				// We try to prove that an unsolved problem is infinite.				
				DpProbCollection dontKnow = result.getSubproblems();

				n = dontKnow.size();
				proof.printlnIfVerbose("## " + (n > 1 ? "Some DP problems" : "A DP problem")
						+ " could not be proved finite.");
				proof.printlnIfVerbose("## Now, we try to prove that " +
						(n > 1 ? "one of these problems" : "this problem") +
						" is infinite.");

				// We process the DP problems concurrently.
				result = this.proveNonTerminationConc(dontKnow);
				proof.merge(result.getProof());

				if (result.isInfinite()) {
					// Here, a DP problem could be proved infinite.
					proof.printlnIfVerbose("This DP problem is infinite.", PROB);
					proof.setResult(Proof.ProofResult.NO);
				}
				else {
					// Here, we have failed: some problems could not be proved
					// finite and none of them could be proved infinite.
					proof.printlnIfVerbose("## Could not solve the following DP problems:");
					int i = 1;
					for (DpProblem prob : dontKnow) proof.printlnIfVerbose((i++) + ": " + prob);
					proof.printlnIfVerbose(
							"Hence, could not prove (non)termination of the TRS under analysis.");
				}
			}
			else
				proof.printlnIfVerbose("## TERMINATION PROVER RETURNED AN UNEXPECTED RESULT!");
		}

		return proof;
	}

	/**
	 * Tries to prove that the DP problems in the specified
	 * collection are finite. The problems are processed
	 * sequentially.
	 * 
	 * Returns either a result indicating finiteness (if all 
	 * of the specified problems could be proved finite) or a
	 * result indicating that some specified problems could
	 * be decomposed into subproblems.
	 * 
	 * BEWARE: the specified collection of problems may be
	 * modified by this method.
	 * 
	 * @param problems a collection of DP problems to be
	 * proved finite
	 * @return the result of the proof
	 */
	private ResultDp proveTermination(DpProbCollection problems) {

		// The thread running this processor.
		Thread currentThread = Thread.currentThread();

		// The collection of subproblems of the returned result.
		DpProbCollection dontKnow = new DpProbCollection();

		// The proof of the returned result.
		Proof proof = new Proof();

		// The collection of smaller problems resulting
		// from applying the processors.
		DpProbCollection newProblems = new DpProbCollection();

		int round = 1;
		while (!problems.isEmpty() && !currentThread.isInterrupted()) {

			int n = problems.size();
			proof.printlnIfVerbose(
					"## Round " + round
					+ " [" + n + " DP problem"
					+ (n > 1 ? "s" : "") + "]:");

			for (DpProblem prob : problems) {

				if (currentThread.isInterrupted()) break;

				// We introduce the problem.
				proof.printlnIfVerbose("## DP problem:", PROB);
				proof.printlnIfVerbose(prob.toString(2));

				// We apply the processors.
				ResultDp result = this.applyTerminationProcessors(prob, proof);

				if (result == null) {
					// Here, all the processors have failed for all the filters.
					proof.printlnIfVerbose("All the DP processors have failed!", PROB);
					proof.printlnIfVerbose("Don't know whether this DP problem is finite.", PROB);
					dontKnow.add(prob);
				}
				else if (result.isFinite()) {
					proof.printlnIfVerbose("Success, finiteness proved!", PROC_BODY);
					proof.printlnIfVerbose("This DP problem is finite.", PROB);
				}
				else if (result.isDecomposed()) {
					newProblems.addAll(result.getSubproblems());
					int m = newProblems.size();
					proof.printlnIfVerbose("Decomposed the DP problem into "
							+ m + " smaller problem" + (1 < m ? "s " : " ") + "to solve!",
							PROC_BODY);
				}
				else	
					throw new IllegalStateException("unexpected result");
			}

			problems.clear();
			problems.addAll(newProblems);
			newProblems.clear();

			round++;
		}

		return (dontKnow.isEmpty() ?
				ResultDp.getFiniteInstance(proof) :
					ResultDp.getDecomposedInstance(proof, dontKnow));
	}

	/**
	 * Applies the DP processors for proving finiteness
	 * to the provided DP problem.
	 * 
	 * If all the processors fail to prove that the
	 * provided DP problem is finite, then returns
	 * <code>null</code>.
	 * 
	 * @param prob a DP problem to solve
	 * @param proof the proof to build
	 * @return the result of applying the processors 
	 * (<code>null</code> if all the processors fail)
	 */
	private ResultDp applyTerminationProcessors(DpProblem prob, Proof proof) {

		// An argument filtering for solving the DP problem.
		ArgFiltering filtering = null;

		for (Processor proc : this.procForTerm) {

			// We introduce the processor.
			proof.printlnIfVerbose(proc.toString(), PROC);

			// We build the argument filtering only if necessary.
			if (proc.usesFiltering() && filtering == null)
				filtering = this.buildFiltering(prob);

			// We run the processor and merge its proof to
			// the proof to build.
			ResultDp result = proc.run(prob, filtering, PROC_BODY);
			proof.merge(result.getProof());

			// Notice that 'result' cannot indicate infiniteness
			// because 'proc' is a processor for proving termination.
			
			if (result.isFinite() || result.isDecomposed())
				return result;
			
			proof.printlnIfVerbose("Failed!", PROC_BODY);
		}

		// Here, all the processors have failed.
		return null;
	}

	/**
	 * Builds the argument filtering corresponding to
	 * the provided DP problem.
	 * 
	 * @param prob a DP problem to solve
	 * @return the argument filtering corresponding to
	 * the provided DP problem
	 */
	private ArgFiltering buildFiltering(DpProblem prob) {

		// The filtering to return at the end.
		ArgFiltering filtering = new ArgFiltering();

		// We build all the filters associated with the
		// symbols of the TRS and we add them to the
		// filtering.
		for (RuleTrs R : prob.getTRS()) {
			R.getLeft().buildFilters(filtering);
			R.getRight().buildFilters(filtering);
		}

		// We build all the filters associated with the
		// symbols of the dependency pairs and we add
		// them to the filtering.
		for (RuleTrs R : prob.getDependencyPairs()) {
			R.getLeft().buildFilters(filtering);
			R.getRight().buildFilters(filtering);
		}

		return filtering;
	}

	/**
	 * Tries to prove that a DP problem in the specified
	 * collection is infinite. The problems are processed
	 * concurrently.
	 * 
	 * @param dontKnow a collection of DP problems
	 * @return the result of the proof
	 */
	private ResultDp proveNonTerminationConc(DpProbCollection dontKnow) {

		// The result to return at the end.
		ResultDp result = null;
		// A proof that will be used to indicate failure.
		Proof proof = null;

		// We create the provers that will be run concurrently.
		// We run each processor on each DP problem. 
		List<Callable<ResultDp>> provers = new LinkedList<Callable<ResultDp>>();
		for (DpProblem prob : dontKnow)
			for (Processor proc : this.procForNonTerm)
				provers.add(new Callable<ResultDp>() {
					@Override
					public ResultDp call() {
						// Each prover works on a copy of
						// the DP problem and a copy of the
						// processor in order to avoid race
						// condition issues. We only build a
						// shallow copy of the problem, because
						// otherwise we would have to compute the
						// estimated dependency graph of the copied
						// TRSs, which may be time consuming.
						return proc.copy().run(prob.shallowCopy(), null, PROC);
					}
				});

		// The number of provers that will be run concurrently.
		int n = provers.size();
		if (0 < n) {
			ExecutorService executor = Executors.newFixedThreadPool(n);
			CompletionService<ResultDp> ecs =
					new ExecutorCompletionService<ResultDp>(executor);

			List<Future<ResultDp>> futures = new LinkedList<Future<ResultDp>>();

			for (Callable<ResultDp> p : provers)
				futures.add(ecs.submit(p));

			executor.shutdown();

			try {
				long seconds = Options.getInstance().getTimeLimitNonTerm();
				for (int i = 0; i < n; i++) {
					try {
						Future<ResultDp> f = ecs.poll(seconds, TimeUnit.SECONDS);
						// If the specified time has elapsed, we stop everything.
						if (f == null) {
							proof = new Proof();
							proof.printlnIfVerbose("\n** INTERRUPTED! **");
							break;
						}
						// Otherwise, we consider the first success i.e.,
						// the first result corresponding to a proof of
						// infiniteness and we cancel all the other provers.
						ResultDp r = f.get();
						if (r != null && r.isInfinite()) {
							result = r;
							break;
						}
					} catch (Exception e) {
						proof = new Proof();
						proof.printlnIfVerbose(e.getMessage());
						break;
					}
				}
			} finally {
				for (Future<ResultDp> f : futures)
					f.cancel(true);
			}
		}

		if (result == null) {
			if (proof == null) {
				proof = new Proof();
				proof.printlnIfVerbose("Failed!", PROB);
			}
			result = ResultDp.getFailedInstance(proof);
		}

		return result;
	}
}
