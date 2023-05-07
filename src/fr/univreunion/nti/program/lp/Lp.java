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

package fr.univreunion.nti.program.lp;

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import fr.univreunion.nti.Blackboard;
import fr.univreunion.nti.Options;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.lp.argument.ArgumentLoopLp;
import fr.univreunion.nti.program.lp.argument.ArgumentLp;
import fr.univreunion.nti.program.lp.loop.RecurrentPairLp;
import fr.univreunion.nti.program.lp.loop.LoopWitness;
import fr.univreunion.nti.program.lp.loop.LoopingPair;
import fr.univreunion.nti.term.Function;

/**
 * A logic program (LP).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Lp extends Program implements Iterable<RuleLp> {

	/**
	 * The rules of the program.
	 */
	protected final LinkedList<RuleLp> rules = new LinkedList<RuleLp>();

	/**
	 * The list of modes, the nontermination of which has to
	 * be proved. 
	 */
	protected final LinkedList<Mode> modes = new LinkedList<Mode>();

	/**
	 * Builds a logic program (LP).
	 * 
	 * @param name the name of this LP
	 * @param rules the rules of this LP
	 * @param modes the modes whose nontermination has to be proved
	 * @throws IllegalArgumentException if a given rule or mode is <tt>null</tt>
	 */
	public Lp(String name, Collection<RuleLp> rules, Collection<Mode> modes) {

		super(name);

		for (RuleLp R : rules)
			if (R != null)
				this.rules.add(R);
			else
				throw new IllegalArgumentException("construction of a LP with a null rule");

		for (Mode m : modes)
			if (m != null)
				this.modes.add(m);
			else
				throw new IllegalArgumentException("construction of a LP with a null mode");
	}

	/**
	 * Returns the size of this program.
	 * 
	 * @return the size of this program
	 */
	@Override
	public int size() {
		return this.rules.size();
	}

	/**
	 * Returns an iterator over the rules of this program.
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<RuleLp> iterator() {
		return this.rules.iterator();	
	}

	/**
	 * Returns the unit loops contained in the given list of unfolded rules.
	 * 
	 * @param unfolded a list of rules resulting from unfolding
	 * a logic program
	 * @return a loop dictionary consisting of the unit loops 
	 * in <code>unfolded</code>
	 */
	private LinkedList<LoopWitness> unitLoops(LinkedList<UnfoldedRuleLp> unfolded) {
		// The loop dictionary to return at the end.
		LinkedList<LoopWitness> newDict = new LinkedList<LoopWitness>();

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();

		for (UnfoldedRuleLp U : unfolded) {
			if (currentThread.isInterrupted()) break;

			if (U instanceof BinaryRuleLp) {
				BinaryRuleLp R = (BinaryRuleLp) U;

				// We keep R for inferring single loops
				// from looping pairs.
				LinkedList<BinaryRuleLp> binseq = new LinkedList<BinaryRuleLp>();
				binseq.add(R);
				SoP tau = new SoP(binseq);
				if (R.isUnitLoop(tau))
					newDict.add(new LoopingPair(binseq, tau));

				// We also keep R for inferring binary loops
				// from recurrent pairs.
				newDict.add(new RecurrentPairLp(R));
			}
		}

		return newDict;
	}

	/**
	 * This method tries to add each binary unfolded rule
	 * in the given list to the loop witnesses of the given
	 * dictionary. The resulting loop dictionary is returned.
	 * 
	 * @param unfolded a list of rules resulting from unfolding
	 * a logic program
	 * @param dict a loop dictionary
	 * @return a loop dictionary
	 */
	private LinkedList<LoopWitness> loopsFromDict(
			LinkedList<UnfoldedRuleLp> unfolded, LinkedList<LoopWitness> dict) {

		// The loop dictionary to return at the end.
		LinkedList<LoopWitness> newDict = new LinkedList<LoopWitness>();

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();

		for (UnfoldedRuleLp U : unfolded) {
			if (currentThread.isInterrupted()) break;

			if (U instanceof BinaryRuleLp) {
				BinaryRuleLp R = (BinaryRuleLp) U;
				for (LoopWitness L : dict) {
					if (currentThread.isInterrupted()) break;

					LoopWitness LL = L.add(R);
					if (LL != L)
						newDict.add(LL);
				}
			}
		}

		return newDict;
	}

	/**
	 * Runs a termination proof for this program.
	 * 
	 * @return the computed proof
	 */
	@Override
	public Proof proveTermination() {
		// The proof that will be returned.
		// By default, it is a 'MAYBE' proof.
		Proof proof = new Proof();

		if (this.modes.size() == 0)
			// No mode is specified in the input file: nothing to do!
			proof.setArgument("The input file does not specify any mode.");
		else {
			// The path to cTI.
			String cTI = Options.getInstance().getPathTo_cTI();

			// The time limit for nontermination proofs.
			long seconds = Options.getInstance().getTimeLimitNonTerm();

			if (cTI == null) {
				// The Options do not specify a path to cTI.
				// Hence, we only run a nontermination proof
				// in a separate thread.

				ExecutorService executor = Executors.newSingleThreadExecutor();
				Future<ResultLp> future = executor.submit(new Callable<ResultLp>() {
					@Override
					public ResultLp call() throws Exception {
						return proveNonTermination();
					}
				});
				executor.shutdown();

				// We run the proof and wait for at most the
				// time limit for the computation to complete.
				try {
					ResultLp result = future.get(seconds, TimeUnit.SECONDS);
					if (result == null)
						proof.printlnIfVerbose("The nontermination prover returned a null proof.");
					else
						proof.merge(result.getProof());
				} catch (InterruptedException e) {
					proof.printlnIfVerbose(e.getMessage());
				} catch (ExecutionException e) {
					proof.printlnIfVerbose(e.getMessage());
				} catch (TimeoutException e) {
					proof.setArgument("Timeout expired!");
				} finally {
					future.cancel(true);
				}
			}
			else {
				// The Options specify a path to cTI.
				// Hence, we run both a termination
				// and a nontermination proof concurrently.

				ExecutorService executor = Executors.newFixedThreadPool(2);
				CompletionService<ResultLp> ecs =
						new ExecutorCompletionService<ResultLp>(executor);

				List<Future<ResultLp>> futures = new ArrayList<Future<ResultLp>>(2);

				// The termination prover.
				futures.add(ecs.submit(new Callable<ResultLp>() {
					@Override
					public ResultLp call() throws Exception {
						return proveTerminationWith_cTI(cTI);
					}
				}));
				// The nontermination prover.
				futures.add(ecs.submit(new Callable<ResultLp>() {
					@Override
					public ResultLp call() throws Exception {
						return proveNonTermination();
					}
				}));

				executor.shutdown();

				try {
					for (int i = 0; i < 2; i++) {
						try {
							Future<ResultLp> f = ecs.poll(seconds, TimeUnit.SECONDS);
							// If the specified time has elapsed, we stop everything.
							if (f == null) {
								proof.setArgument("Timeout expired!");
								break;
							}
							// Otherwise, we consider the first success i.e.,
							// the first result corresponding to a proof of
							// termination or nontermination and we cancel all
							// the other provers.
							ResultLp r = f.get(); // r is supposed to be non-null
							if (r.isYES() || r.isNO()) {
								proof.merge(r.getProof());
								break;
							}
							else if (r.isERROR())
								// Here, r.getProof() is supposed to be non-null.
								proof.printlnIfVerbose(r.getProof().getArgument());
						} catch (Exception e) {
							proof.printlnIfVerbose(e.getMessage());
						}
					}
				} finally {
					for (Future<ResultLp> f : futures)
						f.cancel(true);
				}
			}
		}

		return proof;
	}


	/**
	 * Runs a termination proof for this program using cTI.
	 * 
	 * It is supposed that at least one mode is
	 * specified in the input file.
	 * 
	 * @param cTI the path to cTI
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveTerminationWith_cTI(String cTI) {
		// The proof of the returned result.
		// By default, it is a 'MAYBE' proof.
		Proof proof = new Proof();

		try {
			// We create a process that runs cTI.
			ProcessBuilder pb = new ProcessBuilder(cTI, this.getName()); //.inheritIO();
			Process proc = pb.start();

			// We create a reader for getting the output
			// of the process.
			BufferedReader reader = new BufferedReader(new InputStreamReader(
					proc.getInputStream())); 

			try {
				// We wait for the end of the process.
				proc.waitFor();
			} catch (InterruptedException e) {
				proof.setArgument("INTERRUPTED!");
				return ResultLp.get_MAYBE_Instance(proof);
			}

			if (reader.ready()) {
				// If the process has provided an output, then
				// consider this output.

				String line = reader.readLine();
				// We check the first line of the output.
				if (line.startsWith("YES")) {
					// The first line is a 'YES': this means
					// that cTI was able to prove termination.
					proof.setResult(Proof.ProofResult.YES);

					StringBuffer argument = new StringBuffer("Proved by cTI");
					while (reader.ready()) {
						line = reader.readLine();
						if (line.startsWith("predicate_term_condition("))
							argument.append(line);
						proof.printlnIfVerbose(line);
					}
					if (0 < argument.length()) proof.setArgument(argument.toString());

					return ResultLp.get_YES_Instance(proof);
				}
				else
					// The first line is not a 'YES': this means
					// that cTI was not able to prove termination.
					return ResultLp.get_MAYBE_Instance(proof);
			}
			else {
				// If the process has not provided an output, then
				// return a 'MAYBE' result.
				proof.setArgument("cTI did not output anything.");
				return ResultLp.get_MAYBE_Instance(proof);
			}
		} catch (Exception e) {
			// Occurs for instance when the specified path
			// to cTI is erroneous.
			proof.setArgument(e.toString());
			return ResultLp.get_ERROR_Instance(proof);
		}
	}

	/**
	 * Runs a nontermination proof for this program.
	 * 
	 * It is supposed that at least one mode is
	 * specified in the input file.
	 * 
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveNonTermination() {
		// The proof of the returned result.
		// By default, it is a 'MAYBE' proof.
		Proof proof = new Proof();

		// The loop dictionary which is constructed during the proof.
		LinkedList<LoopWitness> dict = new LinkedList<LoopWitness>();

		// Some data structures used for unfolding the program.
		LinkedList<UnfoldedRuleLp> X = new LinkedList<UnfoldedRuleLp>();
		LinkedList<UnfoldedRuleLp> unfolded = new LinkedList<UnfoldedRuleLp>();

		// The modes whose nontermination still has to be proved.
		int nbRemainingModes = this.modes.size();
		boolean remainingModes[] = new boolean[nbRemainingModes];
		for (int j = 0; j < nbRemainingModes; j++)
			remainingModes[j] = true;

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();
		// The blackboard where this program can write data
		// when building the proof.
		Blackboard blackboard = Blackboard.getInstance();

		ArgumentLp A = new ArgumentLp();
		int i = 0; // The current iteration.
		for (; !currentThread.isInterrupted() && 0 < nbRemainingModes; i++) {

			proof.printIfVerbose("* Iteration = " + i + ": ");

			if (i == 0) {
				proof.printlnIfVerbose("0 unfolded rule generated, 0 witness generated");
				continue;
			}

			// First, we compute the current iteration of the unfolding operator.
			unfolded.clear();
			for (RuleLp R : this.rules) {
				if (currentThread.isInterrupted())
					return ResultLp.get_MAYBE_Instance(proof);

				unfolded.addAll(R.unfold(X, i));
			}
			X.addAll(unfolded);

			int gen = unfolded.size();
			blackboard.incGeneratedRules(gen);
			proof.printIfVerbose(gen + " new unfolded rule(s) generated, ");

			if (gen == 0) {
				// If the set of unfolded rules is empty, then we can safely
				// exit because no more unfolded rule will be generated during
				// the next iterations.
				proof.printlnIfVerbose("aborting!");

				// Moreover, here we can safely conclude that the
				// program is always terminating.
				proof.setResult(Proof.ProofResult.YES);
				String msg = "From iteration " + i + " of the binary unfolding operator,\n" +
						"no new unfolded rule is generated.\n" +
						"Hence, the program always terminates.\n" +
						"So, all the specified modes are terminating.";
				proof.setArgument(msg);
				return ResultLp.get_YES_Instance(proof);
			}

			// Then, we generate loop witnesses from the newly unfolded rules.
			/*
			LinkedList<LoopWitness> unitLoops = this.unitLoops(unfolded);
			LinkedList<LoopWitness> loops = this.loopsFromDict(unfolded, dict);
			loops.addAll(unitLoops);
			*/

			LinkedList<LoopWitness> unitLoops = this.unitLoops(unfolded);
			dict.addAll(unitLoops);
			LinkedList<LoopWitness> loopsFromDict = this.loopsFromDict(unfolded, dict);
			dict.addAll(loopsFromDict);

			LinkedList<LoopWitness> loops = new LinkedList<LoopWitness>(unitLoops);
			loops.addAll(loopsFromDict);

			proof.printlnIfVerbose(loops.size() + " new witness(es) generated");

			// Then, we use the new witnesses to try proving
			// loopingness of the remaining modes.
			for (LoopWitness L : loops) {
				if (currentThread.isInterrupted()) break;

				int k = 0; // the index of the considered mode 
				for (Mode m : this.modes) {
					if (currentThread.isInterrupted()) break;

					if (remainingModes[k]) {
						// Loopingness of this mode has not been proved yet.
						Function looping = L.provesLoopingnessOf(m);
						if (looping != null) {
							A.add(new ArgumentLoopLp(m, looping, L));
							proof.printlnIfVerbose("The mode " + m + " starts a " + L.getLoopKind() +
									" because of the generated witness:\n  " + L);
							remainingModes[k] = false;
							nbRemainingModes--;
						}
					}
					k++;
				}
			}

			// Finally, we update the dictionary.
			// dict.addAll(loops);
		}

		if (0 < nbRemainingModes) {
			proof.printIfVerbose("* DON'T KNOW for mode(s): ");
			int k = 0;
			for (Mode m : this.modes)
				if (remainingModes[k++]) proof.printIfVerbose(m + " ");
			proof.printlnIfVerbose();
			return ResultLp.get_MAYBE_Instance(proof);
		}
		else {
			proof.printIfVerbose("* All specified modes do not terminate: ");
			for (Mode m : this.modes)
				proof.printIfVerbose(m + " ");
			proof.printlnIfVerbose();
			proof.setResult(Proof.ProofResult.NO);
			proof.setArgument(A);
			return ResultLp.get_NO_Instance(proof);
		}
	}

	/**
	 * Returns a String representation of this program.
	 * 
	 * @return a String representation of this program
	 */
	@Override
	public String toString() {
		// Introductory message.
		StringBuffer s = new StringBuffer("** BEGIN program: ");
		s.append(this.getName());

		// The modes whose nontermination has to be proved.
		int nbModes = this.modes.size();
		s.append("\n* ");
		s.append(nbModes);
		s.append(" mode(s)");
		if (0 < nbModes) s.append(":");
		s.append('\n');
		for (Mode m : this.modes) {
			s.append(m);
			s.append('\n');
		}

		// The rules of the program.
		int nbRules = this.rules.size();
		s.append("* ");
		s.append(nbRules);
		s.append(" rule(s)");
		if (0 < nbRules) s.append(":");
		s.append('\n');
		for (RuleLp r : this.rules) {
			s.append(r);
			s.append("\n");
		}

		// Ending message.
		s.append("** END program: ");
		s.append(this.getName());

		return s.toString();
	}

	/**
	 * Returns a String representation of some statistics
	 * about this program.
	 * 
	 * @return a String representation of some statistics
	 * about this program
	 */
	@Override
	public String toStringStat() {
		// Introductory message.
		StringBuffer s = new StringBuffer("** BEGIN STATS for program: ");
		s.append(this.getName());

		// The number of rules of this program.
		s.append("\n* ");
		s.append(this.rules.size());
		s.append(" rule(s)");

		// Ending message.
		s.append("\n** END STATS for program: ");
		s.append(this.getName());

		return s.toString();
	}
}
