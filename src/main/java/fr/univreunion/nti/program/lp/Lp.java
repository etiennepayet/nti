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

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import fr.univreunion.nti.Blackboard;
import fr.univreunion.nti.Options;
import fr.univreunion.nti.Printer;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.lp.argument.ArgumentModeLp;
import fr.univreunion.nti.program.lp.argument.ArgumentLp;
import fr.univreunion.nti.program.lp.nonloop.CorrectPatternRuleLpProducer;
import fr.univreunion.nti.program.lp.nonloop.PatternRuleLp;
import fr.univreunion.nti.program.lp.nonloop.RecurrentPairLp;
import fr.univreunion.nti.program.lp.loop.LoopingPair;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A logic program (LP).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Lp extends Program implements Iterable<RuleLp> {

	/**
	 * The rules of the program.
	 */
	protected final LinkedList<RuleLp> rules = new LinkedList<>();

	/**
	 * The list of modes, the nontermination of which has to
	 * be proved. 
	 */
	protected final LinkedList<Mode> modes = new LinkedList<>();

	/**
	 * An array used for proving non-termination.
	 * For all indices <code>k</code>,
	 * <code>remainingModes[k] == true</code>
	 * iff the <code>k</code>-th mode remains
	 * to be proven non-terminating (i.e., it
	 * has not been proven non-terminating yet).
	 */
	private final boolean[] remainingModes;

	/**
	 * This value is used while proving
	 * non-termination. It is the number
	 * of modes that remain to be proven
	 * non-terminating. 
	 */
	private int nbRemainingModes;

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

		for (RuleLp r : rules)
			if (r != null)
				this.rules.add(r);
			else
				throw new IllegalArgumentException("construction of a LP with a null rule");

		for (Mode m : modes)
			if (m != null)
				this.modes.add(m);
			else
				throw new IllegalArgumentException("construction of a LP with a null mode");

		this.remainingModes = new boolean[this.modes.size()];
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
	 * Implements Prop. 2 of [Payet, ICLP'25].
	 * 
	 * @return a list of pattern rules that are
	 * correct w.r.t. this program
	 */
	public Collection<PatternRuleLp> getCorrectPatternRules() {
		// The list to be returned at the end.
		LinkedList<PatternRuleLp> result = new LinkedList<>();

		// A set that contains the rules of this
		// program that have been successfully
		// used while applying Prop. 2 of
		// [Payet, ICLP'25].
		Set<RuleLp> used = new HashSet<>();

		// We try to construct pattern facts
		// using Prop. 2 of [Payet, ICLP'25].
		for (RuleLp r1 : this.rules)
			if (r1.isFact())
				for (RuleLp r2 : this.rules)
					if (r2.isBinary()) {
						PatternRuleLp r = CorrectPatternRuleLpProducer.getCorrectFact(r1, r2);
						if (r != null) {
							used.add(r1); // r1 has been used
							used.add(r2); // r2 has been used
							result.add(r);
						}
						else {
							r = CorrectPatternRuleLpProducer.getCorrectFact2(r1, r2);
							if (r != null) {
								used.add(r1); // r1 has been used
								used.add(r2); // r2 has been used
								result.add(r);
							}
						}
						for (RuleLp r3 : this.rules)
							if (r3 != r2 && r3.isBinary()) {
								r = CorrectPatternRuleLpProducer.getCorrectFact3(r1, r2, r3);
								if (r != null) {
									used.add(r1); // r1 has been used
									used.add(r2); // r2 has been used
									used.add(r3); // r3 has been used
									result.add(r);
								}
							}
					}

		// Now, we consider all rules of this
		// program that have not been used.
		for (RuleLp r : this.rules)
			if (!used.contains(r))
				if (r.isFact()) {
					// We add h^* to the result, where h is the head of r.
					SimplePatternTerm h = SimplePatternTerm.getInstance(r.getHead());
					result.add(PatternRuleLp.getInstance(h, 0));
				}

				else if (r.isBinary()) {
					PatternRuleLp rr = CorrectPatternRuleLpProducer.getCorrectBinary(r);
					if (rr != null) result.add(rr);
				}

		// System.out.println("x = " + result);
		return result;
	}
	
	/**
	 * Applies the pattern unfolding operator
	 * <code>n</code> times to this program
	 * and displays the result.
	 * 
	 * @param n the number of iterations
	 * of the pattern unfolding operator 
	 * @param printer the printer used
	 * to display the result
	 */
	@Override
	public void patternUnfold(int n, Printer printer) {
		printer.println("Not implemented yet for logic programs!");
	}

	/**
	 * Runs a termination proof for this program.
	 * 
	 * This is a non-parallel version that is used
	 * for testing.
	 * 
	 * @return the computed proof
	 */
	/*
	@Override
	public Proof proveTermination() {
		// All modes remain to be proven non-terminating.
		this.nbRemainingModes = this.modes.size();
		for (int j = 0; j < this.nbRemainingModes; j++)
			this.remainingModes[j] = true;

		ResultLp result = null;
		// result = this.proveNonTerminationWithPatternUnf();
		// result = this.proveNonTerminationWithBinUnf();
		String cTI = Options.getInstance().getPathTo_cTI();
		if (cTI != null)
			result = this.proveTerminationWithCti(cTI);

		return (result == null ? new Proof() : result.getProof());
	}
	*/
	
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

		if (this.modes.isEmpty())
			// No mode is specified in the input file: nothing to do!
			proof.setArgument("The input file does not specify any mode.");
		else {
			// The path to cTI.
			String cTI = Options.getInstance().getPathTo_cTI();

			// The total time limit for all the proofs.
			long seconds = Options.getInstance().getTotalTimeLimit();

			// All modes remain to be proven non-terminating.
			this.nbRemainingModes = this.modes.size();
			for (int j = 0; j < this.nbRemainingModes; j++)
				this.remainingModes[j] = true;

			// The number of threads we are going to start
			// for proving nontermination.
			int nbNonTerm = 2; // binary_unf + pattern_unf
			// The number of threads we are going to start
			// for proving termination + nontermination.
			int nbThreads = (cTI == null ? nbNonTerm : nbNonTerm + 1); 

			ExecutorService executor = Executors.newFixedThreadPool(nbThreads);
			CompletionService<ResultLp> ecs =
					new ExecutorCompletionService<>(executor);

			List<Future<ResultLp>> futures = new ArrayList<>(nbThreads);

			// The termination prover.
			if (cTI != null)
				futures.add(ecs.submit(new Callable<ResultLp>() {
					@Override
					public ResultLp call() throws Exception {
						return proveTerminationWithCti(cTI);
					}
				}));
			// The nontermination provers.
			futures.add(ecs.submit(new Callable<ResultLp>() {
				@Override
				public ResultLp call() throws Exception {
					return proveNonTerminationWithBinUnf();
				}
			}));
			futures.add(ecs.submit(new Callable<ResultLp>() {
				@Override
				public ResultLp call() throws Exception {
					return proveNonTerminationWithPatternUnf();
				}
			}));

			executor.shutdown();

			try {
				for (int i = 0; i < nbThreads; i++) {
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
						// other provers.
						ResultLp r = f.get(); // r is supposed to be non-null
						if (r.isYES() || r.isNO()) {
							// BEWARE: there is a problem if a thread proves 
							// some modes and another thread proves the other
							// modes (then, we get a MAYBE in the end).
							proof.merge(r.getProof());
							break;
						}
						if (r.isERROR())
							// Here, r.getProof() is supposed to be non-null.
							proof.printlnIfVerbose(r.getProof().getArgument());
					} catch (Exception e) {
						// e.printStackTrace();
						proof.printlnIfVerbose(e.getMessage());
					}
				}
			} finally {
				for (Future<ResultLp> f : futures)
					f.cancel(true);
			}
		}

		return proof;
	}

	/**
	 * Runs a nontermination proof for this program.
	 * 
	 * This method runs two threads in parallel. 
	 * One implements the approach of
	 * [Mesnard&Payet, TOPLAS'06] as well as the
	 * recurrent pair approach of [Payet, JAR'24].
	 * The other implements the pattern unfolding
	 * approach of [Payet, ICLP'25].
	 * 
	 * It is supposed that at least one mode is
	 * specified in the input file.
	 * 
	 * @return the <code>Result</code> of this prover
	 */
	/*
	private ResultLp proveNonTermination() {
		// The result that will be returned.
		ResultLp result = null;
		// The proof that will be returned in the result.
		// By default, it is a 'MAYBE' proof. It is shared
		// by all threads performing nontermination proofs.
		Proof proof = new Proof();
		// The argument of the nontermination proof that will
		// be returned. It is shared by all threads performing
		// nontermination proofs.
		ArgumentLp a = new ArgumentLp();

		// The time limit for each nontermination proof.
		long seconds = Options.getInstance().getTimeLimitNonTerm();

		// All modes remain to be proven non-terminating.
		this.nbRemainingModes = this.modes.size();
		for (int j = 0; j < this.nbRemainingModes; j++)
			this.remainingModes[j] = true;

		// The number of threads we are going to start.
		int nbThreads = 2; // 2 = binary_unf + pattern_unf

		ExecutorService executor = Executors.newFixedThreadPool(nbThreads);
		CompletionService<ResultLp> ecs =
				new ExecutorCompletionService<>(executor);

		List<Future<ResultLp>> futures = new ArrayList<>(nbThreads);

		// The nontermination provers.
		futures.add(ecs.submit(new Callable<ResultLp>() {
			@Override
			public ResultLp call() throws Exception {
				return proveNonTerminationWithBinUnf(proof, a);
			}
		}));
		futures.add(ecs.submit(new Callable<ResultLp>() {
			@Override
			public ResultLp call() throws Exception {
				return proveNonTerminationWithPatternUnf(proof, a);
			}
		}));

		executor.shutdown();

		try {
			for (int i = 0; i < nbThreads; i++) {
				try {
					Future<ResultLp> f = ecs.poll(seconds, TimeUnit.SECONDS);
					// If the specified time has elapsed, we stop everything.
					if (f == null) {
						proof.setArgument("Timeout expired!");
						proof.printIfVerbose("* The non-termination provers DON'T KNOW for mode(s): ");
						int k = 0;
						for (Mode m : this.modes)
							if (this.remainingModes[k++]) proof.printIfVerbose(m + " ");
						proof.printlnIfVerbose();
						break;
					}
					// Otherwise, we consider the first success i.e.,
					// the first result corresponding to a proof of
					// termination or nontermination and we cancel all
					// the other provers.
					ResultLp r = f.get(); // r is supposed to be non-null
					if (r.isYES()) {
						// Here, the binary unfolding prover returned a YES.
						result = r;
						break;
					}
					else if (r.isNO()) {
						// Here, one of the nontermination
						// prover returned a NO.
						proof.printIfVerbose("* All specified modes do not terminate: ");
						for (Mode m : this.modes)
							proof.printIfVerbose(m + " ");
						proof.printlnIfVerbose();
						result = r;
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

		// This happens if the specified time has elapsed
		// or all proofs ended in error.
		if (result == null) result = ResultLp.get_MAYBE_Instance(proof);

		return result;
	}
	 */

	/**
	 * Runs a termination proof for this program using cTI.
	 * 
	 * It is supposed that at least one mode is
	 * specified in the input file.
	 * 
	 * @param cTI the path to cTI
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveTerminationWithCti(String cTI) {
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
	 * Runs a nontermination proof for this program
	 * using the binary unfolding operator T^{\beta}_P
	 * of [Codish&Taboch,99].
	 * 
	 * This method implements the approach of
	 * [Mesnard&Payet, TOPLAS'06] as well as the
	 * recurrent pair approach of [Payet, JAR'24].
	 * 
	 * It is supposed that at least one mode is
	 * specified in the input file.
	 * 
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveNonTerminationWithBinUnf() {
		// The proof of the returned result.
		// By default, it is a 'MAYBE' proof.
		Proof proof = new Proof();

		// The loop dictionary which is constructed during the proof.
		// We also use it for storing complete or incomplete
		// recurrent pairs.
		LinkedList<NonTerminationWitness> dict = new LinkedList<>();

		// Some data structures used for unfolding the program
		// using T^{\beta}_P (binary unfolding).
		LinkedList<UnfoldedRuleLp> x = new LinkedList<>();
		LinkedList<UnfoldedRuleLp> unfolded = new LinkedList<>();

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();
		// The blackboard where this program can write data
		// when building the proof.
		Blackboard blackboard = Blackboard.getInstance();

		// The current iteration (we start at 1 because
		// iteration 0 produces nothing).
		int i = 1;
		ArgumentLp a = new ArgumentLp();
		for (; !currentThread.isInterrupted() && 0 < this.nbRemainingModes; i++) {

			proof.printIfVerbose("* [Binary unfolding] Iteration = " + i + ": ");

			// First, we compute the current iteration of
			// the unfolding operator.
			unfolded.clear();
			for (RuleLp r : this.rules) {
				if (currentThread.isInterrupted())
					return ResultLp.get_MAYBE_Instance(proof);

				unfolded.addAll(r.unfold(x, i));
			}
			x.addAll(unfolded);

			int gen = unfolded.size();
			blackboard.incGeneratedRules(gen);
			proof.printIfVerbose(gen + " new unfolded rule(s) generated, ");

			if (gen == 0) {
				// If no binary rule has been generated, then we can
				// safely exit because no more will be produced.
				proof.printIfVerbose("aborting!\n");

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

			// Then, we generate nontermination witnesses
			// from the new unfolded rules.
			LinkedList<NonTerminationWitness> unitLoops = this.unitLoops(unfolded);
			dict.addAll(unitLoops);
			LinkedList<NonTerminationWitness> loopsFromDict = this.loopsFromDict(unfolded, dict);
			dict.addAll(loopsFromDict);

			LinkedList<NonTerminationWitness> loops = new LinkedList<>(unitLoops);
			loops.addAll(loopsFromDict);

			proof.printlnIfVerbose(loops.size() + " new witness(es) generated\n");

			// Then, we use the new witnesses to try proving
			// nontermination of the remaining modes.
			this.checkModes(loops, proof, a);
		}

		// If we get here, then either this.nbRemainingModes <= 0
		// or the current thread is interrupted. 
		// If this.nbRemainingModes <= 0 holds, then we have
		// to check whether the argument of this proof is empty. 
		// Indeed, this.nbRemainingModes <= 0 does not
		// necessarily imply that this proof succeeded (it could
		// be a proof run by another thread that succeeded).
		//
		// BEWARE: there is a problem if a thread proves nontermination
		// of some modes and another thread proves nontermination of the
		// other modes (then, we get a MAYBE in the end).
		if (!a.isEmpty() && this.nbRemainingModes <= 0) {
			proof.setResult(Proof.ProofResult.NO);
			proof.setArgument(a);
			return ResultLp.get_NO_Instance(proof);
		}

		return ResultLp.get_MAYBE_Instance(proof);
	}

	/**
	 * Runs a nontermination proof for this program
	 * using the pattern unfolding operator T^{\pi}_{P,B}
	 * of [Payet, ICLP'25].
	 * 
	 * It is supposed that at least one mode is
	 * specified in the input file.
	 * 
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp proveNonTerminationWithPatternUnf() {
		// The proof of the returned result.
		// By default, it is a 'MAYBE' proof.
		Proof proof = new Proof();

		// A data structure that stores all the unfolded 
		// rules produced by the successive applications
		// of T^{\pi}_{P,B} (pattern unfolding).
		// We initialize it with a collection of correct
		// pattern rules for this program (i.e., the set
		// B in T^{\pi}_{P,B}).
		LinkedList<PatternRuleLp> x = new LinkedList<>(this.getCorrectPatternRules());
		// A data structure that stores all the unfolded 
		// rules produced by an application of
		// T^{\pi}_{P,B} (pattern unfolding).
		LinkedList<PatternRuleLp> unfolded = new LinkedList<>();

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();
		// The blackboard where this program can write data
		// when building the proof.
		Blackboard blackboard = Blackboard.getInstance();

		// The current iteration (we start at 1 because
		// iteration 0 produces nothing).
		int i = 1;
		ArgumentLp a = new ArgumentLp();
		for (; !currentThread.isInterrupted() && 0 < this.nbRemainingModes; i++) {

			proof.printIfVerbose("* [Pattern unfolding] Iteration = " + i + ": ");

			// First, we compute the current iteration of
			// the unfolding operator.
			unfolded.clear();
			for (RuleLp r : this.rules) {
				if (currentThread.isInterrupted())
					return ResultLp.get_MAYBE_Instance(proof);

				unfolded.addAll(r.unfoldPattern(x, i));
				/*
				for (PatternRuleLp pr : unfolded)
					System.out.println(pr);
				 */
			}
			x.addAll(unfolded);

			int gen = unfolded.size(); // the number of generated unfolded rules
			blackboard.incGeneratedRules(gen);
			proof.printlnIfVerbose(gen + " new unfolded rule(s) generated");

			if (gen == 0) {
				// If no unfolded rule has been generated, then we can
				// safely exit because no more will be produced.
				proof.printlnIfVerbose(", aborting!");
				break;
			}
			else proof.printlnIfVerbose();

			// We use the new unfolded rules to try proving
			// nontermination of the remaining modes.
			this.checkModes(unfolded, proof, a);
		}

		// If we get here, then either this.nbRemainingModes <= 0
		// or the current thread is interrupted. 
		// If this.nbRemainingModes <= 0 holds, then we have
		// to check whether the argument of this proof is empty. 
		// Indeed, this.nbRemainingModes <= 0 does not
		// necessarily imply that this proof succeeded (it could
		// be a proof run by another thread that succeeded).
		//
		// BEWARE: there is a problem if a thread proves nontermination
		// of some modes and another thread proves nontermination of the
		// other modes (then, we get a MAYBE in the end).
		if (!a.isEmpty() && this.nbRemainingModes <= 0) {
			proof.setResult(Proof.ProofResult.NO);
			proof.setArgument(a);
			return ResultLp.get_NO_Instance(proof);
		}

		return ResultLp.get_MAYBE_Instance(proof);
	}

	/**
	 * Returns the unit loops contained in the given list
	 * of unfolded rules.
	 * 
	 * @param unfolded a list of rules resulting from
	 * unfolding a logic program
	 * @return a loop dictionary consisting of the unit
	 * loops in <code>unfolded</code>
	 */
	private LinkedList<NonTerminationWitness> unitLoops(LinkedList<UnfoldedRuleLp> unfolded) {
		// The loop dictionary to return at the end.
		LinkedList<NonTerminationWitness> newDict = new LinkedList<>();

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();

		for (UnfoldedRuleLp u : unfolded) {
			if (currentThread.isInterrupted()) break;

			if (u instanceof BinaryRuleLp) {
				BinaryRuleLp r = (BinaryRuleLp) u;

				// We keep r for inferring loops
				// from looping pairs.
				LinkedList<BinaryRuleLp> binseq = new LinkedList<>();
				binseq.add(r);
				SoP tau = new SoP(binseq);
				if (r.isUnitLoop(tau))
					newDict.add(new LoopingPair(binseq, tau));

				// We also keep r for inferring binary chains
				// from recurrent pairs.
				newDict.add(new RecurrentPairLp(r));
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
	private LinkedList<NonTerminationWitness> loopsFromDict(
			LinkedList<UnfoldedRuleLp> unfolded, LinkedList<NonTerminationWitness> dict) {

		// The loop dictionary to return at the end.
		LinkedList<NonTerminationWitness> newDict = new LinkedList<>();

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();

		for (UnfoldedRuleLp u : unfolded) {
			if (currentThread.isInterrupted()) break;

			if (u instanceof BinaryRuleLp) {
				BinaryRuleLp r = (BinaryRuleLp) u;
				for (NonTerminationWitness witness : dict) {
					if (currentThread.isInterrupted()) break;

					NonTerminationWitness witness2 = witness.add(r);
					if (witness2 != witness)
						newDict.add(witness2);
				}
			}
		}

		return newDict;
	}

	/**
	 * Checks which remaining mode is proven nonterminating
	 * by the provided list of nontermination witnesses.
	 * 
	 * This method is synchronized because it is invoked by 
	 * several threads involved in a nontermination proof.
	 * 
	 * @param witnesses a collection of nontermination witnesses
	 * @param proof the nontermination proof in construction
	 * @param a the argument of the nontermination proof in
	 * construction
	 */
	private synchronized void checkModes(
			Collection<? extends NonTerminationWitness> witnesses,
			Proof proof, ArgumentLp a) {

		// The thread running this proof.
		Thread currentThread = Thread.currentThread();

		for (NonTerminationWitness witness : witnesses) {
			if (currentThread.isInterrupted()) break;

			int k = 0; // the index of the considered mode 
			for (Mode m : this.modes) {
				if (currentThread.isInterrupted()) break;

				if (this.remainingModes[k]) {
					// Nontermination of this mode has not been proven yet.
					Function nonterm = witness.provesNonTerminationOf(m);
					if (nonterm != null) {
						a.add(new ArgumentModeLp(m, nonterm, witness));
						proof.printlnIfVerbose("The mode " + m + " is nonterminating. " +
								"The generated witness is:\n  " + witness + "\n");
						this.remainingModes[k] = false;
						this.nbRemainingModes--;
					}
				}
				k++;
			}
		}
	}

	/**
	 * Returns a string representation of this
	 * program relatively to the given set of
	 * variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	public String toString(Map<Variable,String> variables) {
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
			s.append(r.toString(variables));
			s.append("\n");
		}

		// Ending message.
		s.append("** END program: ");
		s.append(this.getName());

		return s.toString();
	}

	/**
	 * Returns a String representation of this program.
	 * 
	 * @return a String representation of this program
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
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
