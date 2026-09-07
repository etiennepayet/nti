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
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech.dependencypair.processor;

import java.util.Collection;
import java.util.Deque;
import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.reducpair.ReducPair;

/**
 * A dependency pair processor for proving finiteness of
 * a dependency pair problem, possibly using argument filtering.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class FinitenessDependencyPairProcessor extends DependencyPairProcessor {

	/**
	 * Builds a dependency pair processor for proving finiteness.
	 *
	 * @param usesFiltering <code>true</code> iff
	 * this processor uses argument filtering
	 */
	protected FinitenessDependencyPairProcessor(boolean usesFiltering) {
		super(usesFiltering);
	}

	/**
	 * Runs this processor on the provided dependency pair
	 * problem, possibly using the provided argument filtering.
	 * <p>
	 * The provided argument filtering is used iff this
	 * processor has been built with <code>true</code>
	 * as parameter of the constructor.
	 * <p>
	 * The returned result indicates whether the provided
	 * dependency pair problem could be proved finite or
	 * infinite, or whether it could be decomposed into a
	 * collection of subproblems.
	 *
	 * @param problem a dependency pair problem to solve using this processor
	 * @param filtering an argument filtering for solving
	 * <code>problem</code>
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the created proof
	 * @param context the context of the analysis
	 * @return the result of this processor
	 */
	@Override
	public DependencyPairProcessorResult run(DependencyPairProblem problem,
						ArgFiltering filtering,
						int indentation,
						AnalysisContext context) {

		// The TRS of the problem to solve.
		Trs trs = problem.getTRS();
		// The dependency pairs of the problem to solve.
		DependencyPairs dependencyPairs = problem.getDependencyPairs();

		// First, we run this processor
		// on the full problem only.
		DependencyPairProcessorResult result = this.run(problem, null,
				trs.toPairsOfTerms(), dependencyPairs.toPairsOfTerms(),
				indentation, context);

		// If the problem has been solved or decomposed,
		// then we stop everything. Otherwise, we go on
		// using argument filtering, if they are allowed.
		if (result.isFailed() && this.usesFiltering()) {

			// We build an object for instantiating the filters.
			FilterInstantiator it = new FilterInstantiator(filtering.getAllFilters());

			boolean suitable = this.isSuitable(it);
			if (suitable) {
				// Here, the total number of filter instantiations
				// is not too large. Hence, we go on, i.e., we
				// enumerate the instantiations of the filters
				// and we run this processor with each of them.

				// The thread running this processor.
				Thread currentThread = Thread.currentThread();

				while (!currentThread.isInterrupted() && it.hasNext() && result.isFailed()) {
					// Let us consider the next instantiation of the filters.
					it.next();

					// We apply the current filter to the problem to solve.
					List<PairOfTerms> trsPairs = filtering.applyFilters(trs.iterator());
					List<PairOfTerms> filteredDependencyPairs =
							filtering.applyFilters(dependencyPairs.iterator());

					// Then, we run the processor.
					result = this.run(problem, filtering, trsPairs,
							filteredDependencyPairs, indentation, context);
				}
			}

			if (result.isFailed()) {
				Proof proof = context.createProof();
				if (!suitable)
					proof.printlnIfVerbose(
							"Too many argument filtering possibilities (" +
									it.getNbInstantiationPossibilities() + ")", indentation);

				result = DependencyPairProcessorResult.failed(proof);
			}
		}

		return result;
	}

	/**
	 * Runs this processor on the provided collections
	 * <code>trsPairs</code> and <code>dependencyPairs</code> that result
	 * from applying the provided argument filtering
	 * <code>filtering</code> respectively to the TRS and
	 * to the dependency pairs of the provided dependency pair problem
	 * <code>problem</code>.
	 * <p>
	 * The returned result indicates whether the provided
	 * problem could be proved finite or could be decomposed
	 * into a collection of subproblems.
	 *
	 * @param problem a dependency pair problem to solve using this processor
	 * @param filtering an argument filtering for solving
	 * <code>problem</code> (<code>null</code> if only the
	 * full problem has to be considered)
	 * @param trsPairs the result of applying <code>filtering</code>
	 * to the TRS of <code>problem</code>
	 * @param dependencyPairs the result of applying <code>filtering</code>
	 * to the dependency pairs of <code>problem</code>
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the created proof
	 * @param context the context of the analysis
	 * @return the result of this processor
	 */
	protected abstract DependencyPairProcessorResult run(DependencyPairProblem problem,
									ArgFiltering filtering,
									Collection<PairOfTerms> trsPairs,
									Collection<PairOfTerms> dependencyPairs,
									int indentation,
									AnalysisContext context);

	/**
	 * Returns a result that corresponds to the situation
	 * defined by the specified elements.
	 * <p>
	 * Used during the resolution of the specified dependency pair problem
	 * <code>problem</code>.
	 * <p>
	 * It is supposed that <code>nonStrictRules</code> is a collection
	 * of dependency pairs with <code>nonStrictRules &sube; problem</code>.
	 * Moreover, every element <code>l &rarr; r</code> of
	 * <code>problem</code> (rule or dependency pair) is supposed to
	 * satisfy <code>pi(l) &ge; pi(r)</code> w.r.t. the specified
	 * reduction pair and some argument filtering <code>pi</code>.
	 * Also, every element <code>l &rarr; r</code> of
	 * <code>nonStrictRules</code> is supposed not to satisfy
	 * <code>pi(l) &gt; pi(r)</code>, i.e., is supposed to satisfy
	 * <code>pi(l) = pi(r)</code>.
	 *
	 * @param problem a problem to solve
	 * @param reducPair a reduction pair
	 * @param nonStrictRules some dependency pairs of <code>problem</code>
	 * @param best the best result that has been computed so
	 * far during the resolution of <code>problem</code>
	 * @param proof the proof to build
	 * @param indentation the number of single spaces to print
	 * at the beginning of each line in the specified proof
	 * @return a result that corresponds to the specified
	 * situation
	 */
	protected static DependencyPairProcessorResult getResult(DependencyPairProblem problem,
										ReducPair reducPair,
										Collection<RuleTrs> nonStrictRules,
										DependencyPairProcessorResult best,
										Proof proof,
										int indentation) {

		// The result to return at the end.
		DependencyPairProcessorResult result = best;

		if (nonStrictRules.isEmpty()) {
			// Here, the specified dependency pair problem has been proved finite.
			proof.printlnIfVerbose(reducPair.toString(indentation));
			result = DependencyPairProcessorResult.finite(proof);
		}
		else if (nonStrictRules.size() < problem.getDependencyPairs().size()) {
			// Here, there exist some strict constraints associated with
			// dependency pairs that are satisfied by the current
			// partial solution.
			// We remove the rules corresponding to these constraints.
			// Hence, the new problem to solve consists of:
			// - the dependency pairs whose strict constraints are
			// not satisfied,
			// - the TRS of the specified dependency pair problem.
			// We consider this new problem and apply the 'SCC' processor
			// to it, i.e., we compute the SCCs of the subgraph induced by
			// the rules in 'nonStrictRules'.
			Trs trs = problem.getTRS();
			Deque<DependencyPairs> sccs =
					trs.getDependencyGraph().getSCCs(nonStrictRules);

			if (sccs.isEmpty()) {
				// Here, there is no new problem to solve.
				// Hence, the specified dependency pair problem has been
				// proved finite.
				proof.printlnIfVerbose(reducPair.toString(indentation));
				result = DependencyPairProcessorResult.finite(proof);
			}
			// Here, there are new, smaller, problems to solve.
			else if (compare(best, sccs)) {
				// Here, 'sccs' is better than 'best', hence we
				// return a decomposed result, the subproblems
				// of which are made from the elements of 'sccs'.
				result = DependencyPairProcessorResult.decomposed(proof);
				for (DependencyPairs scc : sccs)
					result.add(new DependencyPairProblem(trs, scc));
			}
		}

		return result;
	}

	/**
	 * Returns <code>true</code> iff the specified
	 * <code>sccs</code> is better than the specified
	 * <code>best</code>.
	 *
	 * @param best a dependency pair processor result
	 * @param sccs a collection of SCCs
	 * @return <code>true</code> iff <code>sccs</code>
	 * is better than <code>best</code>
	 */
	private static boolean compare(DependencyPairProcessorResult best, Deque<DependencyPairs> sccs) {

		if (best == null || !best.isDecomposed()) return true;

		// From here, 'best' is non-null and decomposed.

		int bestSize = best.getSubproblems().size();
		int sccsSize = sccs.size();

		if (sccsSize < bestSize) return true;

		if (sccsSize == bestSize) {
			// We compute the average number of dependency pairs
			// in the elements of 'sccs' and we compare it with
			// the average number of dependency pairs in the
			// dependency pair problems of 'best'.
			int sum = 0;
			for (DependencyPairs scc : sccs) sum += scc.size();
			float avg = ((float) sum) / ((float) sccs.size());

			return avg < best.getSubproblems().averageNbOfDependencyPairs();
		}

		// From here, we have bestSize < sccsSize, hence
		// 'sccs' is not better than 'best'.

		return false;
	}
}
