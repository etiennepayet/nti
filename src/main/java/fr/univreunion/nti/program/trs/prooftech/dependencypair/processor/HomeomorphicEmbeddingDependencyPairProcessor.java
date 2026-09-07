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


import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.FilterInstantiator;
import fr.univreunion.nti.term.Term;

/**
 * A sound dependency pair processor for proving that
 * a provided DP problem is finite using homeomorphic
 * embeddings.
 *
 * <p>The homeomorphic embedding relation is presented in F. Baader and
 * T. Nipkow, <a href="https://doi.org/10.1017/CBO9781139172752"><i>Term
 * Rewriting and All That</i></a>, Cambridge University Press, 1998,
 * Sect. 5.4.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class HomeomorphicEmbeddingDependencyPairProcessor extends DependencyPairProcessor {

	/**
	 * Builds a dependency pair processor for proving
	 * finiteness of DP problems using homeomorphic
	 * embeddings.
	 * <p>
	 * Argument filterings are not used by this
	 * processor.
	 */
	public HomeomorphicEmbeddingDependencyPairProcessor() {
		super(false);
	}

	/**
	 * Runs this processor on the provided DP problem
	 * without using the provided argument filtering.
	 * <p>
	 * The returned result indicates whether the provided
	 * DP problem could be proved finite or infinite or
	 * whether it could be decomposed into a collection
	 * of subproblems.
	 *
	 * @param problem a DP problem to solve using this processor
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

		// The proof of the returned result.
		Proof proof = context.createProof();

		// We indicate which argument filtering is used.
		this.printFiltering(filtering, proof, indentation);

		// We check whether the set of dependency pairs of 'problem'
		// only consists of pairs l -> r where l embeds r.
		for (RuleTrs rule : problem.getDependencyPairs()) {
			Term left = rule.getLeft();
			Term right = rule.getRight();
			if (left.deepEquals(right) || !left.embeds(right))
				return DependencyPairProcessorResult.failed(proof);
		}

		// Here, every dependency pair has the form l -> r
		// where l embeds r.
		return DependencyPairProcessorResult.finite(proof);
	}

	/**
	 * Checks whether the provided filter instantiator
	 * is suitable for this processor.
	 * <p>
	 * For internal use only.
	 * <p>
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
		return "## DP Processor: homeomorphic embeddings. ";
	}
}
