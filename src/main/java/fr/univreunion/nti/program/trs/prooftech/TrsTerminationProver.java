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

package fr.univreunion.nti.program.trs.prooftech;

import java.util.function.Supplier;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairAnalysis;

/**
 * Runs the default termination analysis for a TRS.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TrsTerminationProver {

	/** The TRS to analyze. */
	private final Trs trs;

	/** Runs the dependency pair phase. */
	private final DependencyPairAnalysisRunner dependencyPairAnalysis;

	/**
	 * Builds a prover for the specified TRS.
	 *
	 * @param trs the TRS to analyze
	 */
	public TrsTerminationProver(Trs trs) {
		this(trs, new DependencyPairAnalysis(trs)::prove);
	}

	/**
	 * Builds a prover whose dependency pair variants are supplied by the
	 * provided runner.
	 *
	 * @param trs the TRS to analyze
	 * @param dependencyPairAnalysis the dependency pair analysis runner
	 */
	TrsTerminationProver(
			Trs trs,
			DependencyPairAnalysisRunner dependencyPairAnalysis) {

		this.trs = trs;
		this.dependencyPairAnalysis = dependencyPairAnalysis;
	}

	/**
	 * Runs a termination proof.
	 *
	 * @param context the context of the analysis
	 * @return the computed proof
	 */
	public Proof prove(AnalysisContext context) {
		Proof proof = new TechGeneralizedRule().run(this.trs, context);

		mergeNextTechnique(proof, context, TechRightSpineLoop::new);
		mergeNextTechnique(proof, context, TechRootVariantCycle::new);
		mergeNextTechnique(proof, context, TechForwardClosureGroundCycle::new);
		mergeNextTechnique(proof, context, TechGroundContextLoop::new);
		mergeNextTechnique(proof, context, TechUnaryCounterGrowth::new);
		mergeNextTechnique(proof, context, TechGuardedUnaryCounterGrowth::new);
		mergeNextTechnique(proof, context, TechGuardedEvaluatorGrowth::new);
		mergeNextTechnique(proof, context, TechOwlRule::new);
		mergeNextTechnique(proof, context, TechListGrowth::new);
		mergeNextTechnique(proof, context, TechUnaryShuttleGrowth::new);
		mergeNextTechnique(proof, context, TechUnarySwapDecrementGrowth::new);
		mergeNextTechnique(proof, context, TechGuardedContextGrowth::new);
		mergeNextTechnique(proof, context, TechSynchronizedArgumentLoop::new);
		mergeNextTechnique(
				proof, context, TechRegularLanguageNonTermination::new);

		if (!proof.isSuccess()) {
			proof.printlnIfVerbose();
			Proof dependencyPairProof = this.dependencyPairAnalysis.run(context, proof);
			if (dependencyPairProof != null)
				proof.merge(dependencyPairProof);
		}

		return proof;
	}

	/**
	 * Runs and merges one technique while the proof remains inconclusive.
	 *
	 * @param proof the proof receiving the technique result
	 * @param context the context of the analysis
	 * @param techniqueSupplier supplies the next proof technique to run
	 */
	private void mergeNextTechnique(
			Proof proof,
			AnalysisContext context,
			Supplier<? extends ProofTechnique> techniqueSupplier) {

		if (!proof.isSuccess())
			proof.merge(techniqueSupplier.get().run(this.trs, context));
	}
}
