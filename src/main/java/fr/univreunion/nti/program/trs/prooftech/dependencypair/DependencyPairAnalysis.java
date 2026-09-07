/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.dependencypair.DependencyGraphLimitException;

/**
 * Public facade for the default dependency pair analysis of a TRS.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public final class DependencyPairAnalysis {

	/** The TRS to analyze. */
	private final Trs trs;

	/** Builds the default dependency pair framework variants. */
	private final DependencyPairFrameworkVariantFactory variantFactory;

	/** Runs the framework variants concurrently. */
	private final ConcurrentDependencyPairFrameworkRunner concurrentRunner =
			new ConcurrentDependencyPairFrameworkRunner();

	/**
	 * Builds the default dependency pair analysis for the specified TRS.
	 *
	 * @param trs the TRS to analyze
	 */
	public DependencyPairAnalysis(Trs trs) {
		this(trs, new DefaultDependencyPairFrameworkVariantFactory(
				new DefaultDependencyPairProcessorConfig()));
	}

	/**
	 * Builds a dependency pair analysis using the specified variant factory.
	 *
	 * @param trs the TRS to analyze
	 * @param variantFactory the framework variant factory to use
	 */
	DependencyPairAnalysis(
			Trs trs, DependencyPairFrameworkVariantFactory variantFactory) {

		this.trs = trs;
		this.variantFactory = variantFactory;
	}

	/**
	 * Runs the default dependency pair analysis.
	 *
	 * @param context the context of the analysis
	 * @param diagnosticProof the proof receiving variant wait failures and the
	 * attempt summary when no variant proof is available
	 * @return the first successful framework proof, the latest completed proof,
	 * or {@code null} if none could be collected
	 */
	public Proof prove(AnalysisContext context, Proof diagnosticProof) {
		try {
			// Build the original graph before the concurrent variants start. If it
			// is too dense, there is no reason to allocate the filtered TRS copy.
			this.trs.getDependencyGraph();
		}
		catch (DependencyGraphLimitException failure) {
			diagnosticProof.printlnIfVerbose(
					"* Dependency pair analysis stopped: "
					+ failure.getMessage());
			return null;
		}

		List<DependencyPairFrameworkAttempt> attempts =
				this.variantFactory.buildAttempts(this.trs, context);
		Proof selectedProof = this.concurrentRunner.run(
				attempts,
				diagnosticProof);
		DependencyPairAttemptSummaryFormatter.appendTo(
				selectedProof == null ? diagnosticProof : selectedProof,
				attempts);
		return selectedProof;
	}
}
