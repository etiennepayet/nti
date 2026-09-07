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

package fr.univreunion.nti.program;

/**
 * The context of an NTI analysis.
 * <p>
 * This object gathers the execution parameters that are needed by
 * proof procedures.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class AnalysisContext {

	/**
	 * The verbosity of this analysis.
	 */
	private final Verbosity verbosity;

	/**
	 * The path to cTI.
	 */
	private final String pathToCti;

	/**
	 * The number of generated unfolded rules during this analysis.
	 */
	private int generatedRules = 0;

	/**
	 * Builds an analysis context.
	 *
	 * @param verbose a boolean indicating whether this analysis runs
	 * in verbose mode
	 * @param pathToCti the path to cTI
	 */
	public AnalysisContext(boolean verbose,
						   String pathToCti) {
		this(verbose ? Verbosity.VERBOSE : Verbosity.QUIET,
				pathToCti);
	}

	/**
	 * Builds an analysis context with an explicit verbosity level.
	 *
	 * @param verbosity the verbosity of this analysis
	 * @param pathToCti the path to cTI
	 */
	public AnalysisContext(Verbosity verbosity,
						   String pathToCti) {
		this.verbosity = verbosity;
		this.pathToCti = pathToCti;
	}

	/**
	 * Builds a new proof.
	 *
	 * @return a new proof
	 */
	public Proof createProof() {
		return new Proof(this.verbosity);
	}

	/**
	 * Adds the specified integer to the number of generated
	 * unfolded rules.
	 *
	 * @param n an integer to add to the number of generated
	 * unfolded rules
	 */
	public synchronized void incGeneratedRules(int n) {
		this.generatedRules += n;
	}

	/**
	 * Returns the number of generated unfolded rules.
	 *
	 * @return the number of generated unfolded rules
	 */
	public synchronized int getGeneratedRules() {
		return this.generatedRules;
	}

	/**
	 * Returns the path to cTI.
	 *
	 * @return the path to cTI
	 */
	public String getPathToCti() {
		return this.pathToCti;
	}

	/**
	 * Returns <code>true</code> if and only if the proofs created
	 * by this context are built in verbose mode.
	 *
	 * @return <code>true</code> if and only if the proofs created
	 * by this context are built in verbose mode
	 */
	public boolean isInVerboseMode() {
		return this.verbosity.includesProofDetails();
	}

}
