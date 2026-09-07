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

package fr.univreunion.nti;

import fr.univreunion.nti.program.Verbosity;

/**
 * A set of options which guide the execution of NTI.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Options {

	/**
	 * The default action to perform.
	 */
	static final NtiAction DEFAULT_ACTION = NtiAction.PROVE_TERM;

	/**
	 * The default verbosity of NTI.
	 */
	static final Verbosity DEFAULT_VERBOSITY = Verbosity.QUIET;

	/**
	 * The default path to cTI.
	 */
	static final String DEFAULT_PATH_TO_CTI = null;

	/**
	 * The default number of iterations of the
	 * pattern unfolding operator.
	 */
	static final int DEFAULT_NB_ITE = 0;


	/**
	 * The name of the file storing the program to analyze.
	 */
	private final String fileName;

	/**
	 * The action that NTI has to perform.
	 */
	private final NtiAction action;

	/**
	 * The verbosity of the execution.
	 */
	private final Verbosity verbosity;

	/**
	 * The path to cTI.
	 */
	private final String pathToCti;

	/**
	 * The number of iterations of the
	 * pattern unfolding operator.
	 */
	private final int nbIte;


	/**
	 * Builds a set of options from the specified command-line arguments.
	 *
	 * @param args a command-line array of strings
	 * @return the options parsed from the command line
	 */
	public static Options parse(String[] args) {
		return new OptionsParser().parse(args);
	}

	/**
	 * Builds a set of options for NTI.
	 *
	 * @param fileName the name of the file storing the program to analyze
	 * @param action the action that NTI has to perform
	 * @param verbosity the verbosity of the execution
	 * @param pathToCti the path to cTI
	 * @param nbIte the number of iterations of the pattern unfolding operator
	 */
	Options(String fileName, NtiAction action, Verbosity verbosity,
			String pathToCti, int nbIte) {
		this.fileName = fileName;
		this.action = action;
		this.verbosity = verbosity;
		this.pathToCti = pathToCti;
		this.nbIte = nbIte;
	}

	/**
	 * Returns the name of the file storing the program to analyze.
	 *
	 * @return the name of the file storing the program to analyze
	 */
	public synchronized String getFileName() {
		return this.fileName;
	}

	/**
	 * Returns the action that NTI has to perform.
	 *
	 * @return the action that NTI has to perform
	 */
	public synchronized NtiAction getAction() {
		return this.action;
	}

	/**
	 * Returns {@code true} if and only if the execution must be
	 * performed in verbose mode.
	 *
	 * @return {@code true} if and only if the execution must be
	 * performed in verbose mode
	 */
	public synchronized boolean isInVerboseMode() {
		return this.verbosity.includesProofDetails();
	}

	/**
	 * Returns the verbosity of the execution.
	 *
	 * @return the verbosity of the execution
	 */
	public synchronized Verbosity getVerbosity() {
		return this.verbosity;
	}

	/**
	 * Returns the path to cTI.
	 *
	 * @return the path to cTI
	 */
	public synchronized String getPathToCti() {
		return this.pathToCti;
	}

	/**
	 * Returns the number of iterations of
	 * the pattern unfolding operator.
	 *
	 * @return the number of iterations
	 * of the pattern unfolding operator
	 */
	public synchronized int getNbIte() {
		return this.nbIte;
	}

}
