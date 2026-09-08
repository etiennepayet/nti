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
 * Parses command-line arguments into options for NTI.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class OptionsParser {

	/**
	 * The name of the file storing the program to analyze.
	 */
	private String fileName = null;

	/**
	 * The action that NTI has to perform.
	 */
	private NtiAction action = Options.DEFAULT_ACTION;

	/**
	 * The verbosity of the execution.
	 */
	private Verbosity verbosity = Options.DEFAULT_VERBOSITY;

	/**
	 * The path to cTI.
	 */
	private String pathToCti = Options.DEFAULT_PATH_TO_CTI;

	/**
	 * The number of iterations of the
	 * pattern unfolding operator.
	 */
	private int nbIte = Options.DEFAULT_NB_ITE;

	/**
	 * Builds options for NTI from an array of strings passed
	 * on the command-line.
	 *
	 * @param args the command-line array of strings
	 * @return the options parsed from the command line
	 */
	Options parse(String[] args) {
		for (String arg : args)
			this.parseArgument(arg);

		return new Options(
				this.fileName,
				this.action,
				this.verbosity,
				this.pathToCti,
				this.nbIte);
	}

	/**
	 * Parses a command-line argument.
	 *
	 * @param arg the argument to parse
	 */
	private void parseArgument(String arg) {
		// A well-formed command-line argument has the form
		// -actionOrOption or -actionOrOption=value.
		// Split only at the first '=' to preserve the complete option value.
		String[] parts = arg.split("=", 2);

		// The action or option identifier occurs on the left of '='.
		String actionOption = parts[0];

		// The value, if any, stands on the right of '='.
		String value = (1 < parts.length ? parts[1] : null);

		if (this.parseAction(actionOption, value))
			return;

		if (this.parseOption(actionOption, value))
			return;

		this.parseFileName(arg);
	}

	/**
	 * Parses an action argument.
	 *
	 * @param actionOption the action or option identifier
	 * @param value the value standing on the right of '=', if any
	 * @return <code>true</code> if the argument has been parsed as an action
	 */
	private boolean parseAction(String actionOption, String value) {
		if ("-h".equals(actionOption) || "--help".equals(actionOption)) {
			this.action = NtiAction.PRINT_HELP;
			return true;
		}
		if ("--version".equals(actionOption)) {
			this.action = NtiAction.PRINT_VERSION;
			return true;
		}
		if ("-print".equals(actionOption)) {
			this.action = NtiAction.PRINT_PROG;
			return true;
		}
		if ("-stat".equals(actionOption)) {
			this.action = NtiAction.PRINT_STAT;
			return true;
		}
		if ("-prove".equals(actionOption)) {
			this.action = NtiAction.PROVE_TERM;
			return true;
		}
		if ("-patunf".equals(actionOption)) {
			this.action = NtiAction.PATUNF;
			this.nbIte = parseIterationCount(value);
			return true;
		}

		return false;
	}

	/**
	 * Parses an option argument.
	 *
	 * @param actionOption the action or option identifier
	 * @param value the value standing on the right of '=', if any
	 * @return <code>true</code> if the argument has been parsed as an option
	 */
	private boolean parseOption(String actionOption, String value) {
		if ("-vv".equals(actionOption)) {
			this.verbosity = Verbosity.VERY_VERBOSE;
			return true;
		}
		if ("-v".equals(actionOption)) {
			if (this.verbosity == Verbosity.QUIET)
				this.verbosity = Verbosity.VERBOSE;
			return true;
		}
		if ("-t".equals(actionOption))
			throw new IllegalStateException(
					"option -t has been removed; use an external process supervisor instead");
		if ("-cTI".equals(actionOption))
			throw new IllegalStateException(
					"option -cTI has been renamed to -cti");
		if ("-cti".equals(actionOption)) {
			this.pathToCti = value;
			return true;
		}

		return false;
	}

	/**
	 * Parses a file name argument.
	 *
	 * @param arg the argument to parse
	 */
	private void parseFileName(String arg) {
		if (!arg.startsWith("-") && (arg.endsWith(".pl") ||
				arg.endsWith(".ari") ||
				arg.endsWith(".xml") ||
				arg.endsWith(".trs") ||
				arg.endsWith(".srs")))
			this.fileName = arg;
		else
			throw new IllegalStateException("unrecognized argument: " + arg);
	}

	/**
	 * Parses the non-negative number of pattern-unfolding iterations.
	 *
	 * @param value the string representation of the integer
	 * @return the parsed iteration count
	 */
	private static int parseIterationCount(String value) {
		int count;
		try {
			count = Integer.parseInt(value);
		} catch (NumberFormatException e) {
			throw new IllegalStateException(
					"the specified number of iterations has to be a non-negative integer");
		}
		if (count < 0)
			throw new IllegalStateException(
					"the specified number of iterations has to be a non-negative integer");
		return count;
	}
}
