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

package fr.univreunion.nti;

/**
 * A set of options which guide the execution of NTI.
 * 
 * This class implements the singleton design pattern:
 * only one instance of it can be created.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Options {

	/**
	 * The unique instance of this class.
	 */
	private static Options UNIQUE_INSTANCE;
	
	/**
	 * The default action to perform.
	 */
	private final static NtiAction DEFAULT_ACTION = NtiAction.PROVE_TERM;

	/**
	 * The default verbosity of NTI.
	 */
	private final static boolean DEFAULT_VERBOSITY = false;

	/**
	 * The default time limit for the whole analysis,
	 * in seconds.
	 */
	private final static long DEFAULT_TOTAL_TIME_LIMIT = 86400L; // 24 hours
	
	/**
	 * The default time limit for the nontermination proofs,
	 * in seconds.
	 */
	private final static long DEFAULT_TIME_LIMIT_NONTERM = 86400L; // 24 hours
	
	/**
	 * The default path to cTI.
	 */
	private final static String DEFAULT_PATH_TO_cTI = null;
		
	
	/**
	 * The printer used for showing the output and error messages of NTI.
	 */
	private final Printer printer;

	/**
	 * The name of the file storing the program to analyze.
	 */
	private final String fileName;

	/**
	 * The action that NTI has to perform.
	 */
	private final NtiAction action;

	/**
	 * True if and only if the execution must be performed in verbose mode.
	 */
	private final boolean verbose;

	/**
	 * The total time limit for the whole analysis,
	 * in seconds.
	 */
	private final long totalTimeLimit;
	
	/**
	 * The time limit for the nontermination proofs,
	 * in seconds.
	 */
	private final long timeLimitNonTerm;
	
	/**
	 * The path to cTI.
	 */
	private final String pathTo_cTI;
		
	
	/**
	 * Returns the unique instance of this class.
	 * 
	 * If the instance does not exist yet, creates
	 * it from the provided array of strings passed
	 * on the command-line.
	 * 
	 * @param args a command-line array of strings
	 * @return the unique instance of this class
	 */
	public static synchronized Options getInstance(String[] args) {
		if (UNIQUE_INSTANCE == null)
			UNIQUE_INSTANCE = new Options(args);
		
		return UNIQUE_INSTANCE;
	}
	
	/**
	 * Returns the unique instance of this class.
	 * 
	 * If the instance does not exist yet, then
	 * returns <code>null</code>.
	 * 
	 * @return the unique instance of this class,
	 * or <code>null</code>
	 */
	public static synchronized Options getInstance() {
		return UNIQUE_INSTANCE;
	}
	
	/**
	 * Builds a set of options for NTI from an array of strings
	 * passed on the command-line.
	 * 
	 * @param args the command-line array of strings
	 * @throws IllegalStateException if an option passed on the
	 * command-line is unrecognized or if no option is provided
	 * at all (the name of the file to analyze must at least be
	 * provided)
	 */
	private Options(String[] args) {
		String fileName = null;
		NtiAction action = DEFAULT_ACTION;
		boolean verbose = DEFAULT_VERBOSITY;
		long totalTimeLimit = DEFAULT_TOTAL_TIME_LIMIT;
		long timeLimitNonTerm = DEFAULT_TIME_LIMIT_NONTERM;
		String pathTo_cTI = DEFAULT_PATH_TO_cTI;

		for (String arg : args) {
			// A well-formed command-line argument has the form
			// -actionOrOption or -actionOrOption=value.
			// First, we split the given argument around matches of '='.
			String[] S = arg.split("=");

			// The action or option identifier occurs on the left of '='.
			String actionOption = S[0];

			// The value, if any, stands on the right of '='.
			String value = (1 < S.length ? S[1] : null);

			// Action:
			if ("-h".equals(actionOption) || "--help".equals(actionOption)) action = NtiAction.PRINT_HELP;
			else if ("--version".equals(actionOption)) action = NtiAction.PRINT_VERSION;
			else if ("-print".equals(actionOption)) action = NtiAction.PRINT_PROG;
			else if ("-stat".equals(actionOption)) action = NtiAction.PRINT_STAT;
			else if ("-prove".equals(actionOption)) action = NtiAction.PROVE_TERM;
			// Options:
			else if ("-v".equals(actionOption)) verbose = true;
			else if ("-t".equals(actionOption))
				try {
					// We get the time in seconds.
					timeLimitNonTerm =  Long.parseLong(value);
				} catch (NumberFormatException e) {
					throw new IllegalStateException("the specified time limit has to be an integer");
				}
			else if ("-cTI".equals(actionOption)) pathTo_cTI = value;
			// File:
			else if (arg.endsWith(".pl") || arg.endsWith(".xml"))
				fileName = arg;
		}

		this.fileName = fileName;
		this.action = action;
		this.verbose = verbose;
		this.totalTimeLimit = totalTimeLimit;
		this.timeLimitNonTerm = timeLimitNonTerm;
		this.pathTo_cTI = pathTo_cTI;

		// We create a printer for showing the output and error messages of NTI.
		this.printer = new Printer(verbose);		
	}

	/**
	 * Returns the printer used for showing the output and
	 * error messages of NTI.
	 * 
	 * @return the printer used for showing the output and
	 * error messages of NTI
	 */
	public synchronized Printer getPrinter() {
		return this.printer;
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
	 * Returns <tt>true</tt> if and only if the execution must be
	 * performed in verbose mode.
	 * 
	 * @return <tt>true</tt> if and only if the execution must be
	 * performed in verbose mode
	 */
	public synchronized boolean isInVerboseMode() {
		return this.verbose;
	}

	/**
	 * Returns the total time limit for the whole
	 * analysis, in seconds.
	 * 
	 * @return the total time limit for the whole
	 * analysis
	 */
	public synchronized long getTotalTimeLimit() {
		return this.totalTimeLimit;
	}
	
	/**
	 * Returns the time limit for the nontermination
	 * proofs, in seconds.
	 * 
	 * @return the time limit for the nontermination
	 * proofs
	 */
	public synchronized long getTimeLimitNonTerm() {
		return this.timeLimitNonTerm;
	}
	
	/**
	 * Returns the path to cTI.
	 * 
	 * @return the path to cTI
	 */
	public synchronized String getPathTo_cTI() {
		return this.pathTo_cTI;
	}
		
	/**
	 * Releases any system resources associated with
	 * this set of options.
	 */
	public synchronized void close() {
		this.printer.close();
	}
}
