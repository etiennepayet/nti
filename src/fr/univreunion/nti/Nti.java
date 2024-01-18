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

import java.io.IOException;
import java.util.concurrent.ExecutionException;

import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;

/**
 * The NTI analyzer.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Nti {

	/**
	 * The version of NTI.
	 */
	public final static String VERSION = "(November 2023)";

	/**
	 * Constructs an instance of NTI with the specified options.
	 *
	 * @param options the options specifying how NTI must run
	 * @throws IOException if an I/O error occurs while processing
	 * the file
	 */
	public Nti(Options options) throws IOException {

		Printer printer = options.getPrinter();

		// We build the program to analyze.
		Program program = Program.getInstance();

		// Then, we analyze it.
		switch (options.getAction()) {
		case PRINT_PROG:
			printer.println(program);
			break;
		case PRINT_STAT:
			printer.println(program.toStringStat());
			break;
		default:
			// By default, we try a termination proof.
			Proof proof = program.proveTermination();
			// We print a message about the OS name at
			// the end of the proof.
			proof.printlnIfVerbose("Proof run on " + System.getProperty("os.name") +
					" version " + System.getProperty("os.version") +
					" for " + System.getProperty("os.arch"));
			proof.printIfVerbose("using Java version " + System.getProperty("java.version"));
			// We print the result.
			printer.println(proof);
			// We also print the total number of generated rules.
			printer.println(
					"Total number of generated unfolded rules = " +
							Blackboard.getInstance().getGeneratedRules());
			break;
		}

		// We release any system resources associated with the options.
		options.close();
	}

	/**
	 * The method where everything starts. It processes the user-provided
	 * command-line arguments and runs the analyzer.
	 * 
	 * @param args the user-provided command-line arguments that will be used
	 * for building the options of analysis
	 * @throws IOException if an I/O error occurs while running the analyzer
	 */
	public static void main(String args[])
			throws IOException, InterruptedException, ExecutionException {

		// The options used for running NTI.
		Options options = Options.getInstance(args);
		Printer printer = options.getPrinter();

		switch (options.getAction()) {
		case PRINT_HELP:
			printHelp(printer);
			break;
		case PRINT_VERSION:
			welcome(printer);
			break;
		default:
			if (options.getFileName() == null) {
				printer.println("No suitable file to analyze (type \'java -jar nti.jar -h\' for help)");
			}
			else
				// We create a new instance of NTI, which does everything itself.
				new Nti(options);
		}
	}

	/**
	 * Prints an introductory message about this version of NTI
	 * together with its licence.
	 * 
	 * @param printer the place where the output goes
	 */
	private static void welcome(Printer printer) {
		printer.println(String.format("NTI %s%n", VERSION));

		printer.printlnIfVerbose("NTI is free software: you can redistribute it and/or modify");
		printer.printlnIfVerbose("it under the terms of the GNU Lesser General Public License as published by");
		printer.printlnIfVerbose("the Free Software Foundation, either version 3 of the License, or");
		printer.printlnIfVerbose("(at your option) any later version.\n");
		printer.printlnIfVerbose("NTI is distributed in the hope that it will be useful");
		printer.printlnIfVerbose("but WITHOUT ANY WARRANTY; without even the implied warranty of");
		printer.printlnIfVerbose("MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the");
		printer.printlnIfVerbose("GNU Lesser General Public License for more details.\n");
		printer.printlnIfVerbose("You should have received a copy of the GNU Lesser General Public License");
		printer.printlnIfVerbose("along with NTI. If not, see <http://www.gnu.org/licenses/>.\n");
	}

	/**
	 * Prints an help on the usage of NTI.
	 * 
	 * @param printer the place where the output goes
	 */
	private static void printHelp(Printer printer) {
		printer.println("Usage: java -jar nti.jar <file> [action] [options]\n");
		//
		printer.println("This program tries to prove (non)termination of the program in the provided file.");
		printer.println("- For logic programs, the implemented technique is described in [Payet & Mesnard, TOPLAS'06].");
		printer.println("- For TRSs, the implemented technique uses the dependency pair (DP) framework:");
		printer.println("  first, it decomposes the initial set of DP problems into subproblems using");
		printer.println("  sound DP processors, then it tries to prove that the unsolved subproblems");
		printer.println("  are infinite using the approaches of [Payet, TCS'08], [Payet, LOPSTR'18]");
		printer.println("  and [Payet, JAR'24].\n");
		//
		printer.println("file has one of the following suffixes:");
		printer.println("   .pl for a pure logic program");
		printer.println("   .xml for a  TRS or an SRS in XML format");
		printer.println("   .trs for a  TRS in the old, human readable, format");
		printer.println("   .srs for an SRS in the old, human readable, format");
		printer.println("file has to conform to the TPDB syntax specification (see http://termination-portal.org/wiki/TPDB)\n");
		//
		printer.println("action (optional) can be:");
		printer.println("   -h|--help: print this help");
		printer.println("   --version: print the version of NTI");
		printer.println("   -print: print the program in the given file");
		printer.println("   -stat: print some statistics about the program in the given file");
		printer.println("   -prove: run a (non)termination proof of the program in the given file");
		printer.println("    THIS IS THE DEFAULT ACTION\n");
		//
		printer.println("options (optional) can be:");
		printer.println("   -v: verbose mode (for printing proof details in the final output)");
		printer.println("   -t=n: set a time bound on the nontermination proofs");
		printer.println("    n is the time bound in seconds");
		printer.println("   -cTI=path: set the path to cTI (for proving termination of logic programs)");
		printer.println("    if no path to cTI is set then only nontermination proofs are run for");
		printer.println("    logic programs");
	}
}
