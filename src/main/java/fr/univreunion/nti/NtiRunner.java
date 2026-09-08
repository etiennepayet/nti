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

import java.io.IOException;

import fr.univreunion.nti.parse.ProgramFactory;
import fr.univreunion.nti.program.lp.Lp;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.patternunfolding.TrsPatternUnfolder;

/**
 * Runs NTI from parsed command-line options.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class NtiRunner {

	/**
	 * Runs NTI according to the specified options.
	 *
	 * @param options the options specifying how NTI must run
	 * @throws IOException if an I/O error occurs while running NTI
	 */
	void run(Options options) throws IOException {

		try (Printer printer = new Printer(options.isInVerboseMode())) {
			switch (options.getAction()) {
			case PRINT_HELP:
				printHelp(printer);
				break;
			case PRINT_VERSION:
				printVersion(printer);
				break;
			default:
				if (options.getFileName() == null)
					printer.println("No suitable file to analyze (type 'java -jar nti.jar -h' for help)");
				else
					this.analyze(options, printer);
			}
		}
	}

	/**
	 * Parses and analyzes the program specified by the options.
	 *
	 * @param options the options specifying how NTI must analyze the program
	 * @throws IOException if an I/O error occurs while processing the file
	 */
	void analyze(Options options, Printer printer) throws IOException {

		// We build the program to analyze.
		Program program = ProgramFactory.parse(options.getFileName());

		// Then, we analyze it.
		switch (options.getAction()) {
		case PRINT_PROG:
			printer.println(program);
			break;
		case PRINT_STAT:
			printer.println(program.toStringStat());
			break;
		case PATUNF:
			this.patternUnfold(program, options.getNbIte(), printer);
			break;
		default:
			// By default, we try a termination proof.
			AnalysisContext context = new AnalysisContext(
					options.getVerbosity(),
					options.getPathToCti());
			Proof proof = program.proveTermination(context);
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
							context.getGeneratedRules());
			break;
		}
	}

	/**
	 * Applies the pattern unfolding operator to the provided program.
	 *
	 * @param program the program to unfold
	 * @param nbIterations the number of unfolding iterations
	 * @param printer the printer used to display the result
	 */
	private void patternUnfold(Program program, int nbIterations, Printer printer) {
		if (program instanceof Trs trs)
			TrsPatternUnfolder.printUnfoldings(trs, nbIterations, printer);
		else if (program instanceof Lp)
			printer.println("Printing of pattern unfolding is not implemented yet for logic programs");
	}

	/**
	 * Prints an introductory message about this version of NTI
	 * together with its license.
	 *
	 * @param printer the place where the output goes
	 */
	private void printVersion(Printer printer) {
		printer.println(String.format("NTI %s%n", Nti.VERSION));

		printer.printlnIfVerbose("NTI is free software: you can redistribute it and/or modify");
		printer.printlnIfVerbose("it under the terms of the GNU Lesser General Public License as published by");
		printer.printlnIfVerbose("the Free Software Foundation, either version 3 of the License, or");
		printer.printlnIfVerbose("(at your option) any later version.\n");
		printer.printlnIfVerbose("NTI is distributed in the hope that it will be useful");
		printer.printlnIfVerbose("but WITHOUT ANY WARRANTY; without even the implied warranty of");
		printer.printlnIfVerbose("MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the");
		printer.printlnIfVerbose("GNU Lesser General Public License for more details.\n");
		printer.printlnIfVerbose("You should have received a copy of the GNU Lesser General Public License");
		printer.printlnIfVerbose("along with NTI. If not, see <https://www.gnu.org/licenses/>.\n");
	}

	/**
	 * Prints a help on the usage of NTI.
	 *
	 * @param printer the place where the output goes
	 */
	private void printHelp(Printer printer) {
		printer.println("Usage: java -jar nti.jar <file> [action] [options]\n");
		//
		printer.println("NTI tries to prove (non)termination of the program in the provided file.");
		printer.println("- For logic programs, the implemented techniques are described in");
		printer.println("  [Payet & Mesnard, TOPLAS'06], [Payet, LOPSTR'25] and [Payet, ICLP'25].");
		printer.println("- For TRSs, NTI first tries direct nontermination techniques, including");
		printer.println("  generalized rules, rewrite cycles, structural growth, and regular tree languages.");
		printer.println("  If none succeeds, it uses the dependency pair (DP) framework: it decomposes");
		printer.println("  the initial set of DP problems into subproblems using");
		printer.println("  sound DP processors, then it tries to prove that the unsolved subproblems");
		printer.println("  are infinite using the approaches of [Payet, TCS'08], [Payet, LOPSTR'18],");
		printer.println("  [Payet, LOPSTR'25] and [Payet, ICLP'25] (adapted to TRSs).\n");
		//
		printer.println("'file' has one of the following suffixes:");
		printer.println("   .pl  for a  pure logic program");
		printer.println("   .ari for a  TRS or an SRS in the ARI format");
		printer.println("   .xml for a  TRS or an SRS in the old XML format");
		printer.println("   .trs for a  TRS in the old, human readable, format");
		printer.println("   .srs for an SRS in the old, human readable, format");
		printer.println("NTI supports a subset of the TPDB input formats");
		printer.println("(see https://termination-portal.org/wiki/TPDB and");
		printer.println(" https://termination-portal.org/wiki/Term_Rewriting)");
		printer.println("Restrictions:");
		printer.println("   Rewriting analysis supports only standard, unrestricted rewriting (FULL).");
		printer.println("   INNERMOST, OUTERMOST, LEFTMOST and RIGHTMOST are not supported.");
		printer.println("   Relative, conditional, context-sensitive and equational rewriting are not supported.");
		printer.println("   ARI: (format TRS), then (fun name arity) declarations, then (rule lhs rhs) rules.");
		printer.println("   Left-hand sides must not be variables; rule costs and function theories are not supported.");
		printer.println("   ARI files are always analyzed using FULL rewriting; only use files intended for that strategy.");
		printer.println("   ARI SRSs use unary function symbols.");
		printer.println("   Logic programs must start with exactly one %query: directive (apart from comments");
		printer.println("   and whitespace), followed by clauses and any supported Prolog directives.");
		printer.println("   Use separate files to analyze different query modes.\n");
		//
		printer.println("'action' (optional) can be:");
		printer.println("   -h|--help: print this help");
		printer.println("   --version: print the version of NTI");
		printer.println("   -print: print the program in the given file");
		printer.println("   -stat: print some statistics about the program in the given file");
		printer.println("   -patunf=n: apply the pattern unfolding operator n times");
		printer.println("    to the TRS or SRS in the given file and print the result");
		printer.println("    n must be a non-negative integer (zero prints only the initial pattern rules)");
		printer.println("    Printing pattern unfoldings is not implemented for logic programs (.pl)");
		printer.println("   -prove: run a (non)termination proof of the program in the given file");
		printer.println("    THIS IS THE DEFAULT ACTION\n");
		//
		printer.println("'options' (optional) can be:");
		printer.println("   -v: verbose mode (for printing proof details in the final output)");
		printer.println("   -vv: very verbose mode (also print work retained from every prover thread)");
		printer.println("   -cti=path: set the path to cTI (for proving termination of logic programs)");
		printer.println("    Without cTI, NTI still runs its internal binary and pattern unfolding analyses.");
		printer.println("    Besides searching for nontermination, binary unfolding can also prove termination");
		printer.println("    when an unfolding iteration generates no rules.");
		printer.println("To bound the complete execution time, use an external process supervisor");
		printer.println("such as GNU timeout.");
	}
}
