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

/**
 * The NTI analyzer.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Nti {

	/**
	 * The version of NTI.
	 */
	public static final String VERSION = "(May 2026)";

	/**
	 * The method where everything starts. It processes the user-provided
	 * command-line arguments and runs the analyzer.
	 * 
	 * @param args the user-provided command-line arguments that will be used
	 * for building the options of analysis
	 * @throws IOException if an I/O error occurs while running the analyzer
	 */
	public static void main(String[] args) throws IOException {
		// The options used for running NTI.
		Options options = Options.parse(args);
		new NtiRunner().run(options);
	}
}
