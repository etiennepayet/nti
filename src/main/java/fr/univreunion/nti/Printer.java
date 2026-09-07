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

import java.io.PrintWriter;

/**
 * A printer for showing the output and error messages of NTI.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Printer implements AutoCloseable {
	/**
	 * The stream for the output.
	 */
	private final PrintWriter out;

	/**
	 * True if and only if this printer owns its output stream.
	 */
	private final boolean ownsOutput;

	/**
	 * True if and only if this {@code Printer} runs in verbose mode.
	 */
	private final boolean verbose;

	/**
	 * Builds a {@code Printer} on {@code System.out}.
	 * 
	 * @param verbose a boolean indicating whether this
	 * {@code Printer} runs in verbose mode
	 */
	@SuppressWarnings("java:S106") // Standard output is the intended CLI output channel.
	public Printer(boolean verbose) {
		this(new PrintWriter(System.out, true), verbose, false);
	}

	/**
	 * Builds a {@code Printer} on the specified output stream.
	 *
	 * @param out the output stream
	 * @param verbose a boolean indicating whether this
	 * {@code Printer} runs in verbose mode
	 * @param ownsOutput <code>true</code> if and only if this printer
	 * owns the specified output stream
	 */
	Printer(PrintWriter out, boolean verbose, boolean ownsOutput) {
		this.out = out;
		this.verbose = verbose;
		this.ownsOutput = ownsOutput;
	}

	/**
	 * Prints the specified object, whose string representation is
	 * obtained using {@code String.valueOf(Object)}.
	 * 
	 * @param object an object to be printed
	 */
	public void print(Object object) {
		this.out.print(object);
		this.out.flush();
	}

	/**
	 * Prints the specified object, whose string representation is
	 * obtained using {@code String.valueOf(Object)}, followed with
	 * a newline character.
	 * 
	 * @param object an object to be printed
	 */
	public void println(Object object) {
		this.out.println(object);
		this.out.flush();
	}

	/**
	 * If this {@code Printer} runs in verbose mode, then prints the
	 * specified object, whose string representation is obtained using
	 * {@code String.valueOf(Object)}, followed with a newline character.
	 * Otherwise, does nothing.
	 * 
	 * @param object an object to be printed
	 */
	public void printlnIfVerbose(Object object) {
		if (this.verbose) {
			this.out.println(object);
			this.out.flush();
		}
	}

	/**
	 * If this {@code Printer} runs in verbose mode, then prints a
	 * newline character. Otherwise, does nothing.
	 */
	public void printlnIfVerbose() {
		if (this.verbose) {
			this.out.println();
			this.out.flush();
		}
	}

	/**
	 * Closes this printer and releases any system resources
	 * associated with it.
	 */
	@Override
	public void close() {
		if (this.ownsOutput)
			this.out.close();
		else
			this.out.flush();
	}
}
