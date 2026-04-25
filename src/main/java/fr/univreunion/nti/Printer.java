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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti;

import java.io.PrintWriter;

/**
 * A printer for showing the output and error messages of NTI.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Printer {
	/**
	 * The stream for the output.
	 */
	private final PrintWriter out;

	/**
	 * True if and only if this <tt>Printer</tt> runs in verbose mode.
	 */
	private final boolean verbose;

	/**
	 * Builds a <ttPrinter</tt> on <tt>System.out</tt>.
	 * 
	 * @param verbose a boolean indicating whether this
	 * <tt>Printer</tt> runs in verbose mode
	 */
	public Printer(boolean verbose) {
		this.out = new PrintWriter(System.out, true);
		this.verbose = verbose;
	}

	/**
	 * Prints the specified object, whose string representation is
	 * obtained using <tt>String.valueOf(Object)</tt>.
	 * 
	 * @param object an object to be printed
	 */
	public void print(Object object) {
		this.out.print(object);
		this.out.flush();
	}

	/**
	 * Prints the specified object, whose string representation is
	 * obtained using <tt>String.valueOf(Object)</tt>, followed with
	 * a newline character.
	 * 
	 * @param object an object to be printed
	 */
	public void println(Object object) {
		this.out.println(object);
		this.out.flush();
	}

	/**
	 * Prints a newline character.
	 */
	public void println() {
		this.out.println();
		this.out.flush();
	}

	/**
	 * Prints the specified <tt>Throwable</tt> and its backtrace.
	 * 
	 * @param cause a <tt>Throwable</tt>
	 */
	public void printStackTrace(Throwable cause) {
		cause.printStackTrace(this.out);
		this.out.flush();
	}

	/**
	 * If this <tt>Printer</tt> runs in verbose mode, then prints the
	 * specified object, whose string representation is obtained using
	 * <tt>String.valueOf(Object)</tt>. Otherwise, does nothing.
	 * 
	 * @param object an object to be printed
	 */
	public void printIfVerbose(Object object) {
		if (this.verbose) {
			this.out.print(object);
			this.out.flush();
		}
	}

	/**
	 * If this <tt>Printer</tt> runs in verbose mode, then prints the
	 * specified object, whose string representation is obtained using
	 * <tt>String.valueOf(Object)</tt>, followed with a newline character.
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
	 * If this <tt>Printer</tt> runs in verbose mode, then prints a
	 * newline character. Otherwise, does nothing.
	 */
	public void printlnIfVerbose() {
		if (this.verbose) {
			this.out.println();
			this.out.flush();
		}
	}

	/**
	 * If this <tt>Printer</tt> runs in verbose mode, then prints
	 * the specified <tt>Throwable</tt> and its backtrace.
	 * Otherwise, does nothing.
	 * 
	 * @param cause a <tt>Throwable</tt>
	 */
	public void printStackTraceIfVerbose(Throwable cause) {
		if (this.verbose) {
			cause.printStackTrace(this.out);
			this.out.flush();
		}
	}

	/**
	 * Closes this printer and releases any system resources
	 * associated with it.
	 */
	public void close() {
		this.out.close();
	}
}
