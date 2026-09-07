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
 * An object of this class is returned by a termination prover.
 * It embeds a result (<code>YES</code>, <code>NO</code>,
 * <code>MAYBE</code>), an argument and, optionally (if
 * verbose mode is on), a content which consists of a detailed
 * history of the proof construction.
 * <p>
 * The default result of an object of this class is <code>MAYBE</code>.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Proof {

	/**
	 * A value indicating whether termination or
	 * non-termination could be proved.
	 *
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	public enum ProofResult {
		YES, // Termination could be proved
		NO,  // Nontermination could be proved
		MAYBE // Neither termination nor nontermination could be proved
	}

	/**
	 * The result of this <code>Proof</code>.
	 */
	private ProofResult result = ProofResult.MAYBE;

	/**
	 * The argument of this <code>Proof</code>.
	 * <p>
	 * If <code>null</code>, then the proof has not succeeded
	 * (corresponds to a MAYBE answer).
	 */
	private Argument argument;

	/**
	 * The detailed content of this <code>Proof</code>.
	 */
	private final StringBuffer content = new StringBuffer();

	/**
	 * The verbosity used to build this proof.
	 */
	private final Verbosity verbosity;

	/**
	 * Builds a proof in the specified verbosity mode.
	 *
	 * @param verbose a boolean indicating whether this proof is built
	 * in verbose mode
	 */
	public Proof(boolean verbose) {
		this(verbose ? Verbosity.VERBOSE : Verbosity.QUIET);
	}

	/**
	 * Builds a proof at the specified verbosity level.
	 *
	 * @param verbosity the verbosity used to build this proof
	 */
	public Proof(Verbosity verbosity) {
		this.verbosity = verbosity;
	}

	/**
	 * Returns the argument of this proof.
	 *
	 * @return the argument of this proof
	 */
	public Argument getArgument() {
		return this.argument;
	}

	/**
	 * Sets the argument of this proof to the specified argument.
	 *
	 * @param argument a proof argument
	 */
	public void setArgument(Argument argument) {
		this.argument = argument;
	}

	/**
	 * Sets the argument of this proof to a simple
	 * argument created from the specified string.
	 *
	 * @param argument a quick description of the
	 * reason why the proof has succeeded or failed
	 */
	public void setArgument(String argument) {
		this.argument = new ArgumentSimple(argument);
	}

	/**
	 * Returns <code>true</code> iff this proof has succeeded
	 * i.e., it has an argument.
	 *
	 * @return <code>true</code> iff this proof has succeeded
	 */
	public boolean isSuccess() {
		return this.argument != null;
	}

	/**
	 * Returns the result of this proof.
	 *
	 * @return the result of this proof
	 */
	public ProofResult getResult() {
		return this.result;
	}

	/**
	 * Sets the result of this proof to the specified
	 * result.
	 *
	 * @param result a result for this proof
	 * (<code>YES</code>, <code>NO</code>, <code>MAYBE</code>)
	 */
	public void setResult(ProofResult result) {
		this.result = result;
	}

	/**
	 * Merges the provided proof with this proof.
	 *
	 * @param proof a proof to merge with this proof
	 * @throws NullPointerException if <code>proof</code>
	 * is <code>null</code>
	 */
	public void merge(Proof proof) {
		this.result = proof.result;
		this.argument = proof.argument;
		this.content.append(proof.content);
	}

	/**
	 * Prints the specified object on this proof.
	 * The string representation of the object is
	 * obtained using {@code Object.toString()}.
	 *
	 * @param object an object to be printed
	 */
	public void print(Object object) {
		this.content.append(object);
	}

	/**
	 * Prints the specified object on this proof.
	 * The string representation of the object is
	 * obtained using {@code Object.toString()}.
	 *
	 * @param object an object to be printed
	 * @param indentation the number of single spaces
	 * to print before the specified object
	 */
	public void print(Object object, int indentation) {
		this.content.repeat(" ", Math.max(0, indentation));
		this.content.append(object);
	}

	/**
	 * Prints the specified object on this proof, followed with
	 * a newline character. The string representation of the object
	 * is obtained using <code>Object.toString()</code>.
	 *
	 * @param object an object to be printed
	 */
	public void println(Object object) {
		this.content.append(object);
		this.content.append("\n");
	}

	/**
	 * Prints the specified object on this proof, followed with
	 * a newline character. The string representation of the object
	 * is obtained using <code>Object.toString()</code>.
	 *
	 * @param object an object to be printed
	 * @param indentation the number of single spaces
	 * to print before the specified object
	 */
	public void println(Object object, int indentation) {
		this.content.repeat(" ", Math.max(0, indentation));
		this.content.append(object);
		this.content.append("\n");
	}

	/**
	 * Prints a newline character on this proof.
	 */
	public void println() {
		this.content.append("\n");
	}

	/**
	 * If this proof is built in verbose mode, then prints the
	 * specified object on it, otherwise does nothing.
	 * The string representation of the object is obtained
	 * using <code>Object.toString()</code>.
	 *
	 * @param object an object to be printed
	 */
	public void printIfVerbose(Object object) {
		if (this.verbosity.includesProofDetails())
			this.content.append(object);
	}

	/**
	 * If this proof is built in verbose mode, then prints the
	 * specified object on it, otherwise does nothing.
	 * The string representation of the object is obtained
	 * using <code>Object.toString()</code>.
	 *
	 * @param object an object to be printed
	 * @param indentation the number of single spaces
	 * to print before the specified object
	 */
	public void printIfVerbose(Object object, int indentation) {
		if (this.verbosity.includesProofDetails()) {
			this.content.repeat(" ", Math.max(0, indentation));
			this.content.append(object);
		}
	}

	/**
	 * If this proof is built in verbose mode, then prints the
	 * specified object on it followed with a newline character,
	 * otherwise does nothing. The string representation of the
	 * object is obtained using <code>Object.toString()</code>.
	 *
	 * @param object an object to be printed
	 */
	public void printlnIfVerbose(Object object) {
		if (this.verbosity.includesProofDetails()) {
			this.content.append(object);
			this.content.append("\n");
		}
	}

	/**
	 * If this proof is built in verbose mode, then prints the
	 * specified object on it followed with a newline character,
	 * otherwise does nothing. The string representation of the
	 * object is obtained using <code>Object.toString()</code>.
	 *
	 * @param object an object to be printed
	 * @param indentation the number of single spaces
	 * to print before the specified object
	 */
	public void printlnIfVerbose(Object object, int indentation) {
		if (this.verbosity.includesProofDetails()) {
			this.content.repeat(" ", Math.max(0, indentation));
			this.content.append(object);
			this.content.append("\n");
		}
	}

	/**
	 * If this proof is built in verbose mode, then prints a
	 * newline character on it, otherwise does nothing.
	 */
	public void printlnIfVerbose() {
		if (this.verbosity.includesProofDetails())
			this.content.append("\n");
	}

	/**
	 * Returns whether retained traces from all concurrent attempts must be
	 * rendered in this proof.
	 *
	 * @return {@code true} only in very verbose mode
	 */
	public boolean isInVeryVerboseMode() {
		return this.verbosity.includesAllAttemptTraces();
	}

	/**
	 * Returns whether this proof has retained a detailed description.
	 *
	 * @return {@code true} iff at least one character was retained
	 */
	public boolean hasDescription() {
		return !this.content.isEmpty();
	}

	/**
	 * Returns a String representation of this proof.
	 *
	 * @return a String representation of this proof
	 */
	@Override
	public String toString() {
		String submitProblem = (this.result == ProofResult.MAYBE ?
				"""
				
				
				Please submit challenging problems to
				the corresponding benchmark collection
				see https://mysolvertimesout.org
				"""
				: "");

		String arg = (this.argument == null ? "" :
			"\n\n** BEGIN proof argument **\n" + this.argument + "\n** END proof argument **");

		String separator1 = "";
		String separator2 = "";
		if (!this.content.isEmpty()) {
			separator1 = "\n\n** BEGIN proof description **\n";
			separator2 = "\n** END proof description **";
		}

		return
				this.result + submitProblem + arg +
				separator1 + this.content + separator2;
	}
}
