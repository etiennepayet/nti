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

package fr.univreunion.nti.program.lp;

import java.io.BufferedReader;
import java.io.Closeable;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CompletionException;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.Consumer;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;

/**
 * Runs a termination proof for an LP using cTI.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class CtiTerminationProver {

	/** The useful part of cTI standard output retained while it is drained. */
	private static final class CtiOutput {

		/** The first output line, which carries the cTI answer. */
		private String firstLine;

		/** The termination argument extracted from positive output. */
		private final StringBuilder argument =
				new StringBuilder("Proved by cTI");

		/** Retains one output line according to the historical output format. */
		private void retain(String line, Proof proof) {
			if (this.firstLine == null) {
				this.firstLine = line;
			}
			else if (this.isPositive()) {
				if (line.startsWith("predicate_term_condition("))
					this.argument.append(line);
				proof.printlnIfVerbose(line);
			}
		}

		/** Returns whether the first output line is a positive answer. */
		private boolean isPositive() {
			return this.firstLine != null && this.firstLine.startsWith("YES");
		}
	}

	/**
	 * Runs cTI on the specified program.
	 *
	 * @param cTI the path to cTI
	 * @param programName the name of the LP to analyze
	 * @param context the context of the analysis
	 * @return the <code>Result</code> of this prover
	 */
	public ResultLp prove(String cTI, String programName, AnalysisContext context) {
		return this.prove(cTI, programName, context.createProof());
	}

	/**
	 * Runs cTI on the specified program and writes its trace to the provided
	 * proof.
	 *
	 * @param cTI the path to cTI
	 * @param programName the name of the LP to analyze
	 * @param proof the proof local to this attempt
	 * @return the <code>Result</code> of this prover
	 */
	ResultLp prove(
			String cTI,
			String programName,
			Proof proof) {

		try {
			return this.readResult(this.startCtiProcess(cTI, programName), proof);
		} catch (Exception e) {
			// Occurs for instance when the specified path
			// to cTI is erroneous.
			proof.setArgument(e.toString());
			return ResultLp.error(proof);
		}
	}

	/**
	 * Starts the cTI process.
	 *
	 * @param cTI the path to cTI
	 * @param programName the name of the LP to analyze
	 * @return the cTI process
	 * @throws java.io.IOException if the process cannot be started
	 */
	private Process startCtiProcess(String cTI, String programName)
			throws IOException {
		ProcessBuilder pb = new ProcessBuilder(cTI, programName);
		return pb.start();
	}

	/**
	 * Reads and interprets the output of a cTI process.
	 *
	 * @param proc the cTI process
	 * @param proof the proof to update
	 * @return the <code>Result</code> of this prover
	 */
	private ResultLp readResult(Process proc, Proof proof) throws IOException {
		CtiOutput standardOutput = new CtiOutput();
		AtomicReference<IOException> streamFailure = new AtomicReference<>();
		CompletableFuture<Void> standardOutputReader = startStreamReader(
				proc.getInputStream(), line -> standardOutput.retain(line, proof),
				streamFailure);
		CompletableFuture<Void> standardErrorReader = startStreamReader(
				proc.getErrorStream(), null, streamFailure);
		terminateProcessOnReaderFailure(
				proc, standardOutputReader, standardErrorReader);
		int exitStatus;
		try {
			exitStatus = proc.waitFor();
			awaitStreamReaders(standardOutputReader, standardErrorReader);
		} catch (InterruptedException e) {
			Thread.currentThread().interrupt();
			terminateProcess(proc, standardOutputReader, standardErrorReader);
			proof.setArgument("INTERRUPTED!");
			return ResultLp.maybe(proof);
		}

		IOException failure = streamFailure.get();
		if (failure != null)
			throw failure;

		if (exitStatus != 0) {
			proof.setArgument("cTI exited with status " + exitStatus + ".");
			return ResultLp.error(proof);
		}

		if (standardOutput.firstLine != null) {
			if (standardOutput.isPositive())
				return this.buildYesResult(standardOutput, proof);

			// The first line is not a 'YES': this means
			// that cTI was not able to prove termination.
			return ResultLp.maybe(proof);
		}

		// If the process has not provided an output, then return a 'MAYBE'
		// result.
		proof.setArgument("cTI did not output anything.");
		return ResultLp.maybe(proof);
	}

	/**
	 * Starts a virtual thread that drains one process stream.
	 *
	 * @param stream the stream to drain
	 * @param lineConsumer the consumer receiving read lines, or {@code null}
	 * when lines only need to be discarded
	 * @param streamFailure the first stream failure encountered
	 * @return a future completed when the stream reader terminates
	 */
	private static CompletableFuture<Void> startStreamReader(
			InputStream stream,
			Consumer<String> lineConsumer,
			AtomicReference<IOException> streamFailure) {

		return CompletableFuture.runAsync(() -> {
			try (BufferedReader reader = new BufferedReader(
					new InputStreamReader(stream))) {
				String line;
				while ((line = reader.readLine()) != null) {
					if (lineConsumer != null)
						lineConsumer.accept(line);
				}
			}
			catch (IOException e) {
				streamFailure.compareAndSet(null, e);
			}
		}, command -> Thread.ofVirtual()
				.name("nti-cti-stream-reader").start(command));
	}

	/**
	 * Prevents a process from blocking on an undrained stream after one of its
	 * reader workers fails.
	 *
	 * @param proc the process whose streams are read
	 * @param streamReaders the stream-reader completions to monitor
	 */
	private static void terminateProcessOnReaderFailure(
			Process proc, CompletableFuture<?>... streamReaders) {

		for (CompletableFuture<?> streamReader : streamReaders) {
			streamReader.whenComplete((unused, failure) -> {
				if (failure != null)
					proc.destroyForcibly();
			});
		}
	}

	/**
	 * Waits for all the provided stream readers and rethrows an unchecked
	 * failure from any reader worker.
	 *
	 * @param streamReaders the stream-reader completions to await
	 */
	private static void awaitStreamReaders(
			CompletableFuture<?>... streamReaders) {

		try {
			CompletableFuture.allOf(streamReaders).join();
		}
		catch (CompletionException e) {
			Throwable cause = e.getCause();
			if (cause instanceof RuntimeException runtimeException)
				throw runtimeException;
			if (cause instanceof Error error)
				throw error;
			throw e;
		}
	}

	/**
	 * Terminates a cancelled cTI process and waits for its stream readers.
	 *
	 * @param proc the process to terminate
	 * @param streamReaders the process stream-reader completions to await
	 */
	private static void terminateProcess(
			Process proc, CompletableFuture<?>... streamReaders) {

		proc.destroyForcibly();
		proc.onExit().join();
		closeQuietly(proc.getInputStream());
		closeQuietly(proc.getErrorStream());
		closeQuietly(proc.getOutputStream());
		awaitStreamReaders(streamReaders);
	}

	/** Closes one process stream without replacing its proof result. */
	private static void closeQuietly(Closeable stream) {
		try {
			stream.close();
		}
		catch (IOException ignored) {
			// The process is already being forcibly terminated.
		}
	}

	/**
	 * Builds a positive cTI result.
	 *
	 * @param standardOutput the useful information retained from cTI output
	 * @param proof the proof to update
	 * @return the <code>YES</code> result
	 */
	private ResultLp buildYesResult(
			CtiOutput standardOutput, Proof proof) {
		proof.setResult(Proof.ProofResult.YES);
		proof.setArgument(standardOutput.argument.toString());

		return ResultLp.yes(proof);
	}
}
