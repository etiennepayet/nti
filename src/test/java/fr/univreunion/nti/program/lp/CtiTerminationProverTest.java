/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.lp;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import fr.univreunion.nti.program.Proof;

class CtiTerminationProverTest {

	@TempDir
	Path temporaryDirectory;

	@Test
	@DisplayName("drain cTI output and error streams while the process runs")
	void drainOutputAndErrorStreamsWhileProcessRuns() throws Exception {
		Path script = this.executableScript("large-output.sh", """
				#!/bin/sh
				echo "initial diagnostic" >&2
				echo YES
				index=0
				while [ "$index" -lt 5000 ]; do
				  echo "output $index"
				  echo "diagnostic $index" >&2
				  index=$((index + 1))
				done
				""");
		Proof proof = new Proof(false);

		ResultLp result = org.junit.jupiter.api.Assertions.assertTimeoutPreemptively(
				Duration.ofSeconds(10),
				() -> new CtiTerminationProver().prove(
						script.toString(), "program.pl", proof));

		assertTrue(result.isYES());
		assertTrue(proof.getArgument().toString().startsWith("Proved by cTI"));
	}

	@Test
	@DisplayName("reject positive cTI output when the process exits with an error")
	void rejectPositiveOutputFromFailedProcess() throws Exception {
		Path script = this.executableScript("failed.sh", """
				#!/bin/sh
				echo YES
				exit 7
				""");
		Proof proof = new Proof(false);

		ResultLp result = new CtiTerminationProver().prove(
				script.toString(), "program.pl", proof);

		assertTrue(result.isERROR());
		assertEquals("cTI exited with status 7.", proof.getArgument().toString());
	}

	@Test
	@DisplayName("convert an ordinary cTI output-reader failure to an error")
	void convertOrdinaryOutputReaderFailureToError() throws Exception {
		Path script = this.positiveOutputWithDetailScript();
		IllegalStateException failure =
				new IllegalStateException("reader failure");
		Proof proof = failingVerboseProof(failure);

		ResultLp result = new CtiTerminationProver().prove(
				script.toString(), "program.pl", proof);

		assertTrue(result.isERROR());
		assertEquals(failure.toString(), proof.getArgument().toString());
	}

	@Test
	@DisplayName("propagate a serious cTI output-reader failure")
	void propagateSeriousOutputReaderFailure() throws Exception {
		Path script = this.positiveOutputWithDetailScript();
		AssertionError failure = new AssertionError("serious reader failure");
		Proof proof = failingVerboseProof(failure);

		AssertionError propagated = assertThrows(
				AssertionError.class,
				() -> new CtiTerminationProver().prove(
						script.toString(), "program.pl", proof));

		assertSame(failure, propagated);
	}

	@Test
	@DisplayName("terminate the cTI process when its worker is interrupted")
	void terminateProcessWhenWorkerIsInterrupted() throws Exception {
		Path processIdentifier = this.temporaryDirectory.resolve("cti.pid");
		Path script = this.executableScript("blocking.sh", """
				#!/bin/sh
				echo $$ > "$1"
				exec sleep 60
				""");
		Proof proof = new Proof(false);
		AtomicReference<ResultLp> result = new AtomicReference<>();
		AtomicBoolean interruptionRestored = new AtomicBoolean();
		Thread worker = new Thread(() -> {
			result.set(new CtiTerminationProver().prove(
					script.toString(), processIdentifier.toString(), proof));
			interruptionRestored.set(Thread.currentThread().isInterrupted());
		});
		worker.start();
		long pid = this.awaitProcessIdentifier(processIdentifier);

		try {
			worker.interrupt();
			worker.join(TimeUnit.SECONDS.toMillis(5));

			assertFalse(worker.isAlive());
			assertNotNull(result.get());
			assertTrue(result.get().isMAYBE(),
					() -> "unexpected result " + result.get()
							+ ": " + proof.getArgument());
			assertEquals("INTERRUPTED!", proof.getArgument().toString());
			assertTrue(interruptionRestored.get());
			assertFalse(ProcessHandle.of(pid)
					.map(ProcessHandle::isAlive).orElse(false));
		}
		finally {
			worker.interrupt();
			ProcessHandle.of(pid).ifPresent(ProcessHandle::destroyForcibly);
		}
	}

	/** Creates one executable shell script in the temporary test directory. */
	private Path executableScript(String name, String contents)
			throws IOException {

		Path script = Files.writeString(
				this.temporaryDirectory.resolve(name), contents);
		assertTrue(script.toFile().setExecutable(true));
		return script;
	}

	/** Creates a cTI-like script that prints a positive answer and one detail. */
	private Path positiveOutputWithDetailScript() throws IOException {
		return this.executableScript("positive-with-detail.sh", """
				#!/bin/sh
				echo YES
				echo detail
				exec sleep 60
				""");
	}

	/** Creates a verbose proof that fails when one detail line is retained. */
	private static Proof failingVerboseProof(Throwable failure) {
		return new Proof(true) {
			@Override
			public void printlnIfVerbose(Object object) {
				if (failure instanceof RuntimeException runtimeException)
					throw runtimeException;
				if (failure instanceof Error error)
					throw error;
				throw new AssertionError(failure);
			}
		};
	}

	/** Waits for the test process to publish its process identifier. */
	private long awaitProcessIdentifier(Path processIdentifier) throws Exception {
		long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(5);
		while ((!Files.exists(processIdentifier)
				|| Files.size(processIdentifier) == 0)
				&& System.nanoTime() < deadline) {
			Thread.sleep(10);
		}
		assertTrue(Files.exists(processIdentifier));
		return Long.parseLong(Files.readString(processIdentifier).trim());
	}
}
