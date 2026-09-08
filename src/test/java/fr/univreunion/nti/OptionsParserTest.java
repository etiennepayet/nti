/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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

package fr.univreunion.nti;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.Verbosity;

class OptionsParserTest {

	@Test
	@DisplayName("parse quiet, verbose and very verbose levels")
	void parseVerbosityLevels() {
		Options quiet = Options.parse(new String[0]);
		Options verbose = Options.parse(new String[] { "-v" });
		Options veryVerbose = Options.parse(new String[] { "-vv" });

		assertEquals(Verbosity.QUIET, quiet.getVerbosity());
		assertFalse(quiet.isInVerboseMode());
		assertEquals(Verbosity.VERBOSE, verbose.getVerbosity());
		assertTrue(verbose.isInVerboseMode());
		assertEquals(Verbosity.VERY_VERBOSE, veryVerbose.getVerbosity());
		assertTrue(veryVerbose.isInVerboseMode());
	}

	@Test
	@DisplayName("keep the greatest verbosity independently of option order")
	void keepGreatestVerbosityIndependentlyOfOptionOrder() {
		assertEquals(
				Verbosity.VERY_VERBOSE,
				Options.parse(new String[] { "-vv", "-v" }).getVerbosity());
		assertEquals(
				Verbosity.VERY_VERBOSE,
				Options.parse(new String[] { "-v", "-vv" }).getVerbosity());
	}

	@Test
	@DisplayName("reject the removed internal timeout option")
	void rejectRemovedInternalTimeoutOption() {
		IllegalStateException failure = assertThrows(
				IllegalStateException.class,
				() -> Options.parse(new String[] { "-t=1" }));

		assertTrue(failure.getMessage().contains("external process supervisor"));
	}

	@Test
	@DisplayName("parse the lowercase cTI option")
	void parseLowercaseCtiOption() {
		Options options = Options.parse(new String[] { "-cti=/usr/local/bin/cti" });

		assertEquals("/usr/local/bin/cti", options.getPathToCti());
	}

	@Test
	void preserveEqualsSignsInCtiPath() {
		String path = "/tmp/tools=custom/cti==";
		Options options = Options.parse(new String[] { "-cti=" + path });

		assertEquals(path, options.getPathToCti());
	}

	@Test
	void preserveEqualsSignsInInputFileName() {
		String fileName = "examples/program=custom.pl";
		Options options = Options.parse(new String[] { fileName, "-print" });

		assertEquals(fileName, options.getFileName());
		assertEquals(NtiAction.PRINT_PROG, options.getAction());
	}

	@Test
	void rejectUnknownArguments() {
		for (String argument : new String[] {
				"-prnit", "--unknown", "-unknown=input.pl", "unexpected.txt", "=", "" }) {
			IllegalStateException failure = assertThrows(
					IllegalStateException.class,
					() -> Options.parse(new String[] { "input.trs", argument }),
					argument);

			assertTrue(failure.getMessage().contains("unrecognized argument"));
		}
	}

	@Test
	void rejectInvalidIterationCounts() {
		for (String argument : new String[] {
				"-patunf=-1", "-patunf=-2147483648", "-patunf", "-patunf=",
				"-patunf=abc", "-patunf=2147483648" }) {
			IllegalStateException failure = assertThrows(
					IllegalStateException.class,
					() -> Options.parse(new String[] { argument }),
					argument);

			assertTrue(failure.getMessage().contains("non-negative integer"));
		}
	}

	@Test
	void acceptZeroAndPositiveIterationCounts() {
		for (int count : new int[] { 0, 1, 10 }) {
			Options options = Options.parse(new String[] { "-patunf=" + count });

			assertEquals(count, options.getNbIte());
			assertEquals(NtiAction.PATUNF, options.getAction());
		}
	}

	@Test
	@DisplayName("reject the former mixed-case cTI option")
	void rejectFormerMixedCaseCtiOption() {
		IllegalStateException failure = assertThrows(
				IllegalStateException.class,
				() -> Options.parse(new String[] { "-cTI=/usr/local/bin/cti" }));

		assertTrue(failure.getMessage().contains("renamed to -cti"));
	}
}
