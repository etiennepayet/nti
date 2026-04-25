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

package fr.univreunion.nti.test;

import static org.junit.jupiter.api.Assertions.*;

import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.util.Iterator;
import java.util.logging.Logger;

import fr.univreunion.nti.parse.ProgramFactory;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.Options;
import fr.univreunion.nti.Printer;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.RecurrentPair;
import fr.univreunion.nti.program.lp.Lp;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;

/**
 * A class for testing recurrent pairs.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
class TestRecurrentPair {

	private static String resourcePath(String resourceName) throws URISyntaxException {
		URL resource = TestRecurrentPair.class.getClassLoader().getResource(resourceName);
		assertNotNull(resource, () -> "Missing test resource: " + resourceName);
		return Path.of(resource.toURI()).toString();
	}

	private static void resetOptions() throws ReflectiveOperationException {
		java.lang.reflect.Field instance = Options.class.getDeclaredField("UNIQUE_INSTANCE");
		instance.setAccessible(true);
		instance.set(null, null);
	}

	/**
	 * @throws java.lang.Exception
	 */
	@BeforeAll
	@DisplayName("@BeforeAll")
	static void setUpBeforeClass() throws Exception {
		// This method is intentionally left empty because there are no resources to
		// clean up after all tests.
	}

	/**
	 * @throws java.lang.Exception
	 */
	@AfterAll
	static void tearDownAfterClass() throws Exception {
		// This method is intentionally left empty because there are no resources to clean up after all tests.
	}

	/**
	 * @throws java.lang.Exception
	 */
	@BeforeEach
	void setUp() throws Exception {
		resetOptions();
	}

	/**
	 * @throws java.lang.Exception
	 */
	@AfterEach
	void tearDown() throws Exception {
		resetOptions();
	}

	@Test
	@DisplayName("test getInstance")
	void testGetInstance() throws Exception {
		String[] args = new String[] {
				resourcePath("examples/TC24/payet-nonloop-1.ari")
		};

		Options.getInstance(args);
		Trs mIR = (Trs) ProgramFactory.parse(Options.getInstance().getFileName());

		// IR is supposed to consist of at least 2 rules.
		assertTrue(2 <= mIR.size(), "Aborting test: not enough terms!");

		Iterator<RuleTrs> it = mIR.iterator();
		RuleTrs mR1  = it.next();
		RuleTrs mR2 = it.next();
		// It is assumed that R1 and R2 have the
		// form f(...) -> f(...).
		Function u1 = mR1.getLeft();
		Function v1 = (Function) mR1.getRight();
		Function u2 = mR2.getLeft();
		Function v2 = (Function) mR2.getRight();

		Logger logger = Logger.getLogger("TestRecurrentPair");
		
		try {
			RecurrentPair recpair = RecurrentPair.getInstance(u1, v1, u2, v2);
			assertTrue(
					recpair != null,
					"Aborting test: getInstance returns null!");
			if (logger.isLoggable(java.util.logging.Level.INFO)) {
				logger.info(recpair.toString());
			}
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}
	
	@Test
	@DisplayName("test LP")
	void testLP() throws Exception {
		String[] args = new String[] {
				resourcePath("examples/TC23/payet-nonloop-1_3.pl"),
				"-v"
		};

		Options options = Options.getInstance(args);
		Printer printer = options.getPrinter();
		
		final Lp mP = (Lp) ProgramFactory.parse(Options.getInstance().getFileName());
				
		try {
			Proof proof = mP.proveTermination();
			assertTrue(proof.isSuccess(), "Aborting test: proof has failed");
			printer.println(proof);
		}
		catch (Exception e) {
			printer.println(e);
		}
		
		printer.close();
	}
}
