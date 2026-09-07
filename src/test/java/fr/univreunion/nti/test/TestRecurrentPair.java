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

package fr.univreunion.nti.test;

import static org.junit.jupiter.api.Assertions.*;

import java.net.URISyntaxException;
import java.net.URL;
import java.nio.file.Path;
import java.util.Iterator;
import java.util.logging.Logger;

import fr.univreunion.nti.parse.ProgramFactory;
import fr.univreunion.nti.program.recurrentpair.RecurrentPair;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.Options;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
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

	@Test
	@DisplayName("test getInstance")
	void testTryBuild() throws Exception {
		Logger logger = Logger.getLogger("TestRecurrentPair");

		try {
			RecurrentPair recpair = buildRecurrentPair();
			assertNotNull(recpair, "Aborting test: tryBuild returns null!");
			if (logger.isLoggable(java.util.logging.Level.INFO)) {
				logger.info(recpair.toString());
			}
		}
		catch (Exception e) {
			logger.info(e.toString());
		}
	}

	@Test
	@DisplayName("test recurrent pair detailed string representation")
	void recurrentPairToStringUsesDetailedCertificateFormat() throws Exception {
		RecurrentPair recurrentPair = buildRecurrentPair();

		assertEquals("""
				u1 -> v1 = f(_0,|0|,s(s(_1)),|0|) -> f(_0,|0|,s(_1),|0|)
				u2 -> v2 = f(_2,|0|,s(|0|),|0|) -> f(s(_2),|0|,s(_2),|0|)
				We have:
				u1 = c1[x,c2^m1[y]], v1 = c1[c2^n1[x],c2^n2[y]]
				u2 = c1[x,c2^m2[s]], v2 = c1[c2^n3[t],c2^n4[x]]
				for:
				c1 = f(\u25a1,|0|,\u25a1',|0|)
				c2 = s(\u25a1)
				s = |0|
				t = _2
				(m1,m2) = (2,1) and (n1,n2,n3,n4) = (0,1,1,1)
				Nonterminating term = f(|0|,|0|,s(|0|),|0|)""",
				recurrentPair.toString());
	}

	@Test
	@DisplayName("test LP")
	void testLP() throws Exception {
		String[] args = new String[] {
				resourcePath("examples/TC23/payet-nonloop-1_3.pl"),
				"-v"
		};

		Options options = Options.parse(args);

		final Lp mP = (Lp) ProgramFactory.parse(options.getFileName());

		Proof proof = mP.proveTermination(new AnalysisContext(
				options.isInVerboseMode(),
				options.getPathToCti()));
		assertTrue(proof.isSuccess(), "Aborting test: proof has failed");
	}

	private static RecurrentPair buildRecurrentPair() throws Exception {
		Iterator<RuleTrs> rules = recurrentPairRules();

		RuleTrs firstRule = rules.next();
		RuleTrs secondRule = rules.next();

		Function u1 = firstRule.getLeft();
		Function v1 = (Function) firstRule.getRight();
		Function u2 = secondRule.getLeft();
		Function v2 = (Function) secondRule.getRight();

		return RecurrentPair.tryBuild(u1, v1, u2, v2);
	}

	private static Iterator<RuleTrs> recurrentPairRules() throws Exception {
		String[] args = new String[] {
				resourcePath("examples/TC24/payet-nonloop-1.ari")
		};

		Options options = Options.parse(args);
		Trs trs = (Trs) ProgramFactory.parse(options.getFileName());

		assertTrue(2 <= trs.size(), "Aborting test: not enough terms!");
		return trs.iterator();
	}

}
