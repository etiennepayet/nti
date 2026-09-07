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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.test;

import static org.junit.jupiter.api.Assertions.*;

import java.util.LinkedList;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.UnfoldedRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;

/**
 * A class for testing unfolded LP rules.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
class TestUnfoldedRuleLp {

	@Test
	@DisplayName("test deep copy preserves binary unfolded rules")
	void testDeepCopyPreservesBinaryUnfoldedRules() {
		BinaryRuleLp binaryRule = new BinaryRuleLp(atom("p"), atom("q"), 2);

		UnfoldedRuleLp copy = binaryRule.deepCopy(3);

		assertInstanceOf(BinaryRuleLp.class, copy);
		assertEquals(3, copy.getIteration());
	}

	@Test
	@DisplayName("test deep copy preserves non-binary unfolded rules")
	void testDeepCopyPreservesNonBinaryUnfoldedRules() {
		UnfoldedRuleLp fact = UnfoldedRuleLp.fact(atom("p"), 2);
		UnfoldedRuleLp multiBodyRule =
				UnfoldedRuleLp.of(atom("p"),
						new Function[] { atom("q"), atom("r") }, 2);

		UnfoldedRuleLp factCopy = fact.deepCopy(3);
		UnfoldedRuleLp multiBodyRuleCopy = multiBodyRule.deepCopy(3);

		assertFalse(factCopy instanceof BinaryRuleLp);
		assertFalse(multiBodyRuleCopy instanceof BinaryRuleLp);
		assertEquals(3, factCopy.getIteration());
		assertEquals(3, multiBodyRuleCopy.getIteration());
	}

	private static Function atom(String predicateName) {
		return new Function(
				FunctionSymbol.intern(predicateName, 0),
				new LinkedList<Term>());
	}
}
