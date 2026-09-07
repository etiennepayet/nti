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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.patternunfolding;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class PatternRuleTrsCopierTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void deeplyCopiesRegularRuleWithSharedFreshVariable() throws IOException {
		PatternRuleTrs original = rule("f(X){}{}", "g(X){}{}", 4);
		Variable originalVariable =
				original.getLeft().getBaseTerm().getVariables().iterator().next();
		Map<Term, Term> copies = new HashMap<>();

		PatternRuleTrs copy = original.deepCopy(copies);

		Variable copiedLeftVariable =
				copy.getLeft().getBaseTerm().getVariables().iterator().next();
		Variable copiedRightVariable =
				copy.getRight().getBaseTerm().getVariables().iterator().next();
		assertNotSame(original, copy);
		assertNotSame(original.getLeft(), copy.getLeft());
		assertNotSame(original.getRight(), copy.getRight());
		assertNotSame(originalVariable, copiedLeftVariable);
		assertSame(copiedLeftVariable, copiedRightVariable);
		assertSame(copiedLeftVariable, copies.get(originalVariable));
		assertEquals(4, copy.getIteration());
		assertEquals(-1, copy.getAlpha());
		assertNull(copy.getNonTerminatingTerm());
	}

	@Test
	void deeplyCopiesPrecomputedAnalysis() throws IOException {
		PatternRuleTrs original = rule("p(0){}{}", "p(0){}{}", 6);

		PatternRuleTrs copy = original.deepCopy();

		assertEquals(6, copy.getIteration());
		assertEquals(original.getAlpha(), copy.getAlpha());
		assertEquals(0, copy.getAlpha());
		assertEquals(
				original.getNonTerminatingTerm().toString(),
				copy.getNonTerminatingTerm().toString());
		assertNotSame(
				original.getNonTerminatingTerm(),
				copy.getNonTerminatingTerm());
	}

	/** Builds a pattern rule from textual simple pattern terms. */
	private PatternRuleTrs rule(
			String left,
			String right,
			int iteration) throws IOException {

		return PatternRuleTrs.tryBuild(
				patternTerm(left),
				patternTerm(right),
				iteration);
	}

	/** Parses one textual simple pattern term. */
	private SimplePatternTerm patternTerm(String text) throws IOException {
		return parser.parseSimplePatternTerm(text, variables);
	}
}
