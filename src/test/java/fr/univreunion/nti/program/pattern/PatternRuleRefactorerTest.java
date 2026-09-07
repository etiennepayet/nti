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

package fr.univreunion.nti.program.pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class PatternRuleRefactorerTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void refactorsMoreGeneralLeftSide() throws IOException {
		SimplePatternTerm left =
				SimplePatternTerm.of(parser.parseTerm("p(X)", variables));
		SimplePatternTerm right =
				SimplePatternTerm.of(parser.parseTerm("p(s(X))", variables));

		RefactoredPatternRule refactored = PatternRuleRefactorer.tryRefactor(left, right);

		assertNotNull(refactored);
		assertNotNull(refactored.left());
		assertNotNull(refactored.right());
		assertTrue(refactored.left().getBaseTerm().isVariantOf(
				refactored.right().getBaseTerm(), new Substitution()));

		Variable variable = variables.get("X");
		HatFunction leftImage = assertInstanceOf(
				HatFunction.class,
				refactored.left().getPatternSubstitution()
						.getHatFunctionSubstitution()
						.getOrDefault(variable, variable));
		HatFunction rightImage = assertInstanceOf(
				HatFunction.class,
				refactored.right().getPatternSubstitution()
						.getHatFunctionSubstitution()
						.getOrDefault(variable, variable));
		assertSame(leftImage.getRootSymbol(), rightImage.getRootSymbol());
		assertEquals("hat[s(□)]", leftImage.getRootSymbol().toString());
		assertSame(variable, leftImage.getArgument());
		assertSame(variable, rightImage.getArgument());
		assertEquals(0, leftImage.getA());
		assertEquals(0, leftImage.getB());
		assertEquals(0, rightImage.getA());
		assertEquals(1, rightImage.getB());
	}

	@Test
	void leavesSubstitutionsWithoutContextualImageWhenVariableIsAbsent()
			throws IOException {
		SimplePatternTerm left =
				SimplePatternTerm.of(parser.parseTerm("p(X)", variables));
		SimplePatternTerm right =
				SimplePatternTerm.of(parser.parseTerm("p(0)", variables));

		RefactoredPatternRule refactored = PatternRuleRefactorer.tryRefactor(left, right);

		assertNotNull(refactored);
		Variable variable = variables.get("X");
		assertSame(
				variable,
				refactored.left().getPatternSubstitution()
						.getHatFunctionSubstitution()
						.getOrDefault(variable, variable));
	}

	@Test
	void rejectsLeftBaseThatIsNotMoreGeneral() throws IOException {
		SimplePatternTerm left =
				SimplePatternTerm.of(parser.parseTerm("p(0)", variables));
		SimplePatternTerm right =
				SimplePatternTerm.of(parser.parseTerm("p(s(0))", variables));

		assertNull(PatternRuleRefactorer.tryRefactor(left, right));
	}

	@Test
	void rejectsGeneralizedVariableInPumpingDomain() throws IOException {
		SimplePatternTerm left = parser.parseSimplePatternTerm(
				"p(X){X->s(X)}{X->0}", variables);
		SimplePatternTerm right = parser.parseSimplePatternTerm(
				"p(f(X,X)){X->s(X)}{X->0}", variables);

		assertNull(PatternRuleRefactorer.tryRefactor(left, right));
	}
}
