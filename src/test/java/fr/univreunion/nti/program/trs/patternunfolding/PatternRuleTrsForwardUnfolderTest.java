/*
 * Copyright 2025 Etienne Payet <etiennepayet at univ-reunion.fr>
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
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class PatternRuleTrsForwardUnfolderTest {

	private final ParserString parser = new ParserString();
	private final Map<String, Variable> variables = new HashMap<>();

	@Test
	void unfoldsAtProvidedPositionWithoutChangingInputs() throws IOException {
		PatternRuleTrs source = rule("f(X){}{}", "g(h(X)){}{}", 2);
		PatternRuleTrs unfoldingRule = rule("h(Y){}{}", "k(Y){}{}", 3);
		Position position = new Position(0);
		SimplePatternTerm rightAtPosition = source.getRight().get(position);
		String sourceBefore = source.toString(variableNames());
		String unfoldingRuleBefore = unfoldingRule.toString(variableNames());

		PatternRuleTrs unfolded = PatternRuleTrsForwardUnfolder.tryUnfold(
				source, unfoldingRule, position, rightAtPosition, 7);

		assertNotNull(unfolded);
		Map<Variable, String> unfoldedVariableNames = new HashMap<>();
		assertEquals("f(_0)", unfolded.getLeft().toString(unfoldedVariableNames));
		assertEquals("g(k(_0))", unfolded.getRight().toString(unfoldedVariableNames));
		assertEquals(7, unfolded.getIteration());
		assertEquals(sourceBefore, source.toString(variableNames()));
		assertEquals(unfoldingRuleBefore, unfoldingRule.toString(variableNames()));
		assertNotSame(
				unfoldingRule.getRight().getPatternSubstitution(),
				unfolded.getRight().getPatternSubstitution());
		assertNotSame(
				unfoldingRule.getRight().getPatternSubstitution()
						.getHatFunctionSubstitution(),
				unfolded.getRight().getPatternSubstitution()
						.getHatFunctionSubstitution());
	}

	@Test
	void rejectsIncompatibleRule() throws IOException {
		PatternRuleTrs source = rule("f(X){}{}", "g(h(X)){}{}", 2);
		PatternRuleTrs unfoldingRule = rule("q(Y){}{}", "k(Y){}{}", 3);
		Position position = new Position(0);

		PatternRuleTrs unfolded = PatternRuleTrsForwardUnfolder.tryUnfold(
				source,
				unfoldingRule,
				position,
				source.getRight().get(position),
				7);

		assertNull(unfolded);
	}

	@Test
	void unfoldsWithMoreThanFourDistinctRightVariables() throws IOException {
		PatternRuleTrs source = rule(
				"f(A,B,C,D,E,F){}{}",
				"g(h(A),B,C,D,E,F,A){}{}",
				2);
		PatternRuleTrs unfoldingRule = rule("h(X){}{}", "k(X){}{}", 3);
		Position position = new Position(0);

		PatternRuleTrs unfolded = PatternRuleTrsForwardUnfolder.tryUnfold(
				source,
				unfoldingRule,
				position,
				source.getRight().get(position),
				7);

		assertNotNull(unfolded);
		Map<Variable, String> names = new HashMap<>();
		assertEquals("f(_0,_1,_2,_3,_4,_5)", unfolded.getLeft().toString(names));
		assertEquals(
				"g(k(_0),_1,_2,_3,_4,_5,_0)",
				unfolded.getRight().toString(names));
	}

	@Test
	void standardizesSharedVariablesApartAfterCompatibilityGuard() throws IOException {
		PatternRuleTrs source = rule("p(X){}{}", "g(X){}{}", 2);
		PatternRuleTrs unfoldingRule = rule("f(X){}{}", "h(X){}{}", 3);
		Position position = new Position(0);

		PatternRuleTrs unfolded = PatternRuleTrsForwardUnfolder.tryUnfold(
				source,
				unfoldingRule,
				position,
				source.getRight().get(position),
				7);

		assertNotNull(unfolded);
		Map<Variable, String> names = new HashMap<>();
		assertEquals("p(f(_0))", unfolded.getLeft().toString(names));
		assertEquals("g(h(_0))", unfolded.getRight().toString(names));
	}

	@Test
	void preservesSharingWithCopiedRightSubstitution() throws IOException {
		PatternRuleTrs source = rule("p(X){}{}", "g(X){}{}", 2);
		PatternRuleTrs unfoldingRule = rule(
				"f(X){}{}",
				"h(X){X->s(X)}{X->0}",
				3);
		Position position = new Position(0);
		String sourceBefore = source.toString(variableNames());
		String unfoldingRuleBefore = unfoldingRule.toString(variableNames());

		PatternRuleTrs unfolded = PatternRuleTrsForwardUnfolder.tryUnfold(
				source,
				unfoldingRule,
				position,
				source.getRight().get(position),
				7);

		assertNotNull(unfolded);
		assertEquals(sourceBefore, source.toString(variableNames()));
		assertEquals(unfoldingRuleBefore, unfoldingRule.toString(variableNames()));
		assertEquals("p(f(_0))", unfolded.getLeft().toString(new HashMap<>()));
		Map<Variable, String> rightNames = new HashMap<>();
		assertEquals(
				"g(h(_0))",
				unfolded.getRight().getBaseTerm().toString(rightNames, false));
		assertEquals(
				"{_0->hat[s(□)]^[1, 0](0)}",
				unfolded.getRight().getPatternSubstitution().toString(rightNames));
	}

	@Test
	void keepsMutableRightResultIndependentFromSourceWithoutGroundArguments()
			throws IOException {

		PatternRuleTrs source = rule(
				"p(X,Y){}{}",
				"g(h(X),q(Y)){}{}",
				2);
		PatternRuleTrs unfoldingRule = rule("h(Z){}{}", "k(Z){}{}", 3);
		Position position = new Position(0);
		String sourceBefore = source.toString(variableNames());

		PatternRuleTrs unfolded = PatternRuleTrsForwardUnfolder.tryUnfold(
				source,
				unfoldingRule,
				position,
				source.getRight().get(position),
				7);

		assertNotNull(unfolded);
		Term unfoldedRightBase = unfolded.getRight().getBaseTerm();
		assertNotSame(source.getRight().getBaseTerm(), unfoldedRightBase);
		Substitution mutation = new Substitution();
		mutation.add((Variable) unfoldedRightBase.get(1).get(0),
				parser.parseTerm("a", new HashMap<>()));
		unfoldedRightBase.applyInPlace(mutation);

		assertEquals("g(k(_0),q(a))", unfoldedRightBase.toString(new HashMap<>(), false));
		assertEquals(sourceBefore, source.toString(variableNames()));
	}

	/** Builds a pattern rule from textual simple pattern terms. */
	private PatternRuleTrs rule(
			String left,
			String right,
			int iteration) throws IOException {

		return PatternRuleTrs.tryBuild(
				parser.parseSimplePatternTerm(left, variables),
				parser.parseSimplePatternTerm(right, variables),
				iteration);
	}

	/** Returns the variable names used by the textual fixtures. */
	private Map<Variable, String> variableNames() {
		Map<Variable, String> names = new HashMap<>();
		for (Map.Entry<String, Variable> entry : this.variables.entrySet())
			names.put(entry.getValue(), entry.getKey());
		return names;
	}
}
