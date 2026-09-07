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

package fr.univreunion.nti.parse.string;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.SyntaxException;
import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.PrologList;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class ParserStringTest {

	private final ParserString parser = new ParserString();

	@Test
	void parsesTermsAndReusesNamedVariables() throws IOException {
		Map<String, Variable> variables = new HashMap<>();
		Variable existingVariable = new Variable();
		variables.put("X", existingVariable);

		Function function = assertInstanceOf(
				Function.class, this.parser.parseTerm("f(X,X,_)", variables));
		assertSame(existingVariable, function.getChild(0));
		assertSame(existingVariable, function.getChild(1));
		assertNotSame(existingVariable, function.getChild(2));
		assertEquals(1, variables.size());

		assertInstanceOf(PrologList.class, this.parser.parseTerm("[a,X|T]", variables));
		assertSame(existingVariable, variables.get("X"));
		assertNotNull(variables.get("T"));
	}

	@Test
	void parsesEmptyProperImproperAndNestedPrologLists() throws IOException {
		Map<String, Variable> variables = new HashMap<>();

		Term emptyList = assertInstanceOf(
				PrologList.class, this.parser.parseTerm("[]", variables));
		Term properList = assertInstanceOf(
				PrologList.class, this.parser.parseTerm("[a,b]", variables));
		Term improperList = assertInstanceOf(
				PrologList.class, this.parser.parseTerm("[a,b|X]", variables));
		Term nestedList = assertInstanceOf(
				PrologList.class, this.parser.parseTerm("[[a],b]", variables));

		assertEquals("[]", emptyList.toString(new HashMap<>(), false));
		assertEquals("[a,b]", properList.toString(new HashMap<>(), false));
		Map<Variable, String> variableNames = new HashMap<>();
		variableNames.put(variables.get("X"), "X");
		assertEquals("[a,b|X]", improperList.toString(variableNames, false));
		assertEquals("[[a],b]", nestedList.toString(new HashMap<>(), false));
	}

	@Test
	void reportsMalformedPrologListsAsSyntaxErrors() {
		SyntaxException exception = assertThrows(SyntaxException.class,
				() -> this.parser.parseTerm("[a b]", new HashMap<>()));
		assertEquals("syntax error: non-ended list at line 1", exception.getMessage());
		assertEquals(1, exception.getLineNumber());
	}

	@Test
	void parsesSubstitutionsAndSimplePatterns() throws IOException {
		Map<String, Variable> variables = new HashMap<>();
		Substitution substitution =
				this.parser.parseSubstitution("{X->s(X),Y->0}", variables);
		Variable x = variables.get("X");
		Function xImage = assertInstanceOf(Function.class, substitution.get(x));
		assertSame(x, xImage.getChild(0));

		SimplePatternSubstitution patternSubstitution =
				this.parser.parseSimplePatternSubstitution("{X->s(X)}{X->0}", variables);
		assertNotNull(patternSubstitution);
		assertEquals(1, patternSubstitution.getArity());
		assertNotNull(patternSubstitution.getPumping().get(x));
		assertNotNull(patternSubstitution.getClosing().get(x));

		SimplePatternTerm patternTerm = this.parser.parseSimplePatternTerm(
				"p(X){X->s(X)}{X->0}", variables);
		assertNotNull(patternTerm);
		assertEquals(1, patternTerm.getArity());
		Function patternBase = assertInstanceOf(Function.class, patternTerm.getBaseTerm());
		assertSame(x, patternBase.getChild(0));
	}

	@Test
	void parsesEmptyAndMultipleMappingsAndOrderedPumpingSubstitutions() throws IOException {
		Map<String, Variable> variables = new HashMap<>();
		assertTrue(this.parser.parseSubstitution("{}", variables).isEmpty());

		Substitution substitution =
				this.parser.parseSubstitution("{X->a,Y->f(X),Z->Y}", variables);
		Variable x = variables.get("X");
		Variable y = variables.get("Y");
		Variable z = variables.get("Z");
		assertEquals(3, substitution.getDomain().size());
		Function yImage = assertInstanceOf(Function.class, substitution.get(y));
		assertSame(x, yImage.getChild(0));
		assertSame(y, substitution.get(z));

		SimplePatternSubstitution patternSubstitution =
				this.parser.parseSimplePatternSubstitution(
						"{X->s(X)}{X->s(s(X))}{X->0}", variables);
		assertNotNull(patternSubstitution);
		assertEquals(2, patternSubstitution.getArity());
		var substitutions = patternSubstitution.iterator();
		Function firstPumpingImage =
				assertInstanceOf(Function.class, substitutions.next().get(x));
		assertSame(x, firstPumpingImage.getChild(0));
		Function secondPumpingImage =
				assertInstanceOf(Function.class, substitutions.next().get(x));
		Function nestedPumpingImage =
				assertInstanceOf(Function.class, secondPumpingImage.getChild(0));
		assertSame(x, nestedPumpingImage.getChild(0));
		Function closingImage = assertInstanceOf(Function.class, substitutions.next().get(x));
		assertEquals("0", closingImage.getRootSymbol().getName());
		assertFalse(substitutions.hasNext());

		assertNull(this.parser.parseSimplePatternSubstitution(
				"{X->f(X)}{X->g(X)}{X->0}", new HashMap<>()));
	}

	@Test
	void parsesLpTrsAndPatternRules() throws IOException {
		Map<String, Variable> variables = new HashMap<>();
		RuleLp lpRule = this.parser.parseLpRule("p(X) :- q(X),r(a).", variables);
		assertEquals(2, lpRule.getBodyLength());
		assertSame(variables.get("X"), lpRule.getHead().getChild(0));
		assertSame(variables.get("X"), lpRule.getBody(0).getChild(0));
		assertEquals("q", lpRule.getBody(0).getRootSymbol().getName());
		assertEquals("r", lpRule.getBody(1).getRootSymbol().getName());

		RuleTrs trsRule = this.parser.parseTrsRule("f(X) -> g(X)", variables);
		assertSame(variables.get("X"), trsRule.getLeft().getChild(0));
		assertSame(variables.get("X"), assertInstanceOf(Function.class,
				trsRule.getRight()).getChild(0));

		PatternRuleTrs patternRule = this.parser.parsePatternRuleTrs(
				"p(X){X->s(X)}{X->0} -> p(X){X->s(X)}{X->0}", variables);
		assertNotNull(patternRule);
		assertEquals(0, patternRule.getIteration());
		Function leftBase = assertInstanceOf(Function.class, patternRule.getLeft().getBaseTerm());
		Function rightBase = assertInstanceOf(Function.class, patternRule.getRight().getBaseTerm());
		assertSame(variables.get("X"), leftBase.getChild(0));
		assertSame(variables.get("X"), rightBase.getChild(0));
	}

	@Test
	void parsesLpFactsAndVariableAndIntegerTrsRightHandSides() throws IOException {
		Map<String, Variable> variables = new HashMap<>();
		RuleLp fact = this.parser.parseLpRule("p(X).", variables);
		assertEquals(0, fact.getBodyLength());
		assertSame(variables.get("X"), fact.getHead().getChild(0));

		RuleTrs variableRule = this.parser.parseTrsRule("f(X) -> X", variables);
		assertSame(variables.get("X"), variableRule.getRight());

		RuleTrs integerRule = this.parser.parseTrsRule("f(X) -> 0", variables);
		Function integerRight = assertInstanceOf(Function.class, integerRule.getRight());
		assertEquals("0", integerRight.getRootSymbol().getName());
		assertEquals(0, integerRight.getRootSymbol().getArity());
	}

	@Test
	void reportsMalformedRuleBodiesAndMappingsAsSyntaxErrors() {
		assertThrows(SyntaxException.class,
				() -> this.parser.parseLpRule("p :- .", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parseTrsRule("f(X) -> .", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parseSubstitution("{X->0,}", new HashMap<>()));
	}

	@Test
	void rejectsTrailingInputAtEveryPublicEntryPoint() {
		assertThrows(SyntaxException.class,
				() -> this.parser.parseTerm("f(X) garbage", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parseSubstitution("{X->0} garbage", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parseSimplePatternSubstitution(
						"{X->s(X)}{X->0} garbage", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parseSimplePatternTerm(
						"p(X){X->s(X)}{X->0} garbage", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parseLpRule("p(X). garbage", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parseTrsRule("f(X) -> g(X) garbage", new HashMap<>()));
		assertThrows(SyntaxException.class,
				() -> this.parser.parsePatternRuleTrs(
						"p(X){}{} -> p(X){}{} garbage", new HashMap<>()));
	}
}
