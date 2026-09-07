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

package fr.univreunion.nti.term.pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

class PatternTermTest {

	@Test
	@DisplayName("share components and delegate structural accessors")
	void shareComponentsAndDelegateStructuralAccessors() {
		Variable variable = new Variable();
		FunctionSymbol rootSymbol = uniqueSymbol("pattern-term-root", 1);
		Function baseTerm = new Function(rootSymbol, List.of(variable));
		Substitution firstPumping = new Substitution();
		Substitution secondPumping = new Substitution();
		Substitution closing = new Substitution();
		TestPatternSubstitution patternSubstitution =
				new TestPatternSubstitution(
						List.of(firstPumping, secondPumping, closing));
		TestPatternTerm patternTerm =
				new TestPatternTerm(baseTerm, patternSubstitution);

		assertSame(baseTerm, patternTerm.getBaseTerm());
		assertSame(patternSubstitution, patternTerm.getPatternSubstitution());
		assertSame(firstPumping, patternTerm.getPumping());
		assertSame(closing, patternTerm.getClosing());
		assertSame(rootSymbol, patternTerm.getRootSymbol());
		assertEquals(2, patternTerm.getArity());
		Map<Variable, String> names = new HashMap<>();
		names.put(variable, "Base");
		assertEquals(baseTerm.toString(names, false)
				+ patternSubstitution.toString(names), patternTerm.toString(names));
	}

	@Test
	@DisplayName("find variables in the base term and every substitution")
	void findVariablesInTheBaseTermAndEverySubstitution() {
		Variable baseVariable = new Variable();
		Variable pumpingVariable = new Variable();
		Variable closingVariable = new Variable();
		Function baseTerm = new Function(
				uniqueSymbol("pattern-term-containment", 1),
				List.of(baseVariable));
		Substitution pumping = new Substitution();
		pumping.add(new Variable(), new Function(
				uniqueSymbol("pattern-term-pumping-range", 1),
				List.of(pumpingVariable)));
		Substitution closing = new Substitution();
		closing.add(closingVariable, constant("pattern-term-closing"));
		TestPatternTerm patternTerm = new TestPatternTerm(baseTerm,
				new TestPatternSubstitution(List.of(pumping, closing)));

		assertTrue(patternTerm.contains(baseVariable));
		assertTrue(patternTerm.contains(pumpingVariable));
		assertTrue(patternTerm.contains(closingVariable));
		assertFalse(patternTerm.contains(new Variable()));
	}

	@Test
	@DisplayName("apply pumping before closing when instantiating")
	void applyPumpingBeforeClosingWhenInstantiating() {
		Variable baseVariable = new Variable();
		Variable closingVariable = new Variable();
		FunctionSymbol baseSymbol = uniqueSymbol("pattern-term-base", 1);
		FunctionSymbol pumpingSymbol = uniqueSymbol("pattern-term-pumping", 1);
		Function baseTerm = new Function(baseSymbol, List.of(baseVariable));
		Substitution pumping = new Substitution();
		pumping.add(baseVariable,
				new Function(pumpingSymbol, List.of(baseVariable)));
		pumping.add(closingVariable, constant("pattern-term-wrong-order"));
		Substitution closing = new Substitution();
		closing.add(baseVariable, closingVariable);
		TestPatternTerm patternTerm = new TestPatternTerm(baseTerm,
				new TestPatternSubstitution(List.of(pumping, closing)));

		Term zero = patternTerm.instantiateAt(0);
		Term negative = patternTerm.instantiateAt(-1);
		Term one = patternTerm.instantiateAt(1);
		Term two = patternTerm.instantiateAt(2);

		assertTrue(new Function(baseSymbol, List.of(closingVariable))
				.deepEquals(zero));
		assertTrue(zero.deepEquals(negative));
		assertTrue(new Function(baseSymbol, List.of(
				new Function(pumpingSymbol, List.of(closingVariable))))
				.deepEquals(one));
		assertTrue(new Function(baseSymbol, List.of(
				new Function(pumpingSymbol, List.of(
						new Function(pumpingSymbol, List.of(closingVariable))))))
				.deepEquals(two));
		assertSame(baseVariable, baseTerm.getChild(0));
		assertSame(baseVariable, ((Function) pumping.get(baseVariable)).getChild(0));
	}

	private static Function constant(String prefix) {
		return new Function(uniqueSymbol(prefix, 0), List.of());
	}

	private static FunctionSymbol uniqueSymbol(String prefix, int arity) {
		return FunctionSymbol.intern(prefix + "-" + UUID.randomUUID(), arity);
	}

	private static final class TestPatternTerm extends PatternTerm {

		private TestPatternTerm(
				Term baseTerm, PatternSubstitution patternSubstitution) {
			super(baseTerm, patternSubstitution);
		}

		@Override
		public PatternTerm deepCopy() {
			return null;
		}

		@Override
		public PatternTerm deepCopy(Map<Term, Term> copies) {
			return null;
		}

		@Override
		public PatternSubstitution unifyWith(
				SimplePatternTerm otherPatternTerm) {
			return null;
		}

		@Override
		public Collection<PatternSubstitution> unifyWith(
				PatternRuleLp patternRule) {
			return List.of();
		}
	}

	private static final class TestPatternSubstitution
			extends PatternSubstitution {

		private TestPatternSubstitution(List<Substitution> substitutions) {
			super(substitutions);
		}

		@Override
		public PatternSubstitution composeWith(
				PatternSubstitution otherPatternSubstitution) {
			return null;
		}

		@Override
		public PatternSubstitution deepCopy() {
			return null;
		}

		@Override
		public PatternSubstitution deepCopy(Map<Term, Term> copies) {
			return null;
		}
	}
}
