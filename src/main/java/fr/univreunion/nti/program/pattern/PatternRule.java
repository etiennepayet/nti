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

package fr.univreunion.nti.program.pattern;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A pattern rule resulting from unfolding a program, as defined by E. Payet
 * in <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination
 * of Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class PatternRule {

	/** The left-hand side of this pattern rule. */
	private final SimplePatternTerm left;

	/** The right-hand side of this pattern rule. */
	private final SimplePatternTerm right;

	/** The iteration at which this rule is generated. */
	private final int iteration;

	/**
	 * The nontermination analysis of this rule, including its ground witness and
	 * <code>alpha</code> threshold. For all naturals <code>n &gt;= alpha</code> and
	 * all substitutions <code>theta</code>, <code>p(n)theta</code> starts an
	 * infinite computation, where <code>p</code> denotes the left-hand side.
	 */
	private final PatternNonTerminationAnalysis analysis;

	/**
	 * Attempts to extract a square linear system of equations from the provided
	 * substitutions.
	 *
	 * @param left the substitution on the left-hand side
	 * @param right the substitution on the right-hand side
	 * @return a square linear system, or {@code null} upon failure
	 */
	public static LinearSystem getLinearSystem(Substitution left, Substitution right) {
		return PatternLinearSystemBuilder.tryBuild(left, right);
	}

	/**
	 * Builds a pattern rule with the provided sides and unfolding iteration.
	 *
	 * @param left the left-hand side
	 * @param right the right-hand side
	 * @param iteration the unfolding iteration at which this rule is generated
	 */
	protected PatternRule(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		this.left = left;
		this.right = right;
		this.iteration = iteration;
		this.analysis = PatternNonTerminationAnalyzer.analyze(left, right);
	}

	/**
	 * Builds a pattern rule from precomputed elements. For internal uses only.
	 *
	 * @param left the left-hand side
	 * @param right the right-hand side
	 * @param iteration the unfolding iteration at which this rule is generated
	 * @param nonTerminatingTerm a ground nonterminating term generated from this rule
	 * @param alpha the <code>alpha</code> threshold
	 */
	protected PatternRule(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration, Function nonTerminatingTerm, int alpha) {

		this.left = left;
		this.right = right;
		this.iteration = iteration;
		this.analysis = new PatternNonTerminationAnalysis(nonTerminatingTerm, alpha);
	}

	/**
	 * Returns a flattened deep copy of this pattern rule.
	 *
	 * @return a deep copy of this pattern rule
	 */
	public PatternRule deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a flattened deep copy using the incrementally constructed map.
	 *
	 * @param copies pairs whose values are deep copies of their keys
	 * @return a deep copy of this pattern rule
	 */
	public abstract PatternRule deepCopy(Map<Term, Term> copies);

	/**
	 * Returns the left-hand side.
	 *
	 * @return the left-hand side
	 */
	public SimplePatternTerm getLeft() {
		return this.left;
	}

	/**
	 * Returns the right-hand side.
	 *
	 * @return the right-hand side
	 */
	public SimplePatternTerm getRight() {
		return this.right;
	}

	/**
	 * Returns the unfolding iteration at which this rule is generated.
	 *
	 * @return the unfolding iteration
	 */
	public int getIteration() {
		return this.iteration;
	}

	/**
	 * Returns the <code>alpha</code> threshold.
	 *
	 * @return the <code>alpha</code> threshold
	 */
	public int getAlpha() {
		return this.analysis.alpha();
	}

	/**
	 * Returns the generated ground nonterminating term.
	 *
	 * @return the term, or {@code null} if none could be produced
	 */
	public Function getNonTerminatingTerm() {
		return this.analysis.nonTerminatingTerm();
	}

	/**
	 * Returns a representation relative to the given variable symbols.
	 *
	 * @param variables variable-to-symbol mappings
	 * @return a string representation of this rule
	 */
	public abstract String toString(Map<Variable, String> variables);

	/** Returns a string representation of this rule. */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
