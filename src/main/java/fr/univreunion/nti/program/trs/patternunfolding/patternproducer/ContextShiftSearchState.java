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

package fr.univreunion.nti.program.trs.patternunfolding.patternproducer;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternUtils;

/**
 * The mutable state accumulated while recognizing one context shift.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class ContextShiftSearchState {

	/** The three progressively generalized instances of context <code>c</code>. */
	private Term u1Context;
	private Term u2Context;
	private Term v2Context;

	/** The variables of the recognized context-shift schema. */
	private Variable x1;
	private Variable x2;
	private Variable y2;
	private Variable z2;

	/** The initial term and unary context of the recognized schema. */
	private Term s;
	private Term c1;

	/** The two exponents of the recognized unary context. */
	private int a = -1;
	private int b = -1;

	/**
	 * Builds an empty search state around the three initial context copies.
	 *
	 * @param u1Context the context derived from the candidate in the first rule
	 * @param u2Context the context derived from the second rule's left-hand side
	 * @param v2Context the context derived from the second rule's right-hand side
	 */
	ContextShiftSearchState(
			Term u1Context, Term u2Context, Term v2Context) {
		this.u1Context = u1Context;
		this.u2Context = u2Context;
		this.v2Context = v2Context;
	}

	/**
	 * Checks whether the first search pass found <code>x2</code> and
	 * the initial term <code>s</code>.
	 *
	 * @return <code>true</code> iff <code>x2</code> and <code>s</code>
	 * have been found
	 */
	boolean hasFoundXAndInitialTerm() {
		return this.s != null && this.x2 != null;
	}

	/**
	 * Checks whether a term is distinct from the already recognized
	 * <code>x2</code> and optional <code>z2</code> variables.
	 *
	 * @param term the term to compare
	 * @return <code>true</code> iff the term is neither <code>x2</code>
	 * nor <code>z2</code>
	 */
	boolean isNeitherXNorZ(Term term) {
		return term != this.x2 && term != this.z2;
	}

	/**
	 * Records the optional <code>z2</code> variable of a context shift.
	 *
	 * @param variableAtPosition the variable found in the second rule's
	 * right-hand side
	 * @param v2AtPosition the right-hand side subterm at the position
	 * @param u1CandidateAtPosition the first-rule candidate subterm at
	 * the position
	 * @param u2AtPosition the second rule's left-hand side subterm at
	 * the position
	 * @return <code>true</code> iff the position is compatible with
	 * <code>z2</code>
	 */
	boolean recordZ(
			Variable variableAtPosition,
			Term v2AtPosition,
			Term u1CandidateAtPosition,
			Term u2AtPosition) {

		if (u2AtPosition != v2AtPosition) return false;

		if (this.z2 != null)
			return v2AtPosition == this.z2 &&
					u1CandidateAtPosition == this.x2;

		if ((this.x2 != null && this.x2 == v2AtPosition) ||
				!(u1CandidateAtPosition instanceof Variable))
			return false;

		this.z2 = variableAtPosition;
		this.x1 = (Variable) u1CandidateAtPosition;
		return true;
	}

	/**
	 * Records the <code>x2</code> variable, initial term <code>s</code>,
	 * context <code>c1</code>, and exponent <code>a</code> of a context shift.
	 *
	 * @param variableAtPosition the variable found in the second rule's
	 * right-hand side
	 * @param u1CandidateAtPosition the first-rule candidate subterm at
	 * the position
	 * @param u2AtPosition the second rule's left-hand side subterm at
	 * the position
	 * @return <code>true</code> iff the position is compatible with
	 * <code>x2</code>
	 */
	boolean recordX(
			Variable variableAtPosition,
			Term u1CandidateAtPosition,
			Term u2AtPosition) {

		int[] aAtPosition = new int[1];
		Term c1AtPosition = PatternUtils.getContext(
				u2AtPosition, variableAtPosition, aAtPosition);
		if (c1AtPosition == null) return false;

		if (this.x2 != null)
			return variableAtPosition == this.x2 &&
					c1AtPosition.deepEquals(this.c1) &&
					aAtPosition[0] == this.a &&
					u1CandidateAtPosition.deepEquals(this.s);

		if (this.z2 != null && this.z2 == variableAtPosition)
			return false;

		this.x2 = variableAtPosition;
		this.c1 = c1AtPosition;
		this.a = aAtPosition[0];
		this.s = u1CandidateAtPosition;
		return true;
	}

	/**
	 * Records the <code>y2</code> and <code>x1</code> variables and exponent
	 * <code>b</code> of a context shift.
	 *
	 * @param variableAtPosition the variable found in the second rule's
	 * left-hand side
	 * @param u1CandidateAtPosition the first-rule candidate subterm at
	 * the position
	 * @param v2AtPosition the second rule's right-hand side subterm at
	 * the position
	 * @return <code>true</code> iff the position is compatible with
	 * <code>y2</code>
	 */
	boolean recordY(
			Variable variableAtPosition,
			Term u1CandidateAtPosition,
			Term v2AtPosition) {

		int[] bAtPosition = new int[1];
		Term c1AtPosition = PatternUtils.getContext(
				v2AtPosition, variableAtPosition, bAtPosition);
		if (c1AtPosition == null ||
				!c1AtPosition.isVariantOf(this.c1))
			return false;

		if (this.y2 != null)
			return variableAtPosition == this.y2 &&
					bAtPosition[0] == this.b &&
					u1CandidateAtPosition == this.x1;

		this.y2 = variableAtPosition;
		this.b = bAtPosition[0];

		if (this.x1 != null)
			return u1CandidateAtPosition == this.x1;

		this.x1 = (Variable) u1CandidateAtPosition;
		return true;
	}

	/**
	 * Checks whether the completed search found the expected variables
	 * and a shared context that does not contain <code>x1</code> in
	 * the initial term.
	 *
	 * @return <code>true</code> iff the search state is accepted
	 */
	boolean hasAcceptedContext() {
		return this.x1 != null && this.y2 != null &&
				!this.s.contains(this.x1) &&
				this.u1Context.deepEquals(this.u2Context) &&
				this.u1Context.deepEquals(this.v2Context);
	}

	/**
	 * Checks whether a term contains a variable of the recognized
	 * context-shift schema.
	 *
	 * @param term the term to inspect
	 * @return <code>true</code> iff <code>term</code> contains
	 * <code>x1</code>, <code>x2</code>, <code>y2</code>, or the optional
	 * <code>z2</code>
	 */
	boolean hasSchemaVariableIn(Term term) {
		Set<Variable> schemaVariables = new HashSet<>();
		schemaVariables.add(this.x1);
		schemaVariables.add(this.x2);
		schemaVariables.add(this.y2);
		if (this.z2 != null) schemaVariables.add(this.z2);

		schemaVariables.retainAll(term.getVariables());
		return !schemaVariables.isEmpty();
	}

	/**
	 * Builds the pattern-function symbol shared by both sides of the
	 * produced rule.
	 *
	 * @return the shared pattern-function symbol
	 */
	HatFunctionSymbol buildPatternFunctionSymbol() {
		return HatFunctionSymbol.intern(this.c1, this.x2);
	}

	/**
	 * Replaces the candidate position with the context derived from the
	 * second rule's left-hand side, then deeply copies the resulting term.
	 *
	 * @param cPrime the outer context of the first rule
	 * @param candidatePosition the position of the context-shift candidate
	 * @param copies the copy map
	 * @return the copied left-hand side term
	 */
	Term deepCopyLeftTerm(
			Term cPrime,
			Position candidatePosition,
			Map<Term, Term> copies) {

		return cPrime.replace(candidatePosition, this.u2Context)
				.deepCopy(copies);
	}

	/**
	 * Builds the pattern substitution for the left-hand side of the
	 * produced rule.
	 *
	 * @param symbol the shared pattern-function symbol
	 * @return the left-hand side pattern substitution
	 */
	Substitution buildLeftTheta(HatFunctionSymbol symbol) {
		Substitution theta = new Substitution();
		theta.add(this.x2, new HatFunction(symbol, this.s, this.a, 0));
		if (this.z2 != null)
			theta.add(this.z2, new HatFunction(symbol, this.y2, this.b, 0));

		return theta;
	}

	/**
	 * Builds the pattern substitution for the right-hand side of the
	 * produced rule.
	 *
	 * @param symbol the shared pattern-function symbol
	 * @return the right-hand side pattern substitution
	 */
	Substitution buildRightTheta(HatFunctionSymbol symbol) {
		Substitution theta = new Substitution();
		theta.add(this.x1, new HatFunction(symbol, this.y2, this.b, 0));
		return theta;
	}

	/**
	 * Replaces a position in the context derived from the first rule
	 * with <code>z2</code> when needed.
	 *
	 * @param position the position to replace
	 * @param currentTerm the current term at the position
	 */
	void replaceU1ContextWithZIfDifferent(
			Position position,
			Term currentTerm) {

		this.u1Context = replaceContextIfDifferent(
				this.u1Context, position, currentTerm, this.z2);
	}

	/**
	 * Replaces a position in the context derived from the first rule
	 * with <code>x2</code> when needed.
	 *
	 * @param position the position to replace
	 * @param currentTerm the current term at the position
	 */
	void replaceU1ContextWithXIfDifferent(
			Position position,
			Term currentTerm) {

		this.u1Context = replaceContextIfDifferent(
				this.u1Context, position, currentTerm, this.x2);
	}

	/**
	 * Replaces a position in the context derived from the second rule's
	 * left-hand side with <code>x2</code> when needed.
	 *
	 * @param position the position to replace
	 * @param currentTerm the current term at the position
	 */
	void replaceU2ContextWithXIfDifferent(
			Position position,
			Term currentTerm) {

		this.u2Context = replaceContextIfDifferent(
				this.u2Context, position, currentTerm, this.x2);
	}

	/**
	 * Replaces a position in the context derived from the first rule
	 * with <code>y2</code> when needed.
	 *
	 * @param position the position to replace
	 * @param currentTerm the current term at the position
	 */
	void replaceU1ContextWithYIfDifferent(
			Position position,
			Term currentTerm) {

		this.u1Context = replaceContextIfDifferent(
				this.u1Context, position, currentTerm, this.y2);
	}

	/**
	 * Replaces a position in the context derived from the second rule's
	 * right-hand side with <code>y2</code> when needed.
	 *
	 * @param position the position to replace
	 * @param currentTerm the current term at the position
	 */
	void replaceV2ContextWithYIfDifferent(
			Position position,
			Term currentTerm) {

		this.v2Context = replaceContextIfDifferent(
				this.v2Context, position, currentTerm, this.y2);
	}

	/**
	 * Replaces a position in a context unless the term at that position
	 * already is the replacement variable.
	 *
	 * @param context the context to update
	 * @param position the position to replace
	 * @param currentTerm the current term at the position
	 * @param replacement the replacement variable
	 * @return the updated context
	 */
	private static Term replaceContextIfDifferent(
			Term context,
			Position position,
			Term currentTerm,
			Variable replacement) {

		return currentTerm == replacement
				? context
				: context.replace(position, replacement);
	}
}
