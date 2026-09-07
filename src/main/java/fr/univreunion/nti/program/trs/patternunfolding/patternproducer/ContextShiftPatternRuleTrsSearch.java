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

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Searches for a pattern rule produced from one context-shift candidate.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class ContextShiftPatternRuleTrsSearch {
	/**
	 * Attempts to build a pattern rule from one context-shift
	 * candidate in the left-hand side of <code>r1</code>.
	 * <p>
	 * More precisely, this method considers the following
	 * situations:
	 * <ol>
	 * <li>
	 * <code>r1 = c'(c(s, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2) -> c(x2, c1^b(y2))</code>
	 * </li>
	 * <li>
	 * <code>r1 = c'(c(s, x1, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2, z2) -> c(x2, c1^b(y2), z2)</code>
	 * </li>
	 * </ol>
	 * where
	 * <code>x1, x2, y2, z2</code> are variables,
	 * <code>x2, y2, z2</code> are distinct and
	 * do not occur in <code>c', c, c1</code>,
	 * <code>x1</code> does not occur in
	 * <code>c', c, c1, s</code>,
	 * <code>a, b</code> are non-zero naturals.
	 * <p>
	 * The provided term <code>u1Candidate</code> is a
	 * non-variable subterm of the left-hand side of
	 * <code>r1</code>. It corresponds to a candidate
	 * for the subterm <code>c(s,x_1)</code> or
	 * <code>c(s,x_1,x_1)</code>.
	 *
	 * @param r1 the TRS rule whose left-hand side contains
	 * the candidate
	 * @param r2 the TRS rule used to validate the candidate
	 * @param candidatePosition a non-variable position in the
	 * left-hand side of <code>r1</code>
	 * @param u1Candidate the subterm of the left-hand
	 * of <code>r1</code> at position <code>candidatePosition</code>
	 * @return the pattern rule
	 * <code>c'(c(c1^{a,0}(s), y2)) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * or
	 * <code>c'(c(c1^{a,0}(s), y2, c1^{b,0}(y2))) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * depending on the situation, or <code>null</code>
	 * if no such rule can be built
	 */
	static PatternRuleTrs tryBuild(
			RuleTrs r1,
			RuleTrs r2,
			Position candidatePosition,
			Term u1Candidate) {

		// We only consider the following particular case:
		// - c and c1 are ground
		// - c' consists of only one occurrence of \square_1.

		// It is supposed that u1Candidate is a non-variable
		// subterm of the left-hand side of r1.

		Function u2   = r2.getLeft();
		Term     v2   = r2.getRight();

		FunctionSymbol candidateRootSymbol = u1Candidate.getRootSymbol();
		if (u2.getRootSymbol() != candidateRootSymbol ||
				v2.getRootSymbol() != candidateRootSymbol)
			return null;

		ContextShiftSearchState search =
				new ContextShiftSearchState(
						u1Candidate.shallowCopy(),
						u2.shallowCopy(),
						v2.shallowCopy());

		if (!findXAndZ(u1Candidate, u2, v2, search)) return null;

		// Here, we are sure that if z2 has been determined
		// then it is distinct from x2.
		// However, we must ensure that s and x2 have been
		// determined.
		if (!search.hasFoundXAndInitialTerm()) return null;

		if (!findY(u1Candidate, u2, v2, search)) return null;

		// Finally, we check if we have found x1 and y2.
		// We also check if x1 occurs in s and if u1
		// corresponds to the same context c as u2 and v2.
		if (!search.hasAcceptedContext()) return null;
		// We know here that x2, y2 and z2 are distinct variables.

		return tryBuildPatternRule(r1, candidatePosition, search);
	}

	/**
	 * Builds a pattern rule from an accepted context-shift search.
	 *
	 * @param r1 the TRS rule from which the pattern rule is built
	 * @param candidatePosition the position of the context-shift candidate
	 * in the left-hand side of <code>r1</code>
	 * @param search the accepted context-shift search state
	 * @return the pattern rule, or <code>null</code> if it cannot be built
	 */
	private static PatternRuleTrs tryBuildPatternRule(
			RuleTrs r1,
			Position candidatePosition,
			ContextShiftSearchState search) {

		// We also compute cPrime.
		Variable hole = new Variable();
		Term cPrime = r1.getLeft().replace(candidatePosition, hole);
		// We check if cPrime contains x1, x2, y2 or z2.
		if (search.hasSchemaVariableIn(cPrime)) return null;

		HatFunctionSymbol patternFunctionSymbol =
				search.buildPatternFunctionSymbol();
		// The pattern substitution on the left-hand side
		// of the produced pattern rule:
		Substitution leftTheta =
				search.buildLeftTheta(patternFunctionSymbol);
		// The pattern substitution on the right-hand side
		// of the produced pattern rule:
		Substitution rightTheta =
				search.buildRightTheta(patternFunctionSymbol);

		Map<Term, Term> copies = new HashMap<>();
		SimplePatternSubstitution leftEta =
				SimplePatternSubstitution.tryBuildTakingOwnership(
						leftTheta.deepCopy(copies));
		SimplePatternSubstitution rightEta =
				SimplePatternSubstitution.tryBuildTakingOwnership(
						rightTheta.deepCopy(copies));
		if (leftEta != null)
			return PatternRuleTrs.tryBuild(
					SimplePatternTerm.tryBuild(
							search.deepCopyLeftTerm(
									cPrime, candidatePosition, copies),
							leftEta),
					SimplePatternTerm.tryBuild(r1.getRight().deepCopy(copies), rightEta),
					0);

		return null;
	}


	/**
	 * Finds <code>x2</code>, the optional <code>z2</code>, the initial term
	 * <code>s</code>, the shared context <code>c1</code>, and exponent
	 * <code>a</code>.
	 *
	 * @param u1Candidate the candidate subterm of the first rule
	 * @param u2 the left-hand side of the second rule
	 * @param v2 the right-hand side of the second rule
	 * @param search the search state to complete
	 * @return <code>true</code> iff all visited positions are compatible
	 */
	private static boolean findXAndZ(
			Term u1Candidate,
			Function u2,
			Term v2,
			ContextShiftSearchState search) {
		// First, we look for x2 and z2 in v2.
		for (Position position : v2) {
			if (!recordXOrZAtPosition(
					position, u1Candidate, u2, v2, search))
				return false;
		}

		return true;
	}

	/**
	 * Records <code>x2</code> or <code>z2</code> at one position of the
	 * second rule's right-hand side.
	 *
	 * @param position the inspected position
	 * @param u1Candidate the candidate subterm of the first rule
	 * @param u2 the left-hand side of the second rule
	 * @param v2 the right-hand side of the second rule
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with
	 * <code>x2</code> or <code>z2</code>
	 */
	private static boolean recordXOrZAtPosition(
			Position position,
			Term u1Candidate,
			Function u2,
			Term v2,
			ContextShiftSearchState search) {

		Term v2AtPosition = v2.get(position);
		if (!(v2AtPosition instanceof Variable variableAtPosition)) return true;

		// Here, v2AtPosition should be x2 or z2.

		Term u1CandidateAtPosition = u1Candidate.get(position);
		// We only consider positions of v2
		// that are also positions of u1.
		if (u1CandidateAtPosition == null) return true;

		Term u2AtPosition = u2.get(position);
		// We only consider positions of v2
		// that are also positions of u2.
		if (u2AtPosition == null) return true;

		if (u2AtPosition instanceof Variable)
			return recordZAtPosition(
					position,
					variableAtPosition,
					v2AtPosition,
					u1CandidateAtPosition,
					u2AtPosition,
					search);

		return recordXAtPosition(
				position,
				variableAtPosition,
				u1CandidateAtPosition,
				u2AtPosition,
				search);
	}

	/**
	 * Records <code>z2</code> at one position of the second rule's
	 * right-hand side.
	 *
	 * @param position the inspected position
	 * @param variableAtPosition the variable found in the second rule's
	 * right-hand side
	 * @param v2AtPosition the right-hand side subterm at the position
	 * @param u1CandidateAtPosition the first-rule candidate subterm at
	 * the position
	 * @param u2AtPosition the second rule's left-hand side subterm at
	 * the position
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with
	 * <code>z2</code>
	 */
	private static boolean recordZAtPosition(
			Position position,
			Variable variableAtPosition,
			Term v2AtPosition,
			Term u1CandidateAtPosition,
			Term u2AtPosition,
			ContextShiftSearchState search) {

		if (!search.recordZ(
				variableAtPosition,
				v2AtPosition,
				u1CandidateAtPosition,
				u2AtPosition))
			return false;

		// We complete c.
		search.replaceU1ContextWithZIfDifferent(
				position, u1CandidateAtPosition);
		return true;
	}

	/**
	 * Records <code>x2</code> at one position of the second rule's
	 * right-hand side.
	 *
	 * @param position the inspected position
	 * @param variableAtPosition the variable found in the second rule's
	 * right-hand side
	 * @param u1CandidateAtPosition the first-rule candidate subterm at
	 * the position
	 * @param u2AtPosition the second rule's left-hand side subterm at
	 * the position
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with
	 * <code>x2</code>
	 */
	private static boolean recordXAtPosition(
			Position position,
			Variable variableAtPosition,
			Term u1CandidateAtPosition,
			Term u2AtPosition,
			ContextShiftSearchState search) {

		if (!search.recordX(
				variableAtPosition,
				u1CandidateAtPosition,
				u2AtPosition))
			return false;

		// We complete c.
		search.replaceU1ContextWithXIfDifferent(
				position, u1CandidateAtPosition);
		search.replaceU2ContextWithXIfDifferent(
				position, u2AtPosition);
		return true;
	}

	/**
	 * Finds <code>y2</code>, <code>x1</code>, and exponent <code>b</code>,
	 * then completes the instances of the shared context <code>c</code>.
	 *
	 * @param u1Candidate the candidate subterm of the first rule
	 * @param u2 the left-hand side of the second rule
	 * @param v2 the right-hand side of the second rule
	 * @param search the search state to complete
	 * @return <code>true</code> iff all visited positions are compatible
	 */
	private static boolean findY(
			Term u1Candidate,
			Function u2,
			Term v2,
			ContextShiftSearchState search) {
		// Then, we look for y2.
		for (Position position : u2) {
			if (!recordYAtPosition(
					position, u1Candidate, u2, v2, search))
				return false;
		}

		return true;
	}

	/**
	 * Records <code>y2</code> at one position of the second rule's
	 * left-hand side and completes the corresponding context instances.
	 *
	 * @param position the inspected position
	 * @param u1Candidate the candidate subterm of the first rule
	 * @param u2 the left-hand side of the second rule
	 * @param v2 the right-hand side of the second rule
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with
	 * <code>y2</code>
	 */
	private static boolean recordYAtPosition(
			Position position,
			Term u1Candidate,
			Function u2,
			Term v2,
			ContextShiftSearchState search) {

		Term u2AtPosition = u2.get(position);
		if (!(u2AtPosition instanceof Variable variableAtPosition) ||
				!search.isNeitherXNorZ(u2AtPosition))
			return true;

		// Here, u2AtPosition should be y2.
		// Moreover, y2 must be distinct from x2 and z2.
		Term u1CandidateAtPosition = u1Candidate.get(position);
		// We only consider positions of u2 that
		// are also positions of u1.
		// Moreover, the candidate subterm at this
		// position should be a variable.
		if (!(u1CandidateAtPosition instanceof Variable)) return false;

		Term v2AtPosition = v2.get(position);
		// We only consider positions of u2
		// that are also positions of v2.
		if (v2AtPosition == null) return false;

		if (!search.recordY(
				variableAtPosition,
				u1CandidateAtPosition,
				v2AtPosition))
			return false;

		// We complete c.
		search.replaceU1ContextWithYIfDifferent(
				position, u1CandidateAtPosition);
		search.replaceV2ContextWithYIfDifferent(
				position, v2AtPosition);
		return true;
	}

	/** Prevents instantiation. */
	private ContextShiftPatternRuleTrsSearch() {}
}
