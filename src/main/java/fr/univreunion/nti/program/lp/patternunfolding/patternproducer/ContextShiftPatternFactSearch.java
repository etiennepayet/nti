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

package fr.univreunion.nti.program.lp.patternunfolding.patternproducer;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternUtils;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Search for pattern facts built from a binary rule that shifts terms
 * through a common unary context.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class ContextShiftPatternFactSearch {

	/**
	 * Attempts to build a context-shift pattern fact.
	 *
	 * @param u1 the head of the fact
	 * @param u2 the head of the binary rule
	 * @param v2 the body atom of the binary rule
	 * @return the pattern fact, or <code>null</code> if no such fact
	 * can be built
	 */
	static PatternRuleLp tryBuild(Function u1, Function u2, Function v2) {
		ContextShiftSearchState search =
				new ContextShiftSearchState(
						u1.shallowCopy(),
						u2.shallowCopy(),
						v2.shallowCopy());

		// First, we look for x and z in v2.
		if (!findXAndZ(u1, u2, v2, search))
			return null;

		// Here, at least x should be determined.
		if (!search.hasFoundX())
			return null;

		// Then, we look for y.
		if (!findY(u1, u2, v2, search))
			return null;

		// Finally, we check if we have found x and y
		// and if u1 corresponds to the same context
		// c as u2 and v2.
		if (!search.hasAcceptedContext())
			return null;

		return tryBuildPatternFact(search);
	}

	/**
	 * Builds the pattern fact from an accepted context-shift search.
	 *
	 * @param search the accepted context-shift search state
	 * @return the pattern fact, or <code>null</code> if it cannot be built
	 */
	private static PatternRuleLp tryBuildPatternFact(
			ContextShiftSearchState search) {

		Substitution theta = search.buildTheta();
		Map<Term, Term> copies = new HashMap<>();
		SimplePatternSubstitution eta =
				SimplePatternSubstitution.tryBuildTakingOwnership(
						theta.deepCopy(copies));
		if (eta == null)
			return null;

		return PatternRuleLp.tryBuildFact(
				SimplePatternTerm.tryBuild(
						search.deepCopyU2Context(copies),
						eta),
				0);
	}

	/**
	 * Finds the variables x and z, the ground term s, the shared
	 * context c1, and exponent a for a context-shift pattern fact.
	 *
	 * @param u1 the head of the fact
	 * @param u2 the head of the binary rule
	 * @param v2 the body atom of the binary rule
	 * @param search the search state to complete
	 * @return <code>true</code> iff the positions visited in v2 are
	 * compatible with the context-shift shape
	 */
	private static boolean findXAndZ(
			Function u1,
			Function u2,
			Function v2,
			ContextShiftSearchState search) {

		for (Position position : v2) {
			if (!recordXOrZAtPosition(
					position,
					u1,
					u2,
					v2,
					search))
				return false;
		}

		return true;
	}

	/**
	 * Records x or z at one position of v2 for a context-shift pattern fact.
	 *
	 * @param position the inspected position
	 * @param u1 the head of the fact
	 * @param u2 the head of the binary rule
	 * @param v2 the body atom of the binary rule
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with x or z
	 */
	private static boolean recordXOrZAtPosition(
			Position position,
			Function u1,
			Function u2,
			Function v2,
			ContextShiftSearchState search) {

		Term v2AtPosition = v2.get(position);
		if (!(v2AtPosition instanceof Variable variableAtPosition))
			return true;

		// Here, v2AtPosition should be x or z.

		Term u1AtPosition = u1.get(position);
		// We only consider positions of v2
		// that are also positions of u1.
		if (u1AtPosition == null)
			return true;

		Term u2AtPosition = u2.get(position);
		// We only consider positions of v2
		// that are also positions of u2.
		if (u2AtPosition == null)
			return true;

		if (u2AtPosition instanceof Variable)
			return recordZAtPosition(
					position,
					variableAtPosition,
					v2AtPosition,
					u1AtPosition,
					u2AtPosition,
					search);

		return recordXAtPosition(
				position,
				variableAtPosition,
				u1AtPosition,
				u2AtPosition,
				search);
	}

	/**
	 * Records z at one position of v2 for a context-shift pattern fact.
	 *
	 * @param position the inspected position
	 * @param variableAtPosition the variable found in v2
	 * @param v2AtPosition the subterm of v2 at the inspected position
	 * @param u1AtPosition the subterm of u1 at the inspected position
	 * @param u2AtPosition the subterm of u2 at the inspected position
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with z
	 */
	private static boolean recordZAtPosition(
			Position position,
			Variable variableAtPosition,
			Term v2AtPosition,
			Term u1AtPosition,
			Term u2AtPosition,
			ContextShiftSearchState search) {

		if (!recordZ(
				variableAtPosition,
				v2AtPosition,
				u1AtPosition,
				u2AtPosition,
				search))
			return false;

		// We complete c.
		search.replaceU1ContextIfDifferent(
				position,
				u1AtPosition,
				search.z);
		return true;
	}

	/**
	 * Records x at one position of v2 for a context-shift pattern fact.
	 *
	 * @param position the inspected position
	 * @param variableAtPosition the variable found in v2
	 * @param u1AtPosition the subterm of u1 at the inspected position
	 * @param u2AtPosition the subterm of u2 at the inspected position
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with x
	 */
	private static boolean recordXAtPosition(
			Position position,
			Variable variableAtPosition,
			Term u1AtPosition,
			Term u2AtPosition,
			ContextShiftSearchState search) {

		if (!recordX(
				variableAtPosition,
				u1AtPosition,
				u2AtPosition,
				search))
			return false;

		// We complete c.
		search.replaceU1ContextIfDifferent(
				position,
				u1AtPosition,
				search.x);
		search.replaceU2ContextIfDifferent(
				position,
				u2AtPosition,
				search.x);
		return true;
	}

	/**
	 * Finds the variable y and exponent b for a context-shift
	 * pattern fact.
	 *
	 * @param u1 the head of the fact
	 * @param u2 the head of the binary rule
	 * @param v2 the body atom of the binary rule
	 * @param search the search state to complete
	 * @return <code>true</code> iff the positions visited in u2 are
	 * compatible with the context-shift shape
	 */
	private static boolean findY(
			Function u1,
			Function u2,
			Function v2,
			ContextShiftSearchState search) {

		for (Position position : u2) {
			Term u2AtPosition = u2.get(position);
			if (!(u2AtPosition instanceof Variable variableAtPosition) ||
					u2AtPosition == search.x ||
					u2AtPosition == search.z)
				continue;

			// Here, u2AtPosition should be y.

			Term u1AtPosition = u1.get(position);
			// We only consider positions of u2 that
			// are also positions of u1.
			// Moreover, u1AtPosition should be a variable.
			if (!(u1AtPosition instanceof Variable))
				return false;

			Term v2AtPosition = v2.get(position);
			// We only consider positions of u2
			// that are also positions of v2.
			if (v2AtPosition == null)
				return false;

			if (!recordY(
					variableAtPosition,
					u1AtPosition,
					v2AtPosition,
					search))
				return false;

			// We complete c.
			search.replaceU1ContextIfDifferent(
					position,
					u1AtPosition,
					search.y);
			search.replaceV2ContextIfDifferent(
					position,
					v2AtPosition,
					search.y);
		}

		return true;
	}

	/**
	 * Records the y variable and exponent b of a context-shift
	 * pattern fact.
	 *
	 * @param variableAtPosition the variable found in u2
	 * @param u1AtPosition the subterm of u1 at the inspected position
	 * @param v2AtPosition the subterm of v2 at the inspected position
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with y
	 */
	private static boolean recordY(
			Variable variableAtPosition,
			Term u1AtPosition,
			Term v2AtPosition,
			ContextShiftSearchState search) {

		// Here, variableAtPosition should be y.
		int[] exponentAtPosition = new int[1];
		Term contextAtPosition =
				PatternUtils.getContext(
						v2AtPosition,
						variableAtPosition,
						exponentAtPosition);

		if (contextAtPosition == null ||
				!contextAtPosition.isVariantOf(search.c1))
			return false;

		if (search.y != null)
			return variableAtPosition == search.y &&
					exponentAtPosition[0] == search.b &&
					u1AtPosition == search.xx;

		// Here, y had not been found already.
		search.y = variableAtPosition;
		search.b = exponentAtPosition[0];

		if (search.xx != null)
			return u1AtPosition == search.xx;

		search.xx = (Variable) u1AtPosition;
		return true;
	}

	/**
	 * Records the optional z variable of a context-shift pattern fact.
	 *
	 * @param variableAtPosition the variable found in v2
	 * @param v2AtPosition the subterm of v2 at the inspected position
	 * @param u1AtPosition the subterm of u1 at the inspected position
	 * @param u2AtPosition the subterm of u2 at the inspected position
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with z
	 */
	private static boolean recordZ(
			Variable variableAtPosition,
			Term v2AtPosition,
			Term u1AtPosition,
			Term u2AtPosition,
			ContextShiftSearchState search) {

		// Here, v2AtPosition should be z.
		if (u2AtPosition != v2AtPosition)
			return false;

		if (search.z != null)
			return v2AtPosition == search.z && u1AtPosition == search.xx;

		if (!(u1AtPosition instanceof Variable u1Variable))
			return false;

		search.z = variableAtPosition;
		search.xx = u1Variable;
		return true;
	}

	/**
	 * Records the x variable, ground term s, context c1, and exponent
	 * a of a context-shift pattern fact.
	 *
	 * @param variableAtPosition the variable found in v2
	 * @param u1AtPosition the subterm of u1 at the inspected position
	 * @param u2AtPosition the subterm of u2 at the inspected position
	 * @param search the search state to complete
	 * @return <code>true</code> iff the position is compatible with x
	 */
	private static boolean recordX(
			Variable variableAtPosition,
			Term u1AtPosition,
			Term u2AtPosition,
			ContextShiftSearchState search) {

		// Here, variableAtPosition should be x.
		int[] exponentAtPosition = new int[1];
		Term contextAtPosition =
				PatternUtils.getContext(
						u2AtPosition,
						variableAtPosition,
						exponentAtPosition);

		if (contextAtPosition == null)
			return false;

		if (search.x != null)
			return variableAtPosition == search.x &&
					contextAtPosition.deepEquals(search.c1) &&
					exponentAtPosition[0] == search.a &&
					u1AtPosition.deepEquals(search.s);

		// Here, x had not been found already.
		if (!u1AtPosition.isGround())
			return false;

		search.x = variableAtPosition;
		search.c1 = contextAtPosition;
		search.a = exponentAtPosition[0];
		search.s = u1AtPosition;
		return true;
	}

	/**
	 * Mutable state for context-shift pattern-fact recognition.
	 */
	private static final class ContextShiftSearchState {

		/**
		 * The context c we are looking for, computed from u1.
		 */
		private Term u1Context;

		/**
		 * The context c we are looking for, computed from u2.
		 */
		private Term u2Context;

		/**
		 * The context c we are looking for, computed from v2.
		 */
		private Term v2Context;

		/**
		 * The variables x, y, z, x' we are looking for.
		 */
		private Variable x;
		private Variable y;
		private Variable z;
		private Variable xx;

		/**
		 * The ground term s we are looking for.
		 */
		private Term s;

		/**
		 * The context c1 we are looking for.
		 */
		private Term c1;

		/**
		 * The exponents a,b we are looking for.
		 */
		private int a = -1;
		private int b = -1;

		/**
		 * Builds a context-shift search state.
		 *
		 * @param u1Context the initial u1 context
		 * @param u2Context the initial u2 context
		 * @param v2Context the initial v2 context
		 */
		private ContextShiftSearchState(
				Term u1Context,
				Term u2Context,
				Term v2Context) {

			this.u1Context = u1Context;
			this.u2Context = u2Context;
			this.v2Context = v2Context;
		}

		/**
		 * Checks whether the first pass found x.
		 *
		 * @return <code>true</code> iff x has been found
		 */
		private boolean hasFoundX() {
			return this.x != null;
		}

		/**
		 * Checks whether the completed search found the expected variables
		 * and a shared context.
		 *
		 * @return <code>true</code> iff the search state is accepted
		 */
		private boolean hasAcceptedContext() {
			return this.x != null && this.y != null &&
					this.u1Context.deepEquals(this.u2Context) &&
					this.u1Context.deepEquals(this.v2Context);
		}

		/**
		 * Builds the pumping substitution for the accepted context shift.
		 *
		 * @return the pumping substitution
		 */
		private Substitution buildTheta() {
			HatFunctionSymbol symb = HatFunctionSymbol.intern(this.c1, this.x);
			Substitution theta = new Substitution();
			theta.add(this.x, new HatFunction(symb, this.s, this.a, 0));
			if (this.z != null)
				theta.add(this.z, new HatFunction(symb, this.y, this.b, 0));

			return theta;
		}

		/**
		 * Copies the u2-derived context using the provided copy map.
		 *
		 * @param copies the copy map
		 * @return a deep copy of the u2-derived context
		 */
		private Term deepCopyU2Context(Map<Term, Term> copies) {
			return this.u2Context.deepCopy(copies);
		}

		/**
		 * Replaces a position in the u1-derived context when needed.
		 *
		 * @param position the position to replace
		 * @param currentTerm the current term at the position
		 * @param replacement the replacement variable
		 */
		private void replaceU1ContextIfDifferent(
				Position position,
				Term currentTerm,
				Variable replacement) {

			this.u1Context = replaceContextIfDifferent(
					this.u1Context,
					position,
					currentTerm,
					replacement);
		}

		/**
		 * Replaces a position in the u2-derived context when needed.
		 *
		 * @param position the position to replace
		 * @param currentTerm the current term at the position
		 * @param replacement the replacement variable
		 */
		private void replaceU2ContextIfDifferent(
				Position position,
				Term currentTerm,
				Variable replacement) {

			this.u2Context = replaceContextIfDifferent(
					this.u2Context,
					position,
					currentTerm,
					replacement);
		}

		/**
		 * Replaces a position in the v2-derived context when needed.
		 *
		 * @param position the position to replace
		 * @param currentTerm the current term at the position
		 * @param replacement the replacement variable
		 */
		private void replaceV2ContextIfDifferent(
				Position position,
				Term currentTerm,
				Variable replacement) {

			this.v2Context = replaceContextIfDifferent(
					this.v2Context,
					position,
					currentTerm,
					replacement);
		}

		/**
		 * Replaces a position in a context when needed.
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

			if (currentTerm == replacement)
				return context;

			return context.replace(position, replacement);
		}
	}

	/**
	 * Disables construction.
	 */
	private ContextShiftPatternFactSearch() {
	}
}
