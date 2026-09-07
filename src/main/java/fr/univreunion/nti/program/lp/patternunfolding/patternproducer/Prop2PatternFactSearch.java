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
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Searches for pattern facts obtained by applying Proposition 2 of E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025, to a fact and a binary rule.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class Prop2PatternFactSearch {

	/**
	 * Attempts to build a Proposition 2 pattern fact.
	 *
	 * @param u1 the head of the fact
	 * @param u2 the head of the binary rule
	 * @param v2 the body atom of the binary rule
	 * @return the pattern fact, or <code>null</code> if no such fact
	 * can be built
	 */
	static PatternRuleLp tryBuild(Function u1, Function u2, Function v2) {
		Prop2FactSearchState search =
				new Prop2FactSearchState(u1.shallowCopy(), u2.shallowCopy());

		// First, we complete sigma and mu.
		if (!search.completeSubstitutionsAndContexts(u1, u2, v2))
			return null;

		// Then, we check whether sigma is suitable
		// and u1 corresponds to the same context c
		// as u2 and v2.
		if (!search.isAccepted(v2))
			return null;

		// Here, the pair (r1,r2) satisfies the conditions
		// of Prop. 2 of [Payet, ICLP'25]. Hence, we can
		// produce a pattern fact from it.

		Map<Term, Term> copies = new HashMap<>();
		return PatternRuleLp.tryBuildFact(
				SimplePatternTerm.tryBuild(v2.deepCopy(copies),
						search.sigma.deepCopy(copies),
						search.mu.deepCopy(copies)),
				0);
	}

	/**
	 * Mutable state for Proposition 2 pattern-fact recognition.
	 */
	private static final class Prop2FactSearchState {

		/**
		 * The pumping substitution of the returned pattern fact.
		 */
		private final Substitution sigma = new Substitution();

		/**
		 * The closing substitution of the returned pattern fact.
		 */
		private final Substitution mu = new Substitution();

		/**
		 * The variables that sigma maps to themselves.
		 */
		private final Set<Variable> identityVariables = new HashSet<>();

		/**
		 * The context c computed from u1.
		 */
		private Term u1Context;

		/**
		 * The context c computed from u2.
		 */
		private Term u2Context;

		/**
		 * Builds a Proposition 2 search state.
		 *
		 * @param u1Context the initial u1 context
		 * @param u2Context the initial u2 context
		 */
		private Prop2FactSearchState(Term u1Context, Term u2Context) {
			this.u1Context = u1Context;
			this.u2Context = u2Context;
		}

		/**
		 * Completes the substitutions and contexts from all positions in v2.
		 *
		 * @param u1 the fact head
		 * @param u2 the binary-rule head
		 * @param v2 the binary-rule body atom
		 * @return <code>true</code> iff all inspected positions are compatible
		 */
		private boolean completeSubstitutionsAndContexts(
				Function u1,
				Function u2,
				Function v2) {

			for (Position position : v2)
				if (!this.completeAtPosition(position, u1, u2, v2))
					return false;

			return true;
		}

		/**
		 * Completes the substitutions and contexts at one position of v2.
		 *
		 * @param position the inspected position
		 * @param u1 the fact head
		 * @param u2 the binary-rule head
		 * @param v2 the binary-rule body atom
		 * @return <code>true</code> iff the position is compatible
		 */
		private boolean completeAtPosition(
				Position position,
				Function u1,
				Function u2,
				Function v2) {

			Term u1AtPosition = u1.get(position);
			// We only consider positions of v2
			// that are also positions of u1.
			if (u1AtPosition == null)
				return false;

			Term u2AtPosition = u2.get(position);
			// We only consider positions of v2
			// that are also positions of u2.
			if (u2AtPosition == null)
				return false;

			Term v2AtPosition = v2.get(position);
			if (!(v2AtPosition instanceof Variable variable))
				return true;

			if (!this.completeSubstitutions(
					variable,
					u1AtPosition,
					u2AtPosition))
				return false;

			this.completeContexts(position, u1AtPosition, u2AtPosition, variable);
			return true;
		}

		/**
		 * Completes the substitutions at one variable position of v2.
		 *
		 * @param variable the variable found in v2
		 * @param u1AtPosition the subterm of the fact head at the same position
		 * @param u2AtPosition the subterm of the binary-rule head at the same
		 * position
		 * @return <code>true</code> iff both substitutions remain compatible
		 */
		private boolean completeSubstitutions(
				Variable variable,
				Term u1AtPosition,
				Term u2AtPosition) {

			return this.completeSigma(variable, u2AtPosition) &&
					this.completeMu(variable, u1AtPosition);
		}

		/**
		 * Completes the pumping substitution at one variable position of v2.
		 *
		 * @param variable the variable found in v2
		 * @param u2AtPosition the expected image in the binary-rule head
		 * @return <code>true</code> iff sigma remains compatible
		 */
		private boolean completeSigma(Variable variable, Term u2AtPosition) {
			if (this.identityVariables.contains(variable))
				// Here, sigma maps variable to itself.
				return u2AtPosition == variable;

			Term image = this.sigma.get(variable);
			if (image != null)
				// Here, variable belongs to Dom(sigma).
				return image.deepEquals(u2AtPosition);

			// Here, variable does not belong to Dom(sigma)
			// and has not been met before.
			if (variable == u2AtPosition) {
				this.identityVariables.add(variable);
				return true;
			}

			// We add variable -> u2AtPosition to sigma, but only
			// if variable occurs in u2AtPosition and is its only
			// variable.
			if (!this.hasSingleVariable(u2AtPosition, variable))
				return false;

			return this.sigma.add(variable, u2AtPosition);
		}

		/**
		 * Checks whether a term has exactly the provided variable.
		 *
		 * @param term the term to inspect
		 * @param variable the expected only variable of the term
		 * @return <code>true</code> iff variable is the only variable of term
		 */
		private boolean hasSingleVariable(Term term, Variable variable) {
			Set<Variable> variables = term.getVariables();
			return variables.size() == 1 && variables.contains(variable);
		}

		/**
		 * Completes the closing substitution at one variable position of v2.
		 *
		 * @param variable the variable found in v2
		 * @param u1AtPosition the expected image in the fact head
		 * @return <code>true</code> iff mu remains compatible
		 */
		private boolean completeMu(Variable variable, Term u1AtPosition) {
			Term image = this.mu.get(variable);
			if (image != null)
				// Here, variable belongs to Dom(mu).
				return image.deepEquals(u1AtPosition);

			// Here, variable does not belong to Dom(mu).
			if (variable == u1AtPosition)
				return true;

			return this.mu.add(variable, u1AtPosition);
		}

		/**
		 * Completes the two contexts at one variable position of v2.
		 *
		 * @param position the inspected position
		 * @param u1AtPosition the subterm of u1 at the inspected position
		 * @param u2AtPosition the subterm of u2 at the inspected position
		 * @param variable the variable found in v2
		 */
		private void completeContexts(
				Position position,
				Term u1AtPosition,
				Term u2AtPosition,
				Variable variable) {

			if (u1AtPosition != variable)
				this.u1Context = this.u1Context.replace(position, variable);
			if (u2AtPosition != variable)
				this.u2Context = this.u2Context.replace(position, variable);
		}

		/**
		 * Checks whether the completed search is accepted.
		 *
		 * @param v2 the binary-rule body atom
		 * @return <code>true</code> iff sigma is suitable and all contexts match
		 */
		private boolean isAccepted(Function v2) {
			return CorrectPatternRuleLpProducer.isSuitable(this.sigma) &&
					this.u1Context.deepEquals(this.u2Context) &&
					this.u1Context.deepEquals(v2);
		}
	}

	/**
	 * Disables construction.
	 */
	private Prop2PatternFactSearch() {
	}
}
