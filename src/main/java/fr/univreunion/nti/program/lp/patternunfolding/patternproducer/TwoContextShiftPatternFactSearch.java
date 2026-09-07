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
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternUtils;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Search for pattern facts built from two binary rules that shift two
 * arguments through a common unary context.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class TwoContextShiftPatternFactSearch {

	/**
	 * Attempts to build a two-context-shift pattern fact.
	 *
	 * @param u1 the head of the fact
	 * @param u2 the head of the first binary rule
	 * @param v2 the body atom of the first binary rule
	 * @param u3 the head of the second binary rule
	 * @param v3 the body atom of the second binary rule
	 * @return the pattern fact, or <code>null</code> if no such fact
	 * can be built
	 */
	static PatternRuleLp tryBuild(
			Function u1,
			Function u2,
			Function v2,
			Function u3,
			Function v3) {

		TwoContextShiftInput input =
				tryBuildInput(u1, u2, v2, u3, v3);
		if (input == null)
			return null;

		// We check if vars(s1) is disjoint from vars(s2).
		if (input.factArgumentsShareVariables())
			return null;

		TwoContextShiftContext shiftedContext =
				input.tryBuildSharedShiftedContext();
		if (shiftedContext == null)
			return null;

		return input.tryBuildPatternFact(shiftedContext);
	}

	/**
	 * Extracts the structurally valid inputs for a two-context-shift
	 * pattern fact.
	 *
	 * @param u1 the head of the fact
	 * @param u2 the head of the first binary rule
	 * @param v2 the body atom of the first binary rule
	 * @param u3 the head of the second binary rule
	 * @param v3 the body atom of the second binary rule
	 * @return the extracted input, or <code>null</code> when the
	 * rules do not have the expected root symbols, arity, or
	 * variable positions
	 */
	private static TwoContextShiftInput tryBuildInput(
			Function u1,
			Function u2,
			Function v2,
			Function u3,
			Function v3) {

		FunctionSymbol rootSymbol =
				tryBuildRootSymbol(u1, u2, v2, u3, v3);
		if (rootSymbol == null)
			return null;

		// From here, u1 has the form p(...),
		// u2 :- v2 has the form p(...) :- p(...) and
		// u3 :- v3 has the form p(...) :- p(...).
		TwoContextShiftArguments arguments =
				TwoContextShiftArguments.from(u1, u2, v2, u3, v3);
		TwoContextShiftVariables variables =
				arguments.tryBuildVariables();
		if (variables == null)
			return null;

		return arguments.buildInput(rootSymbol, variables);
	}

	/**
	 * Extracts the accepted root symbol for a two-context-shift pattern fact.
	 *
	 * @param u1 the head of the fact
	 * @param u2 the head of the first binary rule
	 * @param v2 the body atom of the first binary rule
	 * @param u3 the head of the second binary rule
	 * @param v3 the body atom of the second binary rule
	 * @return the accepted root symbol, or <code>null</code> when the
	 * functions do not share a binary root symbol
	 */
	private static FunctionSymbol tryBuildRootSymbol(
			Function u1,
			Function u2,
			Function v2,
			Function u3,
			Function v3) {

		FunctionSymbol rootSymbol = u1.getRootSymbol();
		if (!haveSameRootSymbol(rootSymbol, u2, v2, u3, v3))
			return null;

		if (rootSymbol.getArity() != 2)
			return null;

		return rootSymbol;
	}

	/**
	 * Checks whether all the specified functions have the same root symbol.
	 *
	 * @param rootSymbol the expected root symbol
	 * @param functions the functions to check
	 * @return <code>true</code> iff all the specified functions have
	 * <code>rootSymbol</code> as root symbol
	 */
	private static boolean haveSameRootSymbol(
			FunctionSymbol rootSymbol,
			Function... functions) {

		for (Function function : functions)
			if (function.getRootSymbol() != rootSymbol)
				return false;

		return true;
	}

	/**
	 * The structurally valid inputs for a two-context-shift pattern fact.
	 */
	private record TwoContextShiftInput(
			FunctionSymbol rootSymbol,
			Variable x,
			Variable y,
			Term firstFactArgument,
			Term secondFactArgument,
			Term firstShiftedArgument,
			Term secondShiftedArgument) {

		/**
		 * Checks whether the two fact arguments share variables.
		 *
		 * @return <code>true</code> iff the two fact arguments share at least
		 * one variable
		 */
		private boolean factArgumentsShareVariables() {
			return this.firstFactArgument.getVariables().removeAll(
					this.secondFactArgument.getVariables());
		}

		/**
		 * Builds the two-context-shift pattern fact.
		 *
		 * @param shiftedContext the shared shifted context and exponents
		 * @return the pattern fact, or <code>null</code> if it cannot be built
		 */
		private PatternRuleLp tryBuildPatternFact(
				TwoContextShiftContext shiftedContext) {

			Substitution theta = this.buildTheta(shiftedContext);
			Map<Term, Term> copies = new HashMap<>();

			SimplePatternSubstitution eta =
					SimplePatternSubstitution.tryBuildTakingOwnership(
							theta.deepCopy(copies));
			if (eta == null)
				return null;

			return PatternRuleLp.tryBuildFact(
					SimplePatternTerm.tryBuild(
							this.buildPatternBase(copies),
							eta),
					0);
		}

		/**
		 * Extracts the shared shifted context and its two exponents.
		 *
		 * @return the shared shifted context, or <code>null</code> when the
		 * shifted arguments do not use variant contexts
		 */
		private TwoContextShiftContext tryBuildSharedShiftedContext() {
			int[] firstExponent = new int[1];
			Term firstContext =
					PatternUtils.getContext(
							this.firstShiftedArgument,
							this.x,
							firstExponent);

			int[] secondExponent = new int[1];
			Term secondContext =
					PatternUtils.getContext(
							this.secondShiftedArgument,
							this.y,
							secondExponent);

			if (firstContext == null ||
					secondContext == null ||
					!firstContext.isVariantOf(secondContext))
				return null;

			return new TwoContextShiftContext(
					firstContext,
					firstExponent[0],
					secondExponent[0]);
		}

		/**
		 * Builds the pumping substitution for a two-context-shift pattern fact.
		 *
		 * @param shiftedContext the shared shifted context and exponents
		 * @return the pumping substitution
		 */
		private Substitution buildTheta(TwoContextShiftContext shiftedContext) {

			HatFunctionSymbol symb =
					HatFunctionSymbol.intern(shiftedContext.context, this.x);
			Substitution theta = new Substitution();
			theta.add(this.x, new HatFunction(
					symb,
					this.firstFactArgument,
					shiftedContext.firstExponent,
					0));
			theta.add(this.y, new HatFunction(
					symb,
					this.secondFactArgument,
					shiftedContext.secondExponent,
					0));

			return theta;
		}

		/**
		 * Builds the base atom of a two-context-shift pattern fact.
		 *
		 * @param copies the copy map
		 * @return the copied base atom
		 */
		private Function buildPatternBase(Map<Term, Term> copies) {
			return new Function(
					this.rootSymbol,
					List.of(
							this.x.deepCopy(copies),
							this.y.deepCopy(copies)));
		}
	}

	/**
	 * The arguments extracted from rules with accepted two-context-shift roots.
	 */
	private record TwoContextShiftArguments(
			Term firstFactArgument,
			Term secondFactArgument,
			Term firstShiftedArgument,
			Term v2FirstArgument,
			Term v2SecondArgument,
			Term u2SecondArgument,
			Term u3FirstArgument,
			Term secondShiftedArgument,
			Term v3FirstArgument,
			Term v3SecondArgument) {

		/**
		 * Extracts the relevant arguments from the fact and binary rules.
		 *
		 * @param u1 the head of the fact
		 * @param u2 the head of the first binary rule
		 * @param v2 the body atom of the first binary rule
		 * @param u3 the head of the second binary rule
		 * @param v3 the body atom of the second binary rule
		 * @return the extracted arguments
		 */
		private static TwoContextShiftArguments from(
				Function u1,
				Function u2,
				Function v2,
				Function u3,
				Function v3) {

			return new TwoContextShiftArguments(
					u1.getChild(0),
					u1.getChild(1),
					u2.getChild(0),
					v2.getChild(0),
					v2.getChild(1),
					u2.getChild(1),
					u3.getChild(0),
					u3.getChild(1),
					v3.getChild(0),
					v3.getChild(1));
		}

		/**
		 * Extracts the variables used by structurally valid two-context shifts.
		 *
		 * @return the extracted variables, or <code>null</code> when the
		 * arguments do not match the expected variable positions
		 */
		private TwoContextShiftVariables tryBuildVariables() {
			if (!(this.v2FirstArgument instanceof Variable x))
				return null;

			if (!(this.v2SecondArgument instanceof Variable))
				return null;

			if (this.v2FirstArgument == this.v2SecondArgument)
				return null;

			if (!(this.v3FirstArgument instanceof Variable))
				return null;

			if (!(this.v3SecondArgument instanceof Variable y))
				return null;

			if (this.v3FirstArgument == this.v3SecondArgument)
				return null;

			if (!(this.u2SecondArgument instanceof Variable))
				return null;

			if (this.u2SecondArgument != this.v2SecondArgument)
				return null;

			if (!(this.u3FirstArgument instanceof Variable))
				return null;

			if (this.u3FirstArgument != this.v3FirstArgument)
				return null;

			return new TwoContextShiftVariables(x, y);
		}

		/**
		 * Builds the accepted two-context-shift input.
		 *
		 * @param rootSymbol the accepted root symbol
		 * @param variables the accepted shifted variables
		 * @return the accepted input
		 */
		private TwoContextShiftInput buildInput(
				FunctionSymbol rootSymbol,
				TwoContextShiftVariables variables) {

			return new TwoContextShiftInput(
					rootSymbol,
					variables.x,
					variables.y,
					this.firstFactArgument,
					this.secondFactArgument,
					this.firstShiftedArgument,
					this.secondShiftedArgument);
		}
	}

	/**
	 * The shared context and exponents extracted from two shifted arguments.
	 */
	private record TwoContextShiftContext(
			Term context,
			int firstExponent,
			int secondExponent) {
	}

	/**
	 * The variables extracted from structurally valid two-context shifts.
	 */
	private record TwoContextShiftVariables(Variable x, Variable y) {
	}

	/**
	 * Disables construction.
	 */
	private TwoContextShiftPatternFactSearch() {
	}
}
