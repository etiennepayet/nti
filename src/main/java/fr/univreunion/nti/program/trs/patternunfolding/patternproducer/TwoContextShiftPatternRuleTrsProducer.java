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
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
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
 * Produces correct TRS pattern rules from two context shifts.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class TwoContextShiftPatternRuleTrsProducer {

	/**
	 * Attempts to build a pattern rule from two binary
	 * rules that shift two arguments through a common
	 * unary context.
	 * <p>
	 * More precisely, this method considers the following
	 * situation:
	 * <ol>
	 * <li>
	 * <code>r1 = (c(s1, s2) -> t)</code>
	 * </li>
	 * <li>
	 * <code>r2 = (c(c1^a(x2), y2) -> c(x2, y2))</code>
	 * </li>
	 * <li>
	 * <code>r3 = (c(x3, c1^b(y3)) -> c(x3, y3))</code>
	 * </li>
	 * </ol>
	 * where <code>s1, s2, t</code> are terms,
	 * <code>c</code> is a 2-context,
	 * <code>c1</code> is a 1-context,
	 * <code>x2, y2</code> are distinct variables
	 * that do not occur in <code>c, c1</code>,
	 * <code>x3, y3</code> are distinct variables
	 * that do not occur in <code>c, c1</code>,
	 * and <code>a, b</code> are naturals.
	 *
	 * @param r1 the rule providing the initial arguments
	 * @param r2 the rule shifting the first argument
	 * @param r3 the rule shifting the second argument
	 * @return the pattern rule
	 * <code>c(c1^{a,0}(s1), c1^{b,0}(s2)) -> t^*</code>,
	 * or <code>null</code> if the provided rules do not
	 * match this schema
	 */
	static PatternRuleTrs tryBuild(
			RuleTrs r1, RuleTrs r2, RuleTrs r3) {
		TwoContextShiftInput input = tryBuildInput(r1, r2, r3);
		if (input == null) return null;

		TwoContextShiftContext shiftedContext =
				input.tryBuildSharedShiftedContext();
		if (shiftedContext == null) return null;

		return input.tryBuildPatternRule(shiftedContext);
	}

	/**
	 * Extracts the structurally valid input of the two-context-shift schema.
	 *
	 * @param r1 the rule providing the initial arguments
	 * @param r2 the rule shifting the first argument
	 * @param r3 the rule shifting the second argument
	 * @return the extracted input, or <code>null</code> if the rules do not
	 * have the expected roots, arity, or variable positions
	 */
	private static TwoContextShiftInput tryBuildInput(
			RuleTrs r1, RuleTrs r2, RuleTrs r3) {

		// We only consider the particular case
		// where c is a context of the form
		// f(square_1,square_2) where f is
		// a function symbol.

		Function u1 = r1.getLeft();
		Function u2 = r2.getLeft();
		Function u3 = r3.getLeft();
		Term v2     = r2.getRight();
		Term v3     = r3.getRight();

		FunctionSymbol f = u1.getRootSymbol();
		if (u2.getRootSymbol() != f || v2.getRootSymbol() != f
				|| u3.getRootSymbol() != f || v3.getRootSymbol() != f)
			return null;

		// From here, u1 has the form f(...),
		// r2 = (u2 -> v2) has the form f(...) -> f(...) and
		// r3 = (u3 -> v3) has the form f(...) -> f(...).
		// In particular, v2 and v3 are functions,
		// but we check anyway.
		if (!(v2 instanceof Function) || !(v3 instanceof Function))
			return null;

		if (f.getArity() != 2) return null;

		TwoContextShiftArguments arguments = TwoContextShiftArguments.from(
				u1, u2, (Function) v2, u3, (Function) v3);
		return arguments.tryBuildInput(f, r1.getRight());
	}

	/** The arguments extracted from rules with accepted roots and arity. */
	private record TwoContextShiftArguments(
			Term firstInitialArgument,
			Term secondInitialArgument,
			Term firstShiftedArgument,
			Term v2FirstArgument,
			Term v2SecondArgument,
			Term u2SecondArgument,
			Term u3FirstArgument,
			Term secondShiftedArgument,
			Term v3FirstArgument,
			Term v3SecondArgument) {

		/**
		 * Extracts the positional arguments of the three rules.
		 *
		 * @param u1 the left-hand side providing the initial arguments
		 * @param u2 the left-hand side shifting the first argument
		 * @param v2 the corresponding right-hand side
		 * @param u3 the left-hand side shifting the second argument
		 * @param v3 the corresponding right-hand side
		 * @return the extracted arguments
		 */
		private static TwoContextShiftArguments from(
				Function u1,
				Function u2,
				Function v2,
				Function u3,
				Function v3) {
			return new TwoContextShiftArguments(
					u1.getChild(0), // s1
					u1.getChild(1), // s2
					u2.getChild(0), // c1^a(x2)
					v2.getChild(0), // x2
					v2.getChild(1), // y2
					u2.getChild(1), // y2
					u3.getChild(0), // x3
					u3.getChild(1), // c1^b(y3)
					v3.getChild(0), // x3
					v3.getChild(1)); // y3
		}

		/**
		 * Validates the variable positions and builds the accepted input.
		 *
		 * @param rootSymbol the common binary root symbol
		 * @param rightHandSide the right-hand side of the first rule
		 * @return the accepted input, or <code>null</code> if a variable
		 * position or identity is invalid
		 */
		private TwoContextShiftInput tryBuildInput(
				FunctionSymbol rootSymbol, Term rightHandSide) {
			if (!(this.v2FirstArgument instanceof Variable x2)) return null;
			if (!(this.v2SecondArgument instanceof Variable)) return null;
			if (this.v2FirstArgument == this.v2SecondArgument) return null;
			if (!(this.v3FirstArgument instanceof Variable)) return null;
			if (!(this.v3SecondArgument instanceof Variable y3)) return null;
			if (this.v3FirstArgument == this.v3SecondArgument) return null;
			if (!(this.u2SecondArgument instanceof Variable)) return null;
			if (this.u2SecondArgument != this.v2SecondArgument) return null;
			if (!(this.u3FirstArgument instanceof Variable)) return null;
			if (this.u3FirstArgument != this.v3FirstArgument) return null;

			return new TwoContextShiftInput(
					rootSymbol,
					x2,
					y3,
					this.firstInitialArgument,
					this.secondInitialArgument,
					this.firstShiftedArgument,
					this.secondShiftedArgument,
					rightHandSide);
		}
	}

	/** The structurally valid input of the two-context-shift schema. */
	private record TwoContextShiftInput(
			FunctionSymbol rootSymbol,
			Variable x2,
			Variable y3,
			Term firstInitialArgument,
			Term secondInitialArgument,
			Term firstShiftedArgument,
			Term secondShiftedArgument,
			Term rightHandSide) {

		/**
		 * Extracts the common unary context and its two exponents.
		 *
		 * @return the common context, or <code>null</code> if either shifted
		 * argument is invalid or the contexts are not variants
		 */
		private TwoContextShiftContext tryBuildSharedShiftedContext() {
			int[] firstExponent = new int[1];
			Term firstContext = PatternUtils.getContext(
					this.firstShiftedArgument, this.x2, firstExponent);
			if (firstContext == null) return null;

			int[] secondExponent = new int[1];
			Term secondContext = PatternUtils.getContext(
					this.secondShiftedArgument, this.y3, secondExponent);
			if (secondContext == null) return null;

			if (!firstContext.isVariantOf(secondContext)) return null;

			return new TwoContextShiftContext(
					firstContext, firstExponent[0], secondExponent[0]);
		}

		/**
		 * Builds the pattern rule from this input and an accepted context.
		 *
		 * @param shiftedContext the common context and its two exponents
		 * @return the pattern rule, or <code>null</code> if its pattern
		 * substitution cannot be built
		 */
		private PatternRuleTrs tryBuildPatternRule(
				TwoContextShiftContext shiftedContext) {
			HatFunctionSymbol symbol =
					HatFunctionSymbol.intern(shiftedContext.context(), this.x2);
			Substitution theta = new Substitution();
			theta.add(this.x2, new HatFunction(
					symbol, this.firstInitialArgument,
					shiftedContext.firstExponent(), 0));
			theta.add(this.y3, new HatFunction(
					symbol, this.secondInitialArgument,
					shiftedContext.secondExponent(), 0));

			Map<Term, Term> copies = new HashMap<>();
			List<Term> arguments = new LinkedList<>();
			arguments.add(this.x2.deepCopy(copies));
			arguments.add(this.y3.deepCopy(copies));

			SimplePatternSubstitution eta =
					SimplePatternSubstitution.tryBuildTakingOwnership(
							theta.deepCopy(copies));
			if (eta == null) return null;

			return PatternRuleTrs.tryBuild(
					SimplePatternTerm.tryBuild(
							new Function(this.rootSymbol, arguments), eta),
					SimplePatternTerm.of(this.rightHandSide.deepCopy(copies)),
					0);
		}
	}

	/** The common shifted unary context and its two exponents. */
	private record TwoContextShiftContext(
			Term context, int firstExponent, int secondExponent) {}

	/** Prevents instantiation. */
	private TwoContextShiftPatternRuleTrsProducer() {}
}
