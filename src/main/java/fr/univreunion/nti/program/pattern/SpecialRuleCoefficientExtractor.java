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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.pattern;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Extracts the coefficients recognized in a special pattern rule.
 *
 * <p>The special-rule criterion is Definition 14 of E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class SpecialRuleCoefficientExtractor {

	/**
	 * Attempts to extract special-rule coefficients from two substitutions.
	 *
	 * @param left the left substitution
	 * @param right the right substitution
	 * @return the special-rule coefficients, or {@code null}
	 */
	static SpecialRuleCoefficients extract(Substitution left, Substitution right) {
		Set<Variable> domain = left.getDomain();
		domain.addAll(right.getDomain());
		Map<Term, Term> variableContexts = new HashMap<>();
		Substitution rho = new Substitution();
		CandidateCoefficients candidate = new CandidateCoefficients();

		for (Variable variable : domain) {
			if (!acceptImagesFor(
					variable,
					left,
					right,
					rho,
					variableContexts,
					candidate))
				return null;
		}

		return candidate.toCoefficients();
	}

	/**
	 * Validates and accumulates the coefficient contribution of one variable's
	 * substitution images.
	 *
	 * @param variable the domain variable whose images are inspected
	 * @param left the left substitution
	 * @param right the right substitution
	 * @param rho the substitution incrementally witnessing embedded-term
	 * generality
	 * @param variableContexts the contexts previously associated with embedded
	 * variables
	 * @param candidate the coefficient candidate being accumulated
	 * @return <code>true</code> if both images are compatible with a special rule
	 */
	private static boolean acceptImagesFor(
			Variable variable,
			Substitution left,
			Substitution right,
			Substitution rho,
			Map<Term, Term> variableContexts,
			CandidateCoefficients candidate) {
		SpecialPatternTermDetails leftDetails =
				extractDetails(left.getOrDefault(variable, variable), variable);
		SpecialPatternTermDetails rightDetails =
				extractDetails(right.getOrDefault(variable, variable), variable);

		if (!leftDetails.context().deepEquals(rightDetails.context()))
			return false;

		Term embeddedTerm = leftDetails.embeddedTerm();
		if (!embeddedTerm.isMoreGeneralThan(rightDetails.embeddedTerm(), rho))
			return false;

		if (hasTrivialGroundContribution(
				leftDetails, rightDetails, embeddedTerm))
			return true;

		if (embeddedTerm.isVariable())
			return candidate.acceptVariable(leftDetails, rightDetails) &&
					checkVariable(
						embeddedTerm, leftDetails.context(), variableContexts);

		return embeddedTerm.isGround() &&
				candidate.acceptGround(leftDetails, rightDetails);
	}

	/** Checks whether both images contribute no nonzero coefficient. */
	private static boolean hasTrivialGroundContribution(
			SpecialPatternTermDetails left,
			SpecialPatternTermDetails right,
			Term embeddedTerm) {
		return left.a() == 0 && left.b() == 0 &&
				right.a() == 0 && right.b() == 0 &&
				embeddedTerm.isGround();
	}

	/**
	 * Extracts the two exponents, context, and embedded term.
	 *
	 * @param term the term to inspect
	 * @param emptyContext the context used when {@code term} is not a hat function
	 * @return the extracted details
	 */
	private static SpecialPatternTermDetails extractDetails(
			Term term, Variable emptyContext) {

		if (term instanceof HatFunction hatFunction)
			return new SpecialPatternTermDetails(
					hatFunction.getA(),
					hatFunction.getB(),
					hatFunction.getRootSymbol().getSimpleContext(),
					hatFunction.getArgument());

		return new SpecialPatternTermDetails(0, 0, emptyContext, term);
	}

	/** Checks that a variable is always embedded in the same context. */
	private static boolean checkVariable(
			Term variable, Term context, Map<Term, Term> variableContexts) {

		Term previousContext = variableContexts.get(variable);
		if (previousContext != null) return previousContext.deepEquals(context);
		variableContexts.put(variable, context);
		return true;
	}

	/** The coefficients accumulated while substitution images are inspected. */
	private static final class CandidateCoefficients {

		private VariableCoefficients variableCoefficients;
		private GroundCoefficients groundCoefficients;

		/** Records and validates the coefficients of a variable embedded term. */
		private boolean acceptVariable(
				SpecialPatternTermDetails left,
				SpecialPatternTermDetails right) {

			if (this.variableCoefficients == null) {
				if (left.a() > right.a()) return false;
				this.variableCoefficients = new VariableCoefficients(
						left.a(), right.a(), left.b(), right.b());
				return true;
			}

			return left.a() == this.variableCoefficients.leftA()
					&& right.a() == this.variableCoefficients.rightA()
					&& left.b() == this.variableCoefficients.leftD()
					&& right.b() == this.variableCoefficients.rightD();
		}

		/** Records and validates the coefficients of a ground embedded term. */
		private boolean acceptGround(
				SpecialPatternTermDetails left,
				SpecialPatternTermDetails right) {

			if (left.a() == 0 && left.b() == 0
					&& right.a() == 0 && right.b() == 0)
				return true;

			if (this.groundCoefficients == null) {
				if (left.a() <= 0 || right.a() != left.a()
						|| left.b() > right.b())
					return false;
				this.groundCoefficients = new GroundCoefficients(
						left.a(), left.b(), right.b());
				return true;
			}

			return left.a() == this.groundCoefficients.groundA()
					&& right.a() == this.groundCoefficients.groundA()
					&& left.b() == this.groundCoefficients.leftB()
					&& right.b() == this.groundCoefficients.rightB();
		}

		/** Validates the accumulated form and creates its final coefficients. */
		private SpecialRuleCoefficients toCoefficients() {
			if (this.variableCoefficients == null)
				return this.buildGroundOnlyCoefficients();
			if (this.groundCoefficients == null)
				return this.buildVariableOnlyCoefficients();
			return this.buildCombinedCoefficients();
		}

		/** Validates and builds coefficients for the ground-only form. */
		private SpecialRuleCoefficients buildGroundOnlyCoefficients() {
			int groundA = this.groundCoefficients == null
					? -1 : this.groundCoefficients.groundA();
			int leftB = this.groundCoefficients == null
					? -1 : this.groundCoefficients.leftB();
			int rightB = this.groundCoefficients == null
					? -1 : this.groundCoefficients.rightB();
			int difference = rightB - leftB;
			if (difference % groundA != 0) return null;
			int k = difference / groundA;
			return new SpecialRuleCoefficients(
					-1, -1, leftB, rightB, -1, -1, k);
		}

		/** Validates and builds coefficients for the variable-only form. */
		private SpecialRuleCoefficients buildVariableOnlyCoefficients() {
			if (this.variableCoefficients.leftA() == this.variableCoefficients.rightA()
					&& this.variableCoefficients.leftD()
							> this.variableCoefficients.rightD())
				return null;
			return new SpecialRuleCoefficients(
					this.variableCoefficients.leftA(),
					this.variableCoefficients.rightA(),
					-1, -1,
					this.variableCoefficients.leftD(),
					this.variableCoefficients.rightD(), 0);
		}

		/** Validates and builds coefficients for the combined form. */
		private SpecialRuleCoefficients buildCombinedCoefficients() {
			int difference =
					this.groundCoefficients.rightB() - this.groundCoefficients.leftB();
			if (difference % this.groundCoefficients.groundA() != 0) return null;
			int k = difference / this.groundCoefficients.groundA();
			if (this.variableCoefficients.leftA()
					== this.variableCoefficients.rightA()
					&& (this.variableCoefficients.rightD()
							- this.variableCoefficients.leftD()
							- this.variableCoefficients.leftA() * k) < 0)
				return null;

			return new SpecialRuleCoefficients(
					this.variableCoefficients.leftA(),
					this.variableCoefficients.rightA(),
					this.groundCoefficients.leftB(),
					this.groundCoefficients.rightB(),
					this.variableCoefficients.leftD(),
					this.variableCoefficients.rightD(), k);
		}
	}

	/** The common coefficients contributed by variable embedded terms. */
	private record VariableCoefficients(
			int leftA,
			int rightA,
			int leftD,
			int rightD) {
	}

	/**
	 * The common coefficients contributed by ground embedded terms.
	 *
	 * @param groundA the common <code>a</code> coefficient, denoted <code>e</code>
	 * in Definition 14 of the Payet (2025) article cited in the class
	 * documentation
	 * @param leftB the left <code>b</code> coefficient
	 * @param rightB the right <code>b</code> coefficient
	 */
	private record GroundCoefficients(
			int groundA,
			int leftB,
			int rightB) {
	}

	/** The details extracted from one special-pattern substitution image. */
	private record SpecialPatternTermDetails(
			int a,
			int b,
			Term context,
			Term embeddedTerm) {
	}

	/** Prevents instantiation of this utility class. */
	private SpecialRuleCoefficientExtractor() {
	}
}
