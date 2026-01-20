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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.nonloop.iclp25;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.program.PatternRule;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.argument.ArgumentIclp25;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A pattern rule (see [Payet, ICLP'25]), resulting from unfolding a program.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternRuleTrsIclp25 extends PatternRule {
	
	/**
	 * Builds a pattern rule which has the provided
	 * left-hand side and right-hand side.
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @throws IllegalArgumentException if the given
	 * left-hand side is <code>null</code> or if the
	 * given iteration is negative
	 */
	private PatternRuleTrsIclp25(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		super(left, right, iteration);		
	}

	/**
	 * Builds a pattern rule from the provided elements.
	 * 
	 * For internal use only.
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @param nonterminating a ground nonterminating term
	 * generated from this rule
	 * @param alpha the <code>alpha</code> threshold of
	 * this rule
	 */
	private PatternRuleTrsIclp25(SimplePatternTerm left, SimplePatternTerm right,
			int iteration, Function nonterminating, int alpha) {

		super(left, right, iteration, nonterminating, alpha);
	}

	/**
	 * Static factory method.
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this rule is generated
	 * @return a pattern rule, or <code>null</code> if no pattern
	 * rule could be constructed from the specified elements
	 */
	public static PatternRuleTrsIclp25 getInstance(
			SimplePatternTerm left, SimplePatternTerm right,
			int iteration) {

		if (left != null && right != null && 0 <= iteration)
			return new PatternRuleTrsIclp25(left, right, iteration);

		return null;
	}

	/**
	 * Static factory method.
	 * 
	 * @param left the base term on the left-hand side of this
	 * pattern rule
	 * @param thetaLeft the pattern substitution on the left-hand
	 * side of this pattern rule
	 * @param right the base term on the right-hand side of this
	 * pattern rule
	 * @param thetaRight the pattern substitution on the right-hand
	 * side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @return a pattern rule, or <code>null</code> if no pattern
	 * rule could be constructed from the specified elements
	 */
	public static PatternRuleTrsIclp25 getInstance(
			Function left,  PatternSubstitution thetaLeft,
			Function right, PatternSubstitution thetaRight,
			int iteration) {

		if (thetaLeft instanceof SimplePatternSubstitution &&
				thetaRight instanceof SimplePatternSubstitution &&
				left != null && right != null && 0 <= iteration)
			return new PatternRuleTrsIclp25(
					SimplePatternTerm.getInstance(left,  (SimplePatternSubstitution) thetaLeft),
					SimplePatternTerm.getInstance(right, (SimplePatternSubstitution) thetaRight),
					iteration);

		return null;
	}
	
	/**
	 * Returns a deep copy of this pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this pattern rule
	 */
	@Override
	public PatternRuleTrsIclp25 deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a deep copy of this pattern rule i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern rule
	 */
	@Override
	public PatternRuleTrsIclp25 deepCopy(Map<Term, Term> copies) {
		SimplePatternTerm right = this.getRight();
		Function nonterminating = this.getNonTerminatingTerm();

		return new PatternRuleTrsIclp25(
				this.getLeft().deepCopy(copies), 
				(right == null ? null : right.deepCopy(copies)),
				this.getIteration(),
				(nonterminating == null ? null : (Function) nonterminating.deepCopy(copies)),
				this.getAlpha());
	}

	/**
	 * Unfolds this pattern rule forwards with the provided
	 * pattern rule and at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param r the pattern rule to use for unfolding this rule
	 * @param p a position in the right-hand side of this rule,
	 * at which the unfolding takes place
	 * @param right_p the subterm at position <code>p</code>
	 * of the right-hand side of this rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this unfolding takes place
	 * @return the resulting unfolded rule
	 */
	public PatternRuleTrsIclp25 unfoldForwardsWith(
			Parameters parameters, PatternRuleTrsIclp25 r,
			Position p, SimplePatternTerm right_p,
			int iteration) {

		// We unify the left-hand side of a copy of r with
		// the subterm at position p of the right-hand side
		// of this rule.
		PatternRuleTrsIclp25 r_copy = r.deepCopy();
		SimplePatternSubstitution sigma = right_p.unifyWith(r_copy.getLeft());
		if (sigma == null) return null;

		// We compose with sigma.
		// We start with the left-hand side of this rule:
		SimplePatternSubstitution thetaLeft = 
				this.getLeft().getPatternSubs().composeWith(sigma);
		if (thetaLeft == null) return null;
		// Then we consider the right-hand side of this rule:
		SimplePatternSubstitution thetaRight =
				this.getRight().getPatternSubs().composeWith(sigma);
		if (thetaRight == null) return null;
		// Finally, we consider the right-hand side of the copy of r:
		SimplePatternSubstitution theta_rRight =
				r_copy.getRight().getPatternSubs().composeWith(sigma);
		if (theta_rRight == null) return null;

		// We compute the left-hand side of the unfolded rule:
		SimplePatternTerm newLeft = SimplePatternTerm.getInstance(
				this.getLeft().getBaseTerm(), thetaLeft);
		if (newLeft == null) return null;

		// Then we compute its right-hand side:
		Term this_right_base = this.getRight().getBaseTerm();
		SimplePatternTerm newRight = SimplePatternTerm.getInstance(
				this_right_base, thetaRight);
		if (newRight == null) return null;
		//
		Term r_copy_right_base = r_copy.getRight().getBaseTerm();
		SimplePatternTerm new_rRight = SimplePatternTerm.getInstance(
				r_copy_right_base, theta_rRight);
		if (new_rRight == null) return null;
		//
		Substitution theta = newRight.getPatternSubs().getTheta().unionWith(new_rRight.getPatternSubs().getTheta());
		if (theta == null) return null;
		//
		thetaRight = SimplePatternSubstitution.getInstance(theta);
		if (thetaRight == null) return null;
		//
		newRight = SimplePatternTerm.getInstance(
				this_right_base.replace(p, r_copy_right_base),
				thetaRight);
		if (newRight == null) return null;

		return PatternRuleTrsIclp25.getInstance(newLeft, newRight, iteration);
	}

	/**
	 * Unfolds this pattern rule once using the
	 * elements of <code>patternRules</code>. 
	 * 
	 * Also applies the nontermination test of [Payet, ICLP'25]
	 * to the computed unfolded rules; if the test succeeds for
	 * an unfolded rule, then the corresponding proof argument
	 * is added to <code>proof</code>.
	 * 
	 * @param parameters parameters for unfolding
	 * @param patternRules the set of pattern rules used for
	 * unfolding this pattern rule
	 * @param iteration the current iteration of the
	 * unfolding operator
	 * @param proof a proof to build while unfolding
	 * this pattern rule
	 * @return the resulting unfolded rules
	 */
	public Collection<PatternRuleTrsIclp25> unfold(
			Parameters parameters,
			Collection<PatternRuleTrsIclp25> patternRules,
			int iteration, Proof proof) {

		// The collection to return at the end.
		LinkedList<PatternRuleTrsIclp25> result = new LinkedList<>();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// For the moment, we only unfold forwards.		
		// We consider every subterm of the right-hand
		// side of this pattern rule.
		SimplePatternTerm right = this.getRight();
		for (Position p : right) {
			if (currentThread.isInterrupted()) break;

			SimplePatternTerm right_p = right.get(p);

			// We only unfold at non-variable positions.
			if (right_p.isVariable()) continue;

			for (PatternRuleTrsIclp25 r : patternRules) {
				if (currentThread.isInterrupted()) break;
				
				// First, we weaken this rule based on
				// right_p and the left-hand side of r.
				for(PatternRuleTrsIclp25 weak_this : this.weaken(right_p, r.getLeft())) {
					if (currentThread.isInterrupted()) break;

					SimplePatternTerm weak_right_p = weak_this.getRight().get(p);
					// Then, we weaken r based on its left-hand
					// side and weak_right_p.
					for (PatternRuleTrsIclp25 weak_r : r.weaken(r.getLeft(), weak_right_p)) {
						if (currentThread.isInterrupted()) break;
						
						// Finally, we unfold the weakened versions
						// of this rule using the weakened versions
						// of r.
						PatternRuleTrsIclp25 u =
								weak_this.unfoldForwardsWith(parameters, weak_r, p, weak_right_p, iteration);
						if (u != null) {
							result.add(u);

							if (proof != null && u.getNonTerminatingTerm() != null) {
								// If u is a non-termination witness, then
								// build a corresponding proof argument.
								proof.setArgument(new ArgumentIclp25(u));
								return result;
							}
						}
					}
				}
			}
		}

		return result;
	}

	/**
	 * Attempts to weaken this pattern rule
	 * based on the provided pattern terms
	 * <code>subterm</code> and <code>p</code>,
	 * where <code>subterm</code> is supposed
	 * to be a subterm of this pattern rule.
	 * 
	 * The values used for weakening this
	 * pattern rule are those computed for
	 * weakening <code>subterm</code> w.r.t.
	 * <code>p</code>.
	 * 
	 * The returned collection always includes
	 * this pattern rule.
	 * 
	 * For the moment, we perform weakening only
	 * if the arity of <code>p</code>, that of
	 * the left-hand side of this rule and that
	 * of the right-hand side of this rule are
	 * all equal to 1.
	 *
	 * @param subterm a subterm of this pattern
	 * rule
	 * @param p a pattern term for weakening
	 * this pattern rule 
	 * @return a collection of weakened versions
	 * of this pattern rule, which always includes
	 * this pattern rule
	 */
	public Collection<PatternRuleTrsIclp25> weaken(SimplePatternTerm subterm, SimplePatternTerm p) {
		// The collection to return at the end.
		// It always includes this rule.
		Collection<PatternRuleTrsIclp25> result = new LinkedList<>();
		result.add(this);

		// The left-hand side and the right-hand side
		// of this pattern rule are not null, see
		// instance creation methods above.
		SimplePatternTerm left  = this.getLeft();
		SimplePatternTerm right = this.getRight();

		// We perform weakening only if the provided
		// pattern terms are not null and the arities
		// are all equal to 1.
		if (subterm != null && p != null &&
				p.getArity() == 1 &&
				left.getArity()  == 1 && 
				right.getArity() == 1) {

			// The values to use for weakening this
			// pattern rule are those to use for
			// weakening subterm w.r.t. p.
			int[] weakeningValues = subterm.getWeakeningValues(p);

			if (weakeningValues != null) {
				// Here, some weakening values could be computed.

				int i_fun = weakeningValues[0];
				int i_hat = weakeningValues[1];

				if (0 <= i_fun && i_hat < 0) {
					// Here, we compute (left(i_fun),right(i_fun)),
					// which is an element of
					// {(left(n),right(n)) | n \in \nat}.
					SimplePatternTerm wLeft  = 
							SimplePatternTerm.getInstance(left.valueOf(i_fun));
					SimplePatternTerm wRight =
							SimplePatternTerm.getInstance(right.valueOf(i_fun));
					PatternRuleTrsIclp25 weak =
							PatternRuleTrsIclp25.getInstance(wLeft, wRight, this.getIteration());
					if (weak != null) result.add(weak);
				}
				else if (i_fun < 0 && 0 <= i_hat) {
					// Here, we replace each mapping
					// x -> c^{a,b}(u) in left.theta
					// and right.theta by
					// x -> c^{a,a*i_hat+b}(u). Indeed,
					// c^{a,a*i_hat+b}(u) describes the set
					// {c^{a*n+a*i_hat+b}(u) | n \in \nat} =
					// {c^{a*(n+i_hat)+b}(u) | n \in \nat} =
					// {c^{a*n+b}(u) | n >= i_hat}
					// which is included in
					// {c^{a*n+b}(u) | n \in \nat}.
					//
					// We also replace each mapping
					// x -> c^{a,b}(u) in left.theta
					// and right.theta by
					// x -> c^{a,a,a*i_hat+b}(u). Indeed,
					// c^{a,a,a*i_hat+b}(u) describes the set
					// {c^{a*n+a*m+a*i_hat+b}(u) | n,m \in \nat} =
					// {c^{a*(n+m+i_hat)+b}(u) | n,m \in \nat} =
					// {c^{a*n+b}(u) | n >= i_hat}
					// which is included in
					// {c^{a*n+b}(u) | n \in \nat}.

					Substitution rho1_left = new Substitution();
					Substitution rho2_left = new Substitution();
					left.weaken(i_hat, rho1_left, rho2_left);

					Substitution rho1_right = new Substitution();
					Substitution rho2_right = new Substitution();
					right.weaken(i_hat, rho1_right, rho2_right);

					this.addWeakenedPatternRule(rho1_left, rho1_right, result);
					this.addWeakenedPatternRule(rho2_left, rho2_right, result);					
				}
			}
		}

		return result;
	}

	/**
	 * Builds a weakened pattern rule from
	 * the provided substitutions and adds
	 * it to the provided collection.
	 * 
	 * @param rho_left a substitution to use
	 * to build the left-hand side of the
	 * pattern rule to add to the collection
	 * @param rho_right a substitution to use
	 * to build the right-hand side of the
	 * pattern rule to add to the collection
	 * @param result a collection to complete
	 */
	private void addWeakenedPatternRule(
			Substitution rho_left, Substitution rho_right,
			Collection<PatternRuleTrsIclp25> result) {

		SimplePatternSubstitution eta_left = SimplePatternSubstitution.getInstance(rho_left);
		if (eta_left != null) {
			SimplePatternSubstitution eta_right = SimplePatternSubstitution.getInstance(rho_right);
			if (eta_right != null) {

				SimplePatternTerm wLeft =
						SimplePatternTerm.getInstance(this.getLeft().getBaseTerm(), eta_left);
				SimplePatternTerm wRight =
						SimplePatternTerm.getInstance(this.getRight().getBaseTerm(), eta_right);

				PatternRuleTrsIclp25 weak =
						PatternRuleTrsIclp25.getInstance(wLeft, wRight, this.getIteration());
				if (weak != null) result.add(weak);
			}
		}
	}

	/**
	 * Returns a string representation of this
	 * pattern rule relatively to the given set
	 * of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	@Override
	public String toString(Map<Variable, String> variables) {
		Function nonterminating = this.getNonTerminatingTerm();

		return this.getLeft().toString(variables) +
				" -> " + this.getRight().toString(variables) +
				(nonterminating == null ? ":?" : ":" + nonterminating.toString(variables, false));
	}
}
