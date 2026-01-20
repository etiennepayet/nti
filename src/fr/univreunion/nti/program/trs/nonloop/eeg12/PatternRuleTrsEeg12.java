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

package fr.univreunion.nti.program.trs.nonloop.eeg12;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.Options;
import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.argument.ArgumentEeg12;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternTerm;

/**
 * A pattern rule, as defined in [Emmes, Enger, Giesl, IJCAR'12].
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternRuleTrsEeg12 extends UnfoldedRuleTrs {

	/**
	 * The pumping substitution on the left-hand side
	 * of this pattern rule.
	 */
	private Substitution sigmaLeft;

	/**
	 * The closing substitution on the left-hand side
	 * of this pattern rule.
	 */
	private Substitution muLeft;

	/**
	 * The pumping substitution on the right-hand side
	 * of this pattern rule.
	 */
	private Substitution sigmaRight;

	/**
	 * The closing substitution on the right-hand side
	 * of this pattern rule.
	 */
	private Substitution muRight;

	/**
	 * Constructs a pattern rule from the given elements.
	 * 
	 * @param left the left-hand side of this pattern rule
	 * @param right the right-hand side of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @param parent the parent of this pattern rule
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public PatternRuleTrsEeg12(PatternTerm left, PatternTerm right,
			int iteration, ParentTrs parent) {

		super((Function) left.getBaseTerm(), right.getBaseTerm(),
				iteration, parent);

		this.sigmaLeft = left.getPumping();
		this.muLeft = left.getClosing();
		this.sigmaRight = right.getPumping();
		this.muRight = right.getClosing();
	}

	/**
	 * Constructs a pattern rule from the given elements.
	 * 
	 * The base term on the left-hand side of this pattern
	 * rule is set to the left-hand side of the specified
	 * rule. The base term on the right-hand side of this
	 * pattern rule is set to the right-hand side of the
	 * specified rule. The substitutions on left-hand side
	 * and on the right-hand side of this pattern rule are
	 * set to the empty substitution. 
	 * 
	 * @param R a rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @param parent the parent of this pattern rule
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public PatternRuleTrsEeg12(RuleTrs R, int iteration, ParentTrs parent) {
		super(R.getLeft(), R.getRight(), iteration, parent);

		this.sigmaLeft = new Substitution();
		this.muLeft = new Substitution();
		this.sigmaRight = new Substitution();
		this.muRight = new Substitution();
	}

	/**
	 * Constructs a pattern rule from the given elements.
	 * 
	 * @param left the base term on the left-hand side of this
	 * pattern rule
	 * @param sigmaLeft the pumping substitution on the left-hand
	 * side of this pattern rule
	 * @param muLeft the closing substitution on the left-hand side
	 * of this pattern rule
	 * @param right the base term on the right-hand side of this
	 * pattern rule
	 * @param sigmaRight the pumping substitution on the right-hand
	 * side of this pattern rule
	 * @param muRight the closing substitution on the right-hand side
	 * of this pattern rule
	 * @param iteration the iteration of the unfolding operator
	 * at which this pattern rule is generated
	 * @param parent the parent of this pattern rule
	 * @throws IllegalArgumentException if <code>right</code>
	 * is not a variable or a function
	 * @throws IllegalArgumentException if the given iteration
	 * is negative
	 */
	public PatternRuleTrsEeg12(Function left, Substitution sigmaLeft, Substitution muLeft,
			Term right, Substitution sigmaRight, Substitution muRight,
			int iteration, ParentTrs parent) {

		super(left, right, iteration, parent);

		this.sigmaLeft = sigmaLeft;
		this.muLeft = muLeft;
		this.sigmaRight = sigmaRight;
		this.muRight = muRight;
	}

	/**
	 * Return the pattern term on the left-hand side
	 * of this pattern rule.
	 * 
	 * @return the pattern term on the left-hand side
	 * of this pattern rule
	 */
	public PatternTerm getLeftPatternTerm() {
		return new PatternTerm(this.left, this.sigmaLeft, this.muLeft);
	}

	/**
	 * Return the pattern term on the right-hand side
	 * of this pattern rule.
	 * 
	 * @return the pattern term on the right-hand side
	 * of this pattern rule
	 */
	public PatternTerm getRightPatternTerm() {
		return new PatternTerm(this.right, this.sigmaRight, this.muRight);
	}

	/**
	 * Returns a deep copy of this rule i.e., a copy
	 * where each subterm is also copied. The iteration
	 * and the parent of the generated copy are set to
	 * the specified iteration and parent.
	 * 
	 * @param iteration the iteration of the generated copy
	 * @param parent the parent of the generated copy
	 * @return a deep copy of this rule
	 */
	@Override
	public UnfoldedRuleTrs deepCopy(int iteration, ParentTrs parent) {
		HashMap<Term, Term> copies = new HashMap<Term, Term>();

		return new PatternRuleTrsEeg12(
				(Function) this.left.deepCopy(copies),
				this.sigmaLeft.deepCopy(copies),
				this.muLeft.deepCopy(copies),
				this.right.deepCopy(copies),
				this.sigmaRight.deepCopy(copies),
				this.muRight.deepCopy(copies),
				iteration,
				parent);
	}

	/**
	 * Copy the specified rule into this rule.
	 * 
	 * @param R the rule to copy
	 */
	private void copy(PatternRuleTrsEeg12 R) {
		// We copy the left-hand side of R into this rule.
		this.left = R.left;
		this.sigmaLeft = R.sigmaLeft;
		this.muLeft = R.muLeft;

		// We copy the right-hand side of R into this rule.
		this.right = R.right;
		this.sigmaRight = R.sigmaRight;
		this.muRight = R.muRight;
	}

	/**
	 * Checks whether is pattern rule is a nontermination
	 * witness.
	 * 
	 * Implements Theorem 8 (Detecting Nontermination) of
	 * [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * @return a non-<code>null</code> nontermination argument
	 * if the test succeeds and <code>null</code> otherwise
	 */
	@Override
	public Argument nonTerminationTest() {
		Substitution mu = this.muLeft;
		Substitution mu_t = this.muRight;
		// We check whether mu is more general than mu_t.
		Substitution muPrime = new Substitution();
		if (!mu.isMoreGeneralThan(mu_t, muPrime))
			return null;

		Substitution sigma = this.sigmaLeft;
		Substitution sigma_t = this.sigmaRight;
		Substitution sigmaPrime = new Substitution();
		// Theorem 8 states that we have to check whether
		// sigma^m is more general than sigma_t, for some
		// integer m. Here, we only check for m=1 and m=2.
		int m = 1;
		if (!sigma.isMoreGeneralThan(sigma_t, sigmaPrime)) {
			m = 2;
			sigmaPrime.clear();
			Substitution sigma2 = sigma.composeWith(sigma);
			if (!sigma2.isMoreGeneralThan(sigma_t, sigmaPrime))
				return null;
		}

		// We check whether sigma' commutes with sigma and mu.
		if (!sigmaPrime.commutesWith(sigma) || !sigmaPrime.commutesWith(mu))
			return null;

		// We check whether sigma^b(s) = t|p for some integer b and
		// some position p. But we need to transform s and t into
		// functions because the inner subterms of t are not tuples.
		Term s = this.left.toFunction();
		Term t = this.right.toFunction();
		for (Position p : t) {
			Term t_p = t.get(p);
			int b = 0;
			Term u = s; // u = sigma^b(s).
			while (u.depth() <= t_p.depth() && b < 5) {
				// We only try until sigma^4(s). If we do not set
				// a limit, this loop may not terminate...
				if (u.deepEquals(t_p))
					return new ArgumentEeg12(
							this, m, b, p, sigmaPrime, muPrime);
				u = u.apply(sigma);
				b++;
			}
		}

		return null;
	}

	/**
	 * Applies the <code>elim</code> operator to this rule.
	 * 
	 * @param parameters parameters for applying <code>elim</code>
	 * @param IR the TRS used for applying <code>elim</code>
	 * @return the rules resulting from applying <code>elim</code>
	 * to this rule
	 */
	@Override
	public Collection<? extends UnfoldedRuleTrs> elim(Parameters parameters, Trs IR) {
		LinkedList<PatternRuleTrsEeg12> Result = new LinkedList<PatternRuleTrsEeg12>();
		Result.add(this);
		return Result;
	}

	/**
	 * Unfolds this rule forwards with the provided rule and
	 * at the provided position.
	 * 
	 * @param parameters parameters for unfolding
	 * @param R the rule to use for unfolding this rule
	 * @param p a position in this rule at which the unfolding
	 * takes place
	 * @param iteration the iteration of the unfolding operator
	 * at which this unfolding takes place
	 * @return the resulting unfolded rules
	 */
	@Override
	public Collection<? extends UnfoldedRuleTrs> unfoldForwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		// The rules that will be returned.
		Collection<UnfoldedRuleTrs> result = new LinkedList<UnfoldedRuleTrs>();

		// If R is a pattern rule, then we narrow this rule with R.
		// Otherwise, we rewrite this rule with R.
		PatternRuleTrsEeg12 N = (R instanceof PatternRuleTrsEeg12 ? 
				this.narrowWith((PatternRuleTrsEeg12) R, p, iteration) :
					this.rewriteWith(R, p, iteration));
		if (N != null) result.add(N);

		return result;
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Collection<? extends UnfoldedRuleTrs> unfoldBackwardsWith(
			Parameters parameters, RuleTrs R, Position p, int iteration) {

		throw new UnsupportedOperationException();
	}

	/**
	 * Unfolds this rule once using the rules of <code>IR</code>. 
	 * 
	 * Also applies <code>nonTerminationTest</code> to the computed
	 * unfolded rules if <code>proof</code> is not <code>null</code>;
	 * if <code>nonTerminationTest</code> succeeds for an unfolded rule,
	 * then the corresponding proof argument is added to <code>proof</code>.
	 * 
	 * @param parameters parameters for unfolding
	 * @param IR the TRS used for unfolding this rule and for applying
	 * the <code>elim</code> operator
	 * @param iteration the current iteration of the unfolding operator
	 * @param proof a proof to build while unfolding this rule
	 * @return the resulting unfolded rules
	 */
	@Override
	public Collection<? extends UnfoldedRuleTrs> unfold( 
			Parameters parameters, Trs IR, int iteration, Proof proof) {

		// The collection to return at the end.
		LinkedList<UnfoldedRuleTrs> result = new LinkedList<UnfoldedRuleTrs>();

		boolean b = parameters.isVariableUnfoldingEnabled();

		for (Position p : this.right) {

			if (b || !this.right.get(p).isVariable()) {
				// First, we try to rewrite this pattern rule with IR.
				for (RuleTrs R : IR)
					for (UnfoldedRuleTrs U : this.unfoldForwardsWith(parameters, R, p, iteration))
						if (add(parameters, IR, proof, U, result))
							return result;			

				// If nontermination was not detected, then we try
				// to narrow this pattern rule with IR.
				for (Iterator<PatternRuleTrsEeg12> it = IR.iteratorPatternRules(); it.hasNext(); )
					for (UnfoldedRuleTrs U : this.unfoldForwardsWith(parameters, it.next(), p, iteration))
						if (add(parameters, IR, proof, U, result))
							return result;
			}
		}

		return result;
	}

	/**
	 * Implements (VI) of [Emmes, Enger, Giesl, IJCAR'12]:
	 * narrows this pattern rule using the specified one
	 * at the specified position.
	 * 
	 * This implementation relies on the narrowing strategy
	 * presented in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * @param R a pattern rule to narrow this pattern
	 * rule with
	 * @param p a position in the base term of the
	 * right-hand side of this pattern rule
	 * @param iteration the current iteration of the unfolding
	 * operator where this narrowing takes place
	 * @return the pattern rule resulting from the narrowing,
	 * or <code>null</code> if the narrowing fails
	 */
	private PatternRuleTrsEeg12 narrowWith(PatternRuleTrsEeg12 R, Position p, int iteration) {
		// We work with copies of this pattern rule and R,
		// in order to keep this rule and R unchanged.
		// We need to build the parent only if we are in verbose mode.
		ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
				new ParentTrsNonLoopEeg12(this, R, p, false, InferenceRuleEeg12.VI) : null);
		PatternRuleTrsEeg12 thisCopy = (PatternRuleTrsEeg12) this.deepCopy(iteration, parent);
		PatternRuleTrsEeg12 Rcopy = (PatternRuleTrsEeg12) R.deepCopy(iteration, parent);

		// First, we apply steps 1-3 of the strategy.
		if (thisCopy.makeNarrowingApplicable(Rcopy, p, iteration)) {

			Term t = thisCopy.right;

			// Here, steps 1-3 have succeeded and thisCopy and
			// Rcopy have been modified accordingly.
			// Therefore, normally t|_p = Rcopy.left,
			// the pumping substitutions in thisCopy and
			// in Rcopy are equal and the closing substitutions
			// in thisCopy and in Rcopy are equal.

			// Now, we apply (VI).

			Term v = Rcopy.right;

			return new PatternRuleTrsEeg12(
					thisCopy.left, thisCopy.sigmaLeft, thisCopy.muLeft,
					t.replace(p, v), thisCopy.sigmaLeft, thisCopy.muLeft,
					iteration, parent);
		}

		return null;
	}

	/**
	 * Implements steps 1-3 of the narrowing strategy presented
	 * in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * These steps are applied to this pattern rule, which
	 * corresponds to <code>p -> q</code> in the strategy, and
	 * to the specified pattern rule, which corresponds to
	 * <code>p' -> q'</code> in the strategy.
	 * 
	 * It is supposed that this pattern rule and the specified
	 * one are variable-disjoint. Moreover, these pattern rules
	 * are modified by this method, according to steps 1-3.
	 * 
	 * @param R the pattern rule <code>p' -> q'</code> of the
	 * strategy
	 * @param p a position in the base term of the right-hand
	 * side of this pattern rule
	 * @param iteration the current iteration of the unfolding
	 * operator where steps 1-3 take place
	 * @return <code>true</code> iff steps 1-3 succeed
	 */
	private boolean makeNarrowingApplicable(
			PatternRuleTrsEeg12 R, Position p, int iteration) {

		// First, we apply step 1 of the strategy.
		if (this.narrowWith1(R, p, iteration)) {

			// Here, step 1 has succeeded and this and R
			// have been modified accordingly.

			// Now, we apply steps 2 & 3.

			// First, in this, we make the pumping substitutions
			// equal and the closing substitutions equal.

			PatternRuleTrsEeg12 thisNormalized = this.normalizedForm(iteration);
			if (thisNormalized != null) {

				// Then, in R, we make the pumping substitutions
				// equal and the closing substitutions equal.

				PatternRuleTrsEeg12 RNormalized = R.normalizedForm(iteration);
				if (RNormalized != null) {

					// Finally, we make the pumping substitutions
					// of this and R equal.

					PatternRuleTrsEeg12 R1 = thisNormalized.
							instantiatePumpingWith(RNormalized.sigmaLeft, iteration);
					if (R1 != null) {

						PatternRuleTrsEeg12 R2 = RNormalized.
								instantiatePumpingWith(thisNormalized.sigmaRight, iteration);
						if (R2 != null) {

							// We also make the closing substitutions
							// of this and R equal.

							Substitution mu1 = R1.muRight;
							Substitution mu2 = R2.muLeft;
							if (mu1.commutesWith(mu2)) {

								R1 = R1.instantiateClosingWith(mu2, iteration);
								R2 = R2.instantiateClosingWith(mu1, iteration);

								// If we get here, then everything went fine.
								// We modify this and R accordingly.
								this.copy(R1);
								R.copy(R2);
								// this.left = R1.left; this.right = R1.right;
								// R.left = R2.left; R.right = R2.right;

								return true;
							}
						}
					}
				}
			}
		}

		// If we get here, then something went wrong.
		return false;
	}

	/**
	 * Implements step 1 of the narrowing strategy presented
	 * in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * This step is applied to this pattern rule, which
	 * corresponds to <code>p -> q</code> in the strategy, and
	 * to the specified pattern rule, which corresponds to
	 * <code>p' -> q'</code> in the strategy.
	 * 
	 * It is supposed that this pattern rule and the specified
	 * one are variable-disjoint. Moreover, these pattern rules
	 * are modified by this method, according to steps 1a-1e.
	 * 
	 * @param R the pattern rule <code>p' -> q'</code> of the
	 * strategy
	 * @param p a position in the base term of the right-hand
	 * side of this pattern rule
	 * @param iteration the current iteration of the unfolding
	 * operator where this step takes place
	 * @return <code>true</code> iff this step succeeds
	 */
	private boolean narrowWith1(PatternRuleTrsEeg12 R, Position p, int iteration) {
		// This rule is built from dependency pairs.
		// Hence, if p = epsilon, then we replace the
		// root tuple symbol with the equivalent function
		// symbol, otherwise the test 'r_p.isUnifiableWith'
		// below will always fail.
		Term r_p = p.isEmpty() ? this.right.get(p).toFunction() : this.right.get(p);
		Term l = R.left;

		while (!r_p.deepEquals(l)) {

			Substitution theta = new Substitution();
			if (!r_p.isUnifiableWith(l, theta))
				return false;

			// As r_p is not equal to l, necessarily theta is not empty.
			Map.Entry<Variable, Term> mapping = theta.iterator().next();
			Variable x = mapping.getKey();
			Term s = mapping.getValue();

			// Now, let us implement steps 1a-1e.
			PatternRuleTrsEeg12 RR = this;
			PatternTerm pp = RR.getRightPatternTerm();
			if (R.left.contains(x) || R.sigmaLeft.contains(x) || R.muLeft.contains(x)) {
				RR = R;
				pp = RR.getLeftPatternTerm();
			}

			if (pp.inDomainVariable(x)) {
				if (pp.inDomainVariable(s)) {
					// Step 1c.
					// Here s is necessarily a variable because
					// it occurs in the domain variable of pp.
					if (!this.narrowWith1c(R, RR, pp, x, (Variable) s, iteration))
						return false;
				}
				else if (s instanceof Variable) {
					Variable v_s = (Variable) s;
					if (pp.contains(v_s)) {
						// Step 1b.
						if (!this.narrowWith1b(R, RR, pp, v_s, x, iteration))
							return false;
					}
					else
						// Step 1d.
						this.narrowWith1d(R, RR, pp, x, s, iteration);
				}
				else
					// Step 1e.
					return false;
			}
			else {
				if (pp.inDomainVariable(s)) {
					// Step 1b.
					// Here s is necessarily a variable because
					// it occurs in the domain variable of pp.
					if (!this.narrowWith1b(R, RR, pp, x, (Variable) s, iteration))
						return false;
				}
				else
					// Step 1a.
					if (!this.narrowWith1a(R, RR, pp, x, s, iteration))
						return false;
			}

			// As this pattern rule or R has changed, we have
			// to update r_p and l.
			r_p = p.isEmpty() ? this.right.get(p).toFunction() : this.right.get(p);
			l = R.left;
		}

		// If we get here, then everything worked fine.
		return true;
	}

	/**
	 * Implements step 1a of the narrowing strategy presented
	 * in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * This step is applied to this pattern rule, which
	 * corresponds to <code>p -> q</code> in the strategy, and
	 * to the specified pattern rule, which corresponds to
	 * <code>p' -> q'</code> in the strategy. Both this pattern
	 * rule and the specified one are modified accordingly.
	 * 
	 * @param R the pattern rule <code>p' -> q'</code> of the
	 * strategy
	 * @param RR a pattern rule which is equal to this pattern
	 * rule or to <code>R</code>
	 * @param pp a pattern term which is equal to the right-hand
	 * side of this pattern rule when RR is equal to this pattern
	 * rule, or to the left-hand side of R when RR is equal to R
	 * @param x a variable in the domain of a unifier
	 * <code>theta</code>
	 * @param s the term <code>theta(x)</code>
	 * @param iteration the current iteration of the unfolding
	 * operator where this step takes place
	 * @return <code>true</code> iff this step succeeds
	 */
	private boolean narrowWith1a(PatternRuleTrsEeg12 R,
			PatternRuleTrsEeg12 RR, PatternTerm pp,
			Variable x, Term s, int iteration) {

		Term ss = s.deepCopy(pp.getDomainVariable());
		Substitution rho = new Substitution();
		rho.add(x, ss);

		PatternRuleTrsEeg12 RR1 = RR.instantiateWith(rho, iteration);

		if (RR1 == null) return false;

		if (RR == this)
			this.copy(RR1);
		else
			R.copy(RR1);

		return true;
	}

	/**
	 * Implements step 1b of the narrowing strategy presented
	 * in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * This step is applied to this pattern rule, which
	 * corresponds to <code>p -> q</code> in the strategy, and
	 * to the specified pattern rule, which corresponds to
	 * <code>p' -> q'</code> in the strategy. Both this pattern
	 * rule and the specified one are modified accordingly.
	 * 
	 * @param R the pattern rule <code>p' -> q'</code> of the
	 * strategy
	 * @param RR a pattern rule which is equal to this pattern
	 * rule or to <code>R</code>
	 * @param pp a pattern term which is equal to the right-hand
	 * side of this pattern rule when RR is equal to this pattern
	 * rule, or to the left-hand side of R when RR is equal to R
	 * @param x a variable on which the pumping substitution of
	 * <code>pp</code> has to operate as on the specified variable
	 * <code>s</code>
	 * @param s the term <code>theta(x)</code>, which has to
	 * be a variable
	 * @param iteration the current iteration of the unfolding
	 * operator where this step takes place
	 * @return <code>true</code> iff this step succeeds
	 */
	private boolean narrowWith1b(PatternRuleTrsEeg12 R,
			PatternRuleTrsEeg12 RR, PatternTerm pp,
			Variable x, Variable s, int iteration) {

		Term ss = pp.getPumping().get(s);

		if (ss != null) {
			Substitution rho = new Substitution();
			rho.add(x, ss);

			PatternRuleTrsEeg12 RR1 = RR.instantiatePumpingWith(rho, iteration);

			if (RR1 == null) return false;

			if (RR == this)
				this.copy(RR1);
			else
				R.copy(RR1);
		}

		// If ss == null we don't do anything
		// because then the pumping substitution
		// of pp does not "operate" on s.

		return true;
	}

	/**
	 * Implements step 1c of the narrowing strategy presented
	 * in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * This step is applied to this pattern rule, which
	 * corresponds to <code>p -> q</code> in the strategy, and
	 * to the specified pattern rule, which corresponds to
	 * <code>p' -> q'</code> in the strategy. Both this pattern
	 * rule and the specified one are modified accordingly.
	 *  
	 * @param R the pattern rule <code>p' -> q'</code> of the
	 * strategy
	 * @param RR a pattern rule which is equal to this pattern
	 * rule or to <code>R</code>
	 * @param pp a pattern term which is equal to the right-hand
	 * side of this pattern rule when RR is equal to this pattern
	 * rule, or to the left-hand side of R when RR is equal to R
	 * @param x a variable in the domain of a unifier
	 * <code>theta</code>
	 * @param s the term <code>theta(x)</code>, which has to
	 * be a variable
	 * @param iteration the current iteration of the unfolding
	 * operator where this step takes place
	 * @return <code>true</code> iff this step succeeds
	 */
	private boolean narrowWith1c(PatternRuleTrsEeg12 R,
			PatternRuleTrsEeg12 RR, PatternTerm pp,
			Variable x, Variable s, int iteration) {

		Substitution rho = new Substitution();
		rho.add(x, s);

		if (rho.commutesWith(pp.getPumping())) {
			PatternRuleTrsEeg12 RR1 = RR.instantiateClosingWith(rho, iteration);
			if (RR == this && RR1.muRight.remove(x, s) && !RR1.muRight.inDomain(s)) {
				this.left  = RR1.left;
				this.sigmaLeft = RR1.sigmaLeft;
				this.muLeft = RR1.muLeft;

				this.right = RR1.right.apply(rho);
				this.sigmaRight = RR1.sigmaRight;
				this.muRight = RR1.muRight;

				return true;
			}
			else if (RR1.muLeft.remove(x, s) && !RR1.muLeft.inDomain(s)) {
				R.left = (Function) RR1.left.apply(rho);
				R.sigmaLeft = RR1.sigmaLeft;
				R.muLeft = RR1.muLeft;

				R.right = RR1.right;
				R.sigmaRight = RR1.sigmaRight;
				R.muRight = RR1.muRight;

				return true;
			}
		}

		return false;
	}

	/**
	 * Implements step 1d of the narrowing strategy presented
	 * in Sect. 3 of [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * This step is applied to this pattern rule, which
	 * corresponds to <code>p -> q</code> in the strategy, and
	 * to the specified pattern rule, which corresponds to
	 * <code>p' -> q'</code> in the strategy. Both this pattern
	 * rule and the specified one are modified accordingly.
	 * 
	 * @param R the pattern rule <code>p' -> q'</code> of the
	 * strategy
	 * @param RR a pattern rule which is equal to this pattern
	 * rule or to <code>R</code>
	 * @param pp a pattern term which is equal to the right-hand
	 * side of this pattern rule when RR is equal to this pattern
	 * rule, or to the left-hand side of R when RR is equal to R
	 * @param x a variable in the domain of a unifier
	 * <code>theta</code>
	 * @param s the term <code>theta(x)</code>
	 * @param iteration the current iteration of the unfolding
	 * operator where this step takes place
	 */
	private void narrowWith1d(PatternRuleTrsEeg12 R,
			PatternRuleTrsEeg12 RR, PatternTerm pp,
			Variable x, Term s, int iteration) {

		Substitution rho = new Substitution();
		rho.add(x, s);

		if (RR == this) {
			PatternTerm r = this.getRightPatternTerm().rename(rho);
			this.right = r.getBaseTerm();
			this.sigmaRight = r.getPumping();
			this.muRight = r.getClosing();
		}
		else {
			PatternTerm l = R.getLeftPatternTerm().rename(rho);
			R.left = (Function) l.getBaseTerm();
			R.sigmaLeft = l.getPumping();
			R.muLeft = l.getClosing();
		}
	}

	/**
	 * Makes the pumping substitution of the left-hand
	 * side equal to that of the right-hand side and
	 * makes the closing substitution of the left-hand
	 * side equal to that of the right-hand side.
	 * 
	 * Rule (IV) + Lemma 6 of [Emmes, Enger, Giesl, IJCAR'12]
	 * are used here.
	 * 
	 * @param iteration the current iteration of the unfolding
	 * operator where this normalization takes place
	 * @return the normalized rule, or <code>null</code>
	 * if normalization failed
	 */
	private PatternRuleTrsEeg12 normalizedForm(int iteration) {

		// If this rule is already in normal form, then
		// we have nothing to do.
		boolean equalPumping = (this.sigmaLeft == this.sigmaRight) ||
				(this.sigmaLeft.isEmpty() && this.sigmaRight.isEmpty());
		boolean equalClosing = (this.muLeft == this.muRight) ||
				(this.muLeft.isEmpty() && this.muRight.isEmpty());
		if (equalPumping && equalClosing)
			return this;

		// We compute the union of the pumping substitution of
		// the left-hand side with the pumping substitution of
		// the right-hand side.
		Substitution sigma2 = this.sigmaLeft.unionWith(this.sigmaRight);
		// If the union of the pumping substitutions fails,
		// then normalization of this rule fails.
		if (sigma2 == null) return null;

		// We compute the union of the closing substitution of
		// the left-hand side with the closing substitution of
		// the right-hand side.
		Substitution mu2 = this.muLeft.unionWith(this.muRight);
		// If the union of the closing substitutions fails,
		// then normalization of this rule fails.
		if (mu2 == null) return null;

		// We check whether sigma2 and mu2 satisfy the
		// requirements of Lemma 6 for the left-hand side.
		for (Variable x : this.relevantVars(this.left, this.sigmaLeft)) {
			if (this.sigmaLeft.get(x) != sigma2.get(x)) return null;
			if (this.muLeft.get(x) != mu2.get(x)) return null;
		}

		// We check whether sigma2 and mu2 satisfy the
		// requirements of Lemma 6 for the right-hand side.
		for (Variable x : this.relevantVars(this.right, this.sigmaRight)) {
			if (this.sigmaRight.get(x) != sigma2.get(x)) return null;
			if (this.muRight.get(x) != mu2.get(x)) return null;
		}

		// We need to build the parent only if we are in verbose mode.
		ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
				new ParentTrsNonLoopEeg12(this, null, null, false,
						InferenceRuleEeg12.IV, InferenceRuleEeg12.Lemma6) : null);

		// We return the normalized rule.
		return new PatternRuleTrsEeg12(
				this.left, sigma2, mu2,
				this.right, sigma2, mu2,
				iteration,
				parent);
	}

	/**
	 * Renames the domain variables on the left-hand side
	 * of this pattern rule. Also makes the pumping
	 * substitution of the left-hand side equal to that
	 * of the right-hand side and makes the closing
	 * substitution of the left-hand side equal to that
	 * of the right-hand side.
	 * 
	 * If this operation fails, then this rule is not
	 * modified.
	 * 
	 * Rule (IV) + Lemma 4 & Lemma 6 of
	 * [Emmes, Enger, Giesl, IJCAR'12]
	 * are used here.
	 * 
	 * @return <code>true</code> if and only if this
	 * operation succeeds
	 */
	public boolean normalizeStrongly() {

		Function l = this.left;
		Substitution sigmaL = this.sigmaLeft;
		Substitution muL = this.muLeft;

		Term r = this.right;
		Substitution sigmaR = this.sigmaRight;
		Substitution muR = this.muRight;

		// If a pumping or closing substitution is not empty,
		// then we apply Lemma 4 on the left-hand side and on
		// the right-hand side of this pattern rule.
		if (!sigmaL.isEmpty() || !muL.isEmpty() ||
				!sigmaR.isEmpty() || !muR.isEmpty()) {

			PatternTerm renamedL = new PatternTerm(l, sigmaL, muL).rename();
			l = (Function) renamedL.getBaseTerm();
			sigmaL = renamedL.getPumping();
			muL = renamedL.getClosing();

			PatternTerm renamedR = new PatternTerm(r, sigmaR, muR).rename();
			r = renamedR.getBaseTerm();
			sigmaR = renamedR.getPumping();
			muR = renamedR.getClosing();
		}

		// We compute the union of the pumping substitution of
		// the left-hand side with the pumping substitution of
		// the right-hand side.
		Substitution sigma = sigmaL.unionWith(sigmaR);
		// If the union of the pumping substitutions fails,
		// then normalization of this rule fails.
		if (sigma == null) return false;

		// We compute the union of the closing substitution of
		// the left-hand side with the closing substitution of
		// the right-hand side.
		Substitution mu = muL.unionWith(muR);
		// If the union of the closing substitutions fails,
		// then normalization of this rule fails.
		if (mu == null) return false;

		// We check whether sigma and mu satisfy the
		// requirements of Lemma 6 for the left-hand side.
		for (Variable x : this.relevantVars(l, sigmaL)) {
			if (sigmaL.get(x) != sigma.get(x)) return false;
			if (muL.get(x) != mu.get(x)) return false;
		}

		// We check whether sigma and mu satisfy the
		// requirements of Lemma 6 for the right-hand side.
		for (Variable x : this.relevantVars(r, sigmaR)) {
			if (sigmaR.get(x) != sigma.get(x)) return false;
			if (muR.get(x) != mu.get(x)) return false;
		}

		// If we get here, then everything went fine.
		// Hence, we can safely modify this rule.
		this.left = l;
		this.right = r;
		this.sigmaLeft = this.sigmaRight = sigma;
		this.muLeft = this.muRight = mu;

		return true;
	}

	/**
	 * Returns the set of relevant variables of an input pattern
	 * term whose base term is the specified term and whose pumping
	 * substitution is the specified substitution (Definition 5 of
	 * [Emmes, Enger, Giesl, IJCAR'12]).
	 * 
	 * @param t the base term of the input pattern term
	 * @param sigma the pumping substitution of the input
	 * pattern term
	 * @return the set of relevant variables of the input
	 * pattern term
	 */
	private Set<Variable> relevantVars(Term t, Substitution sigma) {
		// The value to return at the end.
		// The set of relevant variables of the input
		// pattern term contains at least the variables
		// of its base term.
		Set<Variable> relevant = t.getVariables();

		// Some temporary sets for computing the result.
		Set<Variable> X = new HashSet<Variable>(relevant);
		Set<Variable> Xsigma = new HashSet<Variable>();

		while (!X.isEmpty()) {
			for (Variable x : X) {
				Term s = sigma.get(x);
				if (s != null)
					for (Variable v : s.getVariables())
						if (!relevant.contains(v)) {
							relevant.add(v);
							Xsigma.add(v);
						}
			}
			X.clear();
			X.addAll(Xsigma);
			Xsigma.clear();
		}

		return relevant;
	}

	/**
	 * Implements (V) of [Emmes, Enger, Giesl, IJCAR'12]:
	 * instantiates this pattern rule with the provided
	 * substitution.
	 * 
	 * This method checks whether the provided substitution
	 * <code>rho</code> is suitable i.e.,
	 * <code>Vars(rho)</code> is disjoint from
	 * <code>dv(l)</code> and <code>dv(r)</code> where
	 * <code>l</code> (resp. <code>r</code>) denotes the
	 * left-hand (resp. right-hand) side of this pattern
	 * rule. If <code>rho</code> is not suitable then
	 * <code>null</code> is returned.
	 * 
	 * @param rho a substitution for instantiating this
	 * pattern rule
	 * @param iteration the current iteration of the unfolding
	 * operator where this instantiation takes place
	 * @return if <code>rho</code> is suitable, then the result
	 * of instantiating this pattern rule with <code>rho</code>,
	 * else <code>null</code>
	 */
	private PatternRuleTrsEeg12 instantiateWith(Substitution rho, int iteration) {

		// The value to return at the end.
		PatternRuleTrsEeg12 result = null;

		// We compute the union of the domains of the
		// pumping and the closing substitutions.
		Set<Variable> domains = this.sigmaLeft.getDomain();
		domains.addAll(this.muLeft.getDomain());
		domains.addAll(this.sigmaRight.getDomain());
		domains.addAll(this.muRight.getDomain());

		// We check whether the provided substitution rho
		// is suitable.
		if (rho.isDisjointFrom(domains)) {
			// We instantiate the left-hand side with rho.
			PatternTerm leftInstantiated = this.getLeftPatternTerm().instantiateWith(rho);

			// We instantiate the right-hand side with rho.
			PatternTerm rightInstantiated = this.getRightPatternTerm().instantiateWith(rho);

			/*
			result = new PatternRule(leftInstantiated, rightInstantiated,
					iteration, new ParentTRS_NonLoop(this, null, null, false, "(V)"));
			 */

			Function l = (Function) leftInstantiated.getBaseTerm();
			Substitution sigma1 = leftInstantiated.getPumping();
			Substitution mu1 = leftInstantiated.getClosing();

			Term r = rightInstantiated.getBaseTerm();
			Substitution sigma2 = (this.sigmaLeft == this.sigmaRight ? sigma1 : rightInstantiated.getPumping());
			Substitution mu2 = (this.muLeft == this.muRight ? mu1 : rightInstantiated.getClosing());

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
					new ParentTrsNonLoopEeg12(
							this, null, null, false, InferenceRuleEeg12.V) : null);

			result = new PatternRuleTrsEeg12(l, sigma1, mu1, r, sigma2, mu2,
					iteration, parent);
		}

		return result;
	}

	/**
	 * Implements (VII) of [Emmes, Enger, Giesl, IJCAR'12]:
	 * instantiates the pumping substitutions of this pattern
	 * rule with the provided substitution.
	 * 
	 * If the provided substitution is not suitable (i.e., it
	 * does not commute with a pumping or a closing substitution
	 * of this pattern rule) then <code>null</code> is returned.
	 * 
	 * @param rho a substitution for instantiating
	 * the pumping substitutions of this pattern rule
	 * @param iteration the current iteration of the unfolding
	 * operator where this instantiation takes place
	 * @return the result of instantiating the pumping
	 * substitutions of this pattern rule with the provided
	 * substitution, or <code>null</code> if the provided
	 * substitution is not suitable  
	 */
	private PatternRuleTrsEeg12 instantiatePumpingWith(Substitution rho, int iteration) {
		// The value to return at the end.
		PatternRuleTrsEeg12 R = null;

		// The substitutions on the left-hand side.
		Substitution sigma_l = this.sigmaLeft;
		Substitution mu_l = this.muLeft;
		// The substitutions on the right-hand side.
		Substitution sigma_r = this.sigmaRight;
		Substitution mu_r = this.muRight;

		// If the provided substitution is suitable, then
		// we apply (VII). Otherwise, we return null.
		if (rho.commutesWith(sigma_l) && rho.commutesWith(mu_l) &&
				rho.commutesWith(sigma_r) && rho.commutesWith(mu_r)) {

			// We need to build the parent only if we are in verbose mode.
			ParentTrs parent = (Options.getInstance().isInVerboseMode() ?
					new ParentTrsNonLoopEeg12(
							this, null, null, false, InferenceRuleEeg12.VII) : null);

			R = new PatternRuleTrsEeg12(
					this.left, sigma_l.composeWith(rho), mu_l,
					this.right, sigma_r.composeWith(rho), mu_r,
					iteration,
					parent);
		}

		return R;
	}

	/**
	 * Implements (VIII) of [Emmes, Enger, Giesl, IJCAR'12]:
	 * instantiates the closing substitutions of this pattern
	 * rule with the provided substitution.
	 * 
	 * @param rho a substitution for instantiating
	 * the closing substitutions of this pattern rule
	 * @param iteration the current iteration of the unfolding
	 * operator where this instantiation takes place
	 * @return the result of instantiating the closing
	 * substitutions of this pattern rule with the provided
	 * substitution
	 */
	private PatternRuleTrsEeg12 instantiateClosingWith(Substitution rho, int iteration) {
		// We need to build the parent only if we are in verbose mode.
		ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
				new ParentTrsNonLoopEeg12(
						this, null, null, false, InferenceRuleEeg12.VIII) : null);

		return new PatternRuleTrsEeg12(
				this.left, this.sigmaLeft, this.muLeft.composeWith(rho),
				this.right, this.sigmaRight, this.muRight.composeWith(rho),
				iteration,
				parent);
	}

	/**
	 * Rewrites the base term on the right-hand side of
	 * this pattern rule, at the specified position, using
	 * the specified rule.
	 * 
	 * @param R a rule for rewriting this pattern rule
	 * @param p a position in the base term on the
	 * right-hand side of this pattern rule where the
	 * rewriting has to take place
	 * @param iteration the current iteration of the unfolding
	 * operator where this rewriting takes place
	 * @return the pattern rule resulting from the rewriting,
	 * or <code>null</code> if the rewriting fails
	 */
	private PatternRuleTrsEeg12 rewriteWith(RuleTrs R, Position p, int iteration) {
		// The value to return at the end.
		PatternRuleTrsEeg12 result = null;

		// We only rewrite the base term on the right-hand side
		// of this pattern rule. We do not rewrite the pumping
		// and closing substitutions.
		Term t_p = this.right.get(p);

		// We only rewrite the subterms located at a non-variable position.
		if (!t_p.isVariable()) {

			// First, we try a usual rewriting with R.
			Substitution theta = new Substitution();
			if (R.getLeft().isMoreGeneralThan(t_p, theta)) {
				
				// We need to build the parent only if we are in verbose mode.
				ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
						new ParentTrsNonLoopEeg12(this, R, p, false, InferenceRuleEeg12.IX) : null);
				
				Term u = this.right.replace(p, R.getRight().apply(theta));
				result = new PatternRuleTrsEeg12(
						this.left, this.sigmaLeft, this.muLeft,
						u, this.sigmaRight, this.muRight,
						iteration,
						parent);
			}
			else {
				// If usual rewriting fails, then we try to instantiate
				// this rule to enforce rewriting.
				theta.clear();
				if (t_p.isMoreGeneralThan(R.getLeft(), theta)) {
					PatternRuleTrsEeg12 instantiated = this.instantiateWith(theta, iteration);
					if (instantiated != null) {
						// Now, we have instantiated.right|_p = R.left.

						// We need to build the parent only if we are in verbose mode.
						ParentTrs parent = (Options.getInstance().isInVerboseMode() ? 
								new ParentTrsNonLoopEeg12(this, R, p, false,
										InferenceRuleEeg12.V, InferenceRuleEeg12.IX) : null);

						Term u = instantiated.right.replace(p, R.getRight());
						result = new PatternRuleTrsEeg12(
								instantiated.left, instantiated.sigmaLeft, instantiated.muLeft, 
								u, instantiated.sigmaRight, instantiated.muRight,
								iteration,
								parent);
					}
				}
			}
		}

		/*
		// Then, we rewrite the pumping substitution sigma.
		for (Substitution eta : sigma.rewriteWith(IR)) {
			PatternRule rewritten = new PatternRule(
					this.left, this.sigmaLeft, this.muLeft,
					t, eta, mu,
					iteration,
					new ParentTRS_NonLoop(this, null, null, false, rule));
			if (add(parameters, IR, proof, rewritten, result))
				return result;
		}

		// Finally, we rewrite the closing substitution mu.
		for (Substitution eta : mu.rewriteWith(IR)) {
			PatternRule rewritten = new PatternRule(
					this.left, this.sigmaLeft, this.muLeft,
					t, sigma, eta,
					iteration,
					new ParentTRS_NonLoop(this, null, null, false, rule));
			if (add(parameters, IR, proof, rewritten, result))
				return result;
		}
		 */

		return result;
	}

	/**
	 * Returns a String representation of this pattern rule
	 * relatively to the given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a String representation of this pattern rule
	 */
	public String toString(Map<Variable,String> variables) {
		return this.left.toString(variables, false) +
				this.sigmaLeft.toString(variables) + "^n" +
				this.muLeft.toString(variables) +
				" -> " +
				this.right.toString(variables, false) +
				this.sigmaRight.toString(variables) + "^n" +
				this.muRight.toString(variables);
	}

	/**
	 * Returns a string representation of this
	 * pattern rule.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<Variable,String>());
	}
}
