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

package fr.univreunion.nti.term.pattern.simple;

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.PatternTerm;
import fr.univreunion.nti.term.pattern.PatternUtils;

/**
 * A simple pattern term, i.e., a pattern term
 * <code>(s, eta)</code> such that
 * <code>eta = (sigma_1, ..., sigma_l, mu)</code>
 * with, for all <code>x \in Var(s)</code>,
 * <code>sigma_i(x) = c^{a_i}(x)</code> and
 * <code>mu(x) = c^b(u)</code> for
 * some 1-context <code>c</code>,
 * some <code>a_1,...,a_l,b \in \nat</code> and
 * some <code>u \in T(Sigma,X)</code>.
 * <p>
 * This class stores both the pattern-term representation
 * <code>p = (s, eta)</code>, where <code>eta</code> is a
 * simple pattern substitution, and an element of
 * <code>upsilon(p)</code>. The latter is represented by the
 * field <code>upsilon</code> and is obtained from the base
 * term after applying the substitution <code>theta</code>
 * carried by <code>eta</code>.
 *
 * <p>Simple pattern terms and their unification are defined by E. Payet in
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025, Sect. 4.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class SimplePatternTerm extends PatternTerm implements Iterable<Position> {

	/**
	 * An element of <code>upsilon(p)</code>, where
	 * <code>p</code> denotes this pattern term.
	 */
	private final Term upsilon;

	/**
	 * Builds a simple pattern term from the specified base term,
	 * pattern substitution and upsilon term.
	 * <p>
	 * <b>It is supposed that <code>eta</code> has the correct
	 * form for building simple pattern terms (NOT CHECKED)</b>.
	 * It is also supposed that <code>upsilon</code> is the
	 * element of <code>upsilon(p)</code> corresponding to
	 * <code>p = (t,eta)</code> (NOT CHECKED). These invariants
	 * are established by the public factory methods.
	 *
	 * @param t the base term of this pattern term
	 * @param eta the pattern substitution of this pattern term
	 * @param upsilon the term <code>upsilon(p)</code> where
	 * <code>p</code> denotes this pattern term
	 */
	private SimplePatternTerm(Term t, SimplePatternSubstitution eta, Term upsilon) {
		super(t, eta);
		this.upsilon = upsilon;
	}

	/**
	 * Tries to build a simple pattern term from a base term and
	 * the substitutions <code>[sigma,mu]</code>, i.e., the case
	 * <code>l = 1</code> of the representation
	 * <code>[sigma_1,...,sigma_l,mu]</code>.
	 * <p>
	 * This method first attempts to build the corresponding simple
	 * pattern substitution <code>eta</code>, then delegates to
	 * <code>tryBuild(Term, PatternSubstitution)</code>.
	 * <p>
	 * <b>It is supposed that <code>sigma</code> only consists
	 * of mappings of the form <code>x -> c(x)</code> where
	 * <code>c</code> is a simple context whose hole is
	 * <code>x</code> (NOT CHECKED)</b>.
	 *
	 * @param t the base term of this pattern term
	 * @param sigma the pumping substitution of this pattern term
	 * @param mu the closing substitution of this pattern term
	 * @return a simple pattern term, or <code>null</code>
	 * if the simple pattern substitution <code>eta</code>
	 * or the simple pattern term could not be constructed
	 */
	public static SimplePatternTerm tryBuild(
			Term t, Substitution sigma, Substitution mu) {

		SimplePatternSubstitution patternSubstitution =
				SimplePatternSubstitution.tryBuild(List.of(sigma, mu));

		if (patternSubstitution != null)
			return tryBuild(t, patternSubstitution);

		return null;
	}

	/**
	 * Tries to build a simple pattern term from the specified
	 * base term and pattern substitution.
	 * <p>
	 * The provided pattern substitution must be simple. This method
	 * uses the substitution <code>theta</code> carried by
	 * <code>eta</code>, restricts it to the variables of the base
	 * term, moves ground subterms of the base term into this
	 * restricted substitution, simplifies the resulting pair, and
	 * then computes the corresponding element of <code>upsilon(p)</code>.
	 * <p>
	 * The provided pattern substitution <code>eta</code> is not
	 * modified directly.
	 *
	 * @param t the base term of this pattern term
	 * @param eta the pattern substitution of this
	 * pattern term
	 * @return a simple pattern term, or <code>null</code>
	 * if no pattern term could be constructed from the
	 * specified pattern substitution
	 */
	public static SimplePatternTerm tryBuild(
			Term t, PatternSubstitution eta) {

		if (eta instanceof SimplePatternSubstitution simplePatternSubstitution)
			return tryBuildWithSimpleSubstitution(t, simplePatternSubstitution);

		return null;
	}

	/**
	 * Tries to build a simple pattern term from the specified
	 * base term and already validated simple pattern substitution.
	 *
	 * @param baseTerm the base term of this pattern term
	 * @param patternSubstitution the simple pattern substitution
	 * of this pattern term
	 * @return a simple pattern term, or <code>null</code> if no
	 * pattern term could be constructed
	 */
	private static SimplePatternTerm tryBuildWithSimpleSubstitution(
			Term baseTerm,
			SimplePatternSubstitution patternSubstitution) {

		return tryBuildWithSimpleSubstitution(
				baseTerm,
				patternSubstitution,
				baseTerm.getVariables(),
				false);
	}

	/**
	 * Tries to build a simple pattern term after replacing a subterm of this
	 * pattern term's base term.
	 * <p>
	 * This pattern term, the replacement and the provided substitution are not
	 * modified. Variable collection uses a short-lived compact workspace suited
	 * to the freshly constructed base term.
	 *
	 * @param position the position to replace in this pattern term's base term
	 * @param replacement the replacement term
	 * @param patternSubstitution the pattern substitution of the result
	 * @return the resulting simple pattern term, or {@code null} if it could not
	 * be constructed
	 * @throws IndexOutOfBoundsException if {@code position} is not valid
	 */
	public SimplePatternTerm tryBuildReplacingBaseTerm(
			Position position,
			Term replacement,
			PatternSubstitution patternSubstitution) {

		Term replacedBaseTerm = this.getBaseTerm().replace(position, replacement);
		if (!(patternSubstitution instanceof SimplePatternSubstitution simpleSubstitution))
			return null;

		Set<Variable> variables = new CompactVariableSet();
		replacedBaseTerm.collectVariablesInto(variables);

		return tryBuildWithSimpleSubstitution(
				replacedBaseTerm,
				simpleSubstitution,
				variables,
				true);
	}

	/**
	 * Tries to build a simple pattern term using the already collected variables
	 * of its base term.
	 *
	 * @param baseTerm the base term of this pattern term
	 * @param patternSubstitution the simple pattern substitution
	 * @param baseVariables the variables of {@code baseTerm}
	 * @param freshBaseTerm whether {@code baseTerm} is invocation-local and can
	 * be retained when no direct ground argument has to be extracted
	 * @return a simple pattern term, or {@code null} if it could not be built
	 */
	private static SimplePatternTerm tryBuildWithSimpleSubstitution(
			Term baseTerm,
			SimplePatternSubstitution patternSubstitution,
			Collection<Variable> baseVariables,
			boolean freshBaseTerm) {

		Substitution hatFunctionSubstitution =
				patternSubstitution.getHatFunctionSubstitution().restrictTo(baseVariables);
		// We move the ground subterms of baseTerm into the
		// hat-function substitution: each such subterm is
		// replaced by a fresh variable, which is then mapped
		// to the original subterm by the substitution.
		if (!freshBaseTerm || hasDirectGroundArgument(baseTerm))
			baseTerm = baseTerm.toSubstitution(hatFunctionSubstitution);

		// We simplify baseTerm and the hat-function substitution
		// before computing upsilon(p).
		baseTerm = PatternUtils.simplify(baseTerm, hatFunctionSubstitution);
		Term upsilon = baseTerm.apply(hatFunctionSubstitution);

		SimplePatternSubstitution simplifiedSubstitution =
				SimplePatternSubstitution.tryBuildTakingOwnership(
						hatFunctionSubstitution);
		if (simplifiedSubstitution != null)
			return new SimplePatternTerm(baseTerm, simplifiedSubstitution, upsilon);

		return null;
	}

	/**
	 * Checks whether an ordinary function has a direct ground argument. Other
	 * term forms retain their historical substitution-form construction.
	 *
	 * @param term the term to inspect
	 * @return {@code true} when the historical construction must run
	 */
	private static boolean hasDirectGroundArgument(Term term) {
		if (term.getClass() != Function.class) return true;

		int arity = term.getRootSymbol().getArity();
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++)
			if (term.get(argumentIndex).isGround()) return true;
		return false;
	}

	/**
	 * A variable set with four inline entries and an array only when needed.
	 * It is used solely while building a freshly replaced pattern base term.
	 */
	private static final class CompactVariableSet extends AbstractSet<Variable> {

		private Variable first;
		private Variable second;
		private Variable third;
		private Variable fourth;
		private Variable[] overflow;
		private int size;

		@Override
		public boolean add(Variable variable) {
			if (this.contains(variable)) return false;

			switch (this.size) {
				case 0 -> this.first = variable;
				case 1 -> this.second = variable;
				case 2 -> this.third = variable;
				case 3 -> this.fourth = variable;
				default -> this.addOverflow(variable);
			}
			this.size++;
			return true;
		}

		@Override
		public boolean contains(Object candidate) {
			for (int index = 0; index < this.size; index++)
				if (this.variableAt(index).equals(candidate)) return true;
			return false;
		}

		@Override
		public Iterator<Variable> iterator() {
			return new Iterator<>() {
				private int index;

				@Override
				public boolean hasNext() {
					return this.index < CompactVariableSet.this.size;
				}

				@Override
				public Variable next() {
					if (!this.hasNext()) throw new NoSuchElementException();
					return CompactVariableSet.this.variableAt(this.index++);
				}
			};
		}

		@Override
		public int size() {
			return this.size;
		}

		private void addOverflow(Variable variable) {
			int overflowIndex = this.size - 4;
			if (this.overflow == null)
				this.overflow = new Variable[4];
			else if (overflowIndex == this.overflow.length)
				this.overflow = Arrays.copyOf(this.overflow, this.overflow.length * 2);
			this.overflow[overflowIndex] = variable;
		}

		private Variable variableAt(int index) {
			return switch (index) {
				case 0 -> this.first;
				case 1 -> this.second;
				case 2 -> this.third;
				case 3 -> this.fourth;
				default -> this.overflow[index - 4];
			};
		}
	}

	/**
	 * Builds the simple pattern term <code>t^*</code>,
	 * whose pattern substitution is empty and whose
	 * <code>upsilon</code> term is <code>t</code>.
	 *
	 * @param t the base term of this pattern term
	 * @return a simple pattern term
	 */
	public static SimplePatternTerm of(Term t) {
		return new SimplePatternTerm(t, SimplePatternSubstitution.empty(), t);
	}

	/**
	 * Returns a deep copy of this pattern term, i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @return a deep copy of this pattern term
	 */
	@Override
	public SimplePatternTerm deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a deep copy of this pattern term, i.e.,
	 * a copy where each subterm is also copied, even
	 * variable subterms.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern term
	 */
	@Override
	public SimplePatternTerm deepCopy(Map<Term, Term> copies) {
		return new SimplePatternTerm(this.getBaseTerm().deepCopy(copies),
				this.getPatternSubstitution().deepCopy(copies),
				this.upsilon.deepCopy(copies));
	}

	/**
	 * Returns the subterm of this pattern term
	 * at the given position.
	 *
	 * @param position a position
	 * @return the subterm of this pattern term
	 * at the specified position, or
	 * <code>null</code> if <code>position</code> is not
	 * a valid position in this pattern term
	 */
	public SimplePatternTerm get(Position position) {
		Term baseSubterm = this.getBaseTerm().get(position);

		if (baseSubterm == null) return null;

		return SimplePatternTerm.tryBuild(baseSubterm, this.getPatternSubstitution());
	}

	/**
	 * Returns the term <code>upsilon(p)</code> where
	 * <code>p</code> denotes this pattern term.
	 *
	 * @return <code>upsilon(p)</code> where
	 * <code>p</code> denotes this pattern term
	 */
	public Term getUpsilon() {
		return this.upsilon;
	}

	/**
	 * Returns the pattern substitution of
	 * this simple pattern term.
	 *
	 * @return the pattern substitution of
	 * this simple pattern term
	 */
	@Override
	public SimplePatternSubstitution getPatternSubstitution() {
		// The pattern substitution of this simple pattern term
		// is simple by construction.
		return (SimplePatternSubstitution) super.getPatternSubstitution();
	}

	/**
	 * Computes the indexes to use to weaken this pattern term
	 * w.r.t. the provided one.
	 * <p>
	 * It is supposed that the arity of this pattern term and
	 * that of <code>otherPatternTerm</code> are both equal to 1.
	 * <p>
	 * Each negative index in the returned value means that no
	 * corresponding index was determined.
	 *
	 * @param otherPatternTerm a pattern term for weakening this
	 * pattern term
	 * @return the indexes to use for weakening, or
	 * <code>null</code> if no consistent weakening indexes could
	 * be computed
	 */
	public WeakeningIndexes computeWeakeningIndexes(
			SimplePatternTerm otherPatternTerm) {

		int functionWeakeningIndex = -1;
		int hatWeakeningIndex = -1;

		// We consider the disagreement positions of this
		// pattern term and otherPatternTerm.
		for (Position position : otherPatternTerm.upsilon.dpos(this.upsilon, true)) {
			Term thisSubterm = this.upsilon.get(position);
			Term otherSubterm = otherPatternTerm.upsilon.get(position);
			if (!(thisSubterm instanceof HatFunction thisHatFunction))
				continue;

			if (otherSubterm instanceof Function) {
				WeakeningIndexUpdate updatedFunctionWeakeningIndex =
						updateFunctionWeakeningIndex(
								functionWeakeningIndex,
								thisHatFunction,
								otherSubterm);
				if (!updatedFunctionWeakeningIndex.successful()) return null;
				functionWeakeningIndex = updatedFunctionWeakeningIndex.weakeningIndex();
			}
			else if (otherSubterm instanceof HatFunction otherHatFunction) {
				hatWeakeningIndex = updateHatWeakeningIndex(
						hatWeakeningIndex,
						thisHatFunction,
						otherHatFunction);
			}
		}

		return new WeakeningIndexes(functionWeakeningIndex, hatWeakeningIndex);
	}

	/**
	 * The indexes to use when weakening a simple pattern term.
	 *
	 * @param functionWeakeningIndex the index to use when
	 * weakening ordinary function occurrences
	 * @param hatWeakeningIndex the index to use when weakening
	 * hat function occurrences
	 */
	public record WeakeningIndexes(
			int functionWeakeningIndex,
			int hatWeakeningIndex) {}

	/**
	 * The result of updating a weakening index.
	 *
	 * @param successful whether the update succeeded
	 * @param weakeningIndex the updated weakening index
	 */
	private record WeakeningIndexUpdate(boolean successful, int weakeningIndex) {}

	/**
	 * Updates the weakening index computed from positions where
	 * this pattern term has a hat function and the other pattern
	 * term has an ordinary function.
	 *
	 * @param functionWeakeningIndex the weakening index computed
	 * so far
	 * @param thisHatFunction the hat function occurring in this
	 * pattern term
	 * @param otherSubterm the ordinary function occurring in the
	 * other pattern term
	 * @return a successful update with the new weakening index, or
	 * a failed update if the current disagreement position is
	 * incompatible with the weakening index computed so far
	 */
	private static WeakeningIndexUpdate updateFunctionWeakeningIndex(
			int functionWeakeningIndex,
			HatFunction thisHatFunction,
			Term otherSubterm) {

		HatFunctionSymbol hatSymbol = thisHatFunction.getRootSymbol();
		int thisStep = thisHatFunction.getA();
		int thisOffset = thisHatFunction.getB();
		// Here, thisSubterm = c^{thisStep,thisOffset}(u1).
		int[] exponentHolder = new int[1];
		Term contextArgument = PatternUtils.towerOfContexts(
				otherSubterm,
				hatSymbol.getSimpleContext(),
				hatSymbol.getVariable(),
				exponentHolder);
		int otherExponent = exponentHolder[0];
		if (hasAbsorbableExtraFunctionExponent(otherExponent, thisOffset))
			return updateFunctionWeakeningIndexFromExtraExponent(
					functionWeakeningIndex,
					thisStep,
					otherExponent - thisOffset);

		if (hasZeroFunctionWeakening(
				otherExponent,
				thisOffset,
				contextArgument,
				thisHatFunction.getArgument()))
			// Here, otherSubterm = u and
			// thisSubterm = c^{thisStep,0}(u).
			return new WeakeningIndexUpdate(true, 0);

		return new WeakeningIndexUpdate(true, functionWeakeningIndex);
	}

	/**
	 * Checks whether an ordinary function occurrence provides an
	 * extra context exponent that must be absorbed by the current
	 * function weakening index.
	 *
	 * @param otherExponent the context exponent found in the other
	 * term
	 * @param thisOffset the offset of the current hat function
	 * @return <code>true</code> iff there is an extra exponent to
	 * absorb
	 */
	private static boolean hasAbsorbableExtraFunctionExponent(
			int otherExponent, int thisOffset) {

		return 0 < otherExponent && thisOffset < otherExponent;
	}

	/**
	 * Updates the function weakening index from an extra context
	 * exponent.
	 *
	 * @param functionWeakeningIndex the weakening index computed
	 * so far
	 * @param thisStep the step of the current hat function
	 * @param extraFunctionExponent the extra exponent to absorb
	 * @return a successful update with the new weakening index, or
	 * a failed update if the extra exponent is incompatible with the
	 * weakening index computed so far
	 */
	private static WeakeningIndexUpdate updateFunctionWeakeningIndexFromExtraExponent(
			int functionWeakeningIndex,
			int thisStep,
			int extraFunctionExponent) {

		// Here, otherSubterm = c^otherExponent(u),
		// i.e., otherSubterm = c^{0,otherExponent}(u).
		// The extra exponent must be absorbed by
		// iterations of thisStep.
		if (extraFunctionExponent % thisStep != 0)
			return new WeakeningIndexUpdate(false, functionWeakeningIndex);

		int candidateFunctionIndex = extraFunctionExponent / thisStep;
		return mergeFunctionWeakeningIndex(
				functionWeakeningIndex, candidateFunctionIndex);
	}

	/**
	 * Merges a candidate function weakening index with the one
	 * computed so far.
	 *
	 * @param functionWeakeningIndex the weakening index computed
	 * so far
	 * @param candidateFunctionIndex the candidate weakening index
	 * computed at the current disagreement position
	 * @return a successful update if both indexes are compatible,
	 * or a failed update otherwise
	 */
	private static WeakeningIndexUpdate mergeFunctionWeakeningIndex(
			int functionWeakeningIndex,
			int candidateFunctionIndex) {

		if (functionWeakeningIndex < 0)
			return new WeakeningIndexUpdate(true, candidateFunctionIndex);
		if (candidateFunctionIndex != functionWeakeningIndex)
			return new WeakeningIndexUpdate(false, functionWeakeningIndex);

		return new WeakeningIndexUpdate(true, functionWeakeningIndex);
	}

	/**
	 * Checks whether an ordinary function occurrence matches the
	 * zero weakening index case.
	 *
	 * @param otherExponent the context exponent found in the other
	 * term
	 * @param thisOffset the offset of the current hat function
	 * @param contextArgument the argument remaining after extracting
	 * the context tower from the other term
	 * @param thisArgument the argument of the current hat function
	 * @return <code>true</code> iff the zero weakening index case
	 * applies
	 */
	private static boolean hasZeroFunctionWeakening(
			int otherExponent,
			int thisOffset,
			Term contextArgument,
			Term thisArgument) {

		return otherExponent == 0 &&
				thisOffset == 0 &&
				contextArgument.deepEquals(thisArgument);
	}

	/**
	 * Updates the weakening index computed from positions where
	 * both pattern terms have hat functions.
	 *
	 * @param hatWeakeningIndex the weakening index computed so far
	 * @param thisHatFunction the hat function occurring in this
	 * pattern term
	 * @param otherHatFunction the hat function occurring in the
	 * other pattern term
	 * @return the updated weakening index
	 */
	private static int updateHatWeakeningIndex(
			int hatWeakeningIndex,
			HatFunction thisHatFunction,
			HatFunction otherHatFunction) {

		HatFunctionSymbol hatSymbol = thisHatFunction.getRootSymbol();
		int thisStep = thisHatFunction.getA();
		int thisOffset = thisHatFunction.getB();
		if (hatSymbol != otherHatFunction.getRootSymbol())
			return hatWeakeningIndex;

		int otherStep = otherHatFunction.getA();
		int otherOffset = otherHatFunction.getB();
		// Here, otherSubterm = c^{otherStep,otherOffset}(u2).
		if (otherStep <= thisStep && thisOffset < otherOffset) {
			int extraHatExponent = otherOffset - thisOffset;
			int roundingOffset = (extraHatExponent % thisStep == 0 ? 0 : 1);
			return Math.max(
					hatWeakeningIndex,
					extraHatExponent / thisStep + roundingOffset);
		}

		return hatWeakeningIndex;
	}

	/**
	 * Checks if this pattern term is a variable.
	 *
	 * @return <code>true</code> iff this pattern
	 * term is a variable
	 */
	public boolean isVariable() {
		return this.upsilon.isVariable();
	}

	/**
	 * Returns an iterator over the positions of
	 * this pattern term.
	 *
	 * @return an iterator over the positions of the base term
	 */
	@Override
	public Iterator<Position> iterator() {
		return this.getBaseTerm().iterator();
	}

	/**
	 * Attempts to compute the most general unifier of
	 * this pattern term and the provided one.
	 * <p>
	 * This method implements the unification algorithm
	 * described in the Payet (2025) article cited in the class documentation.
	 * <p>
	 * Neither this pattern term nor the provided one are
	 * modified by this method.
	 *
	 * @param otherPatternTerm a pattern term
	 * @return the most general unifier of this pattern
	 * term and the provided one, or <code>null</code>
	 * in case of failure
	 */
	@Override
	public SimplePatternSubstitution unifyWith(SimplePatternTerm otherPatternTerm) {
		return this.tryUnifyUpsilonWith(otherPatternTerm.upsilon);
	}

	/**
	 * Attempts to unify the <code>upsilon</code> term of this
	 * pattern term with the specified term.
	 *
	 * @param otherTerm a term
	 * @return the resulting simple pattern substitution, or
	 * <code>null</code> if unification failed or if the computed
	 * unifier does not define a simple pattern substitution
	 */
	private SimplePatternSubstitution tryUnifyUpsilonWith(Term otherTerm) {
		Substitution unifier = new Substitution();
		if (this.upsilon.isUnifiableWith(otherTerm, unifier))
			return SimplePatternSubstitution.tryBuildTakingOwnership(unifier);

		return null;
	}

	/**
	 * Attempts to compute the most general unifier of this
	 * pattern term with the left-hand side of the provided
	 * pattern rule. If the provided rule is a fact (i.e.,
	 * its right-hand side is empty), then also attempts to
	 * compute the most general unifier of this pattern term
	 * with weakened versions of the left-hand side of the
	 * provided rule.
	 * <p>
	 * Neither this pattern term nor the provided pattern
	 * rule are modified by this method.
	 *
	 * @param patternRule a pattern rule
	 * @return a collection of most general unifiers
	 */
	@Override
	public Collection<PatternSubstitution> unifyWith(PatternRuleLp patternRule) {

		// The value to return at the end.
		Collection<PatternSubstitution> result = new LinkedList<>();

		// First, we try to unify this pattern term
		// with the left-hand side of patternRule.
		SimplePatternSubstitution directUnifier = this.unifyWith(patternRule.getLeft());

		if (directUnifier != null)
			// If direct unification succeeds,
			// we keep the resulting unifier.
			result.add(directUnifier);

		this.addWeakeningUnifiers(patternRule, result);

		return result;
	}

	/**
	 * Adds the unifiers obtained from weakened left-hand sides
	 * of the specified pattern rule.
	 *
	 * @param patternRule a pattern rule
	 * @param unifiers the collection to fill with successful
	 * weakened unifiers
	 */
	private void addWeakeningUnifiers(
			PatternRuleLp patternRule,
			Collection<PatternSubstitution> unifiers) {

		// We try to unify this pattern term with weakened
		// left-hand sides when the rule is a fact.
		for (Term weakenedLeft : patternRule.weakenLeftIfFact(this)) {
			SimplePatternSubstitution weakenedUnifier =
					this.tryUnifyUpsilonWith(weakenedLeft);
			if (weakenedUnifier != null) unifiers.add(weakenedUnifier);
		}
	}

	/**
	 * Performs the following actions.
	 * <ol>
	 * <li>
	 * Replaces each mapping
	 * <code>x -> c^{a,b}(u)</code> in the
	 * simple pattern substitution of this
	 * pattern term by
	 * <code>x -> c^{a,a*hatWeakeningIndex+b}(u)</code>.
	 * Indeed,
	 * <code>c^{a,a*hatWeakeningIndex+b}(u)</code>
	 * describes the set
	 * <code>{c^{a*n+a*hatWeakeningIndex+b}(u) | n \in \nat}</code>
	 * = <code>{c^{a*(n+hatWeakeningIndex)+b}(u) | n \in \nat}</code>
	 * = <code>{c^{a*n+b}(u) | n >= hatWeakeningIndex}</code>
	 * which is included in
	 * <code>{c^{a*n+b}(u) | n \in \nat}</code>.
	 * </li>
	 * <li>Replaces each mapping
	 * <code>x -> c^{a,b}(u)</code> in the
	 * simple pattern substitution of this
	 * pattern term by
	 * <code>x -> c^{a,a,a*hatWeakeningIndex+b}(u)</code>.
	 * Indeed,
	 * <code>c^{a,a,a*hatWeakeningIndex+b}(u)</code>
	 * describes the set
	 * <code>{c^{a*n+a*m+a*hatWeakeningIndex+b}(u) | n,m \in \nat}</code>
	 * = <code>{c^{a*(n+m+hatWeakeningIndex)+b}(u) | n,m \in \nat}</code>
	 * = <code>{c^{a*n+b}(u) | n >= hatWeakeningIndex}</code>
	 * which is included in
	 * <code>{c^{a*n+b}(u) | n \in \nat}</code>.
	 * </li>
	 * </ol>
	 * <p>
	 * This pattern term (hence its pattern
	 * substitution) are not modified by this
	 * method.
	 *
	 * @param hatWeakeningIndex a weakening coefficient
	 * to use
	 * @return the two weakening substitutions built from
	 * this pattern term
	 * @throws ArithmeticException if a weakened exponent cannot be represented
	 * as an <code>int</code>
	 */
	public WeakeningSubstitutions buildWeakeningSubstitutions(
			int hatWeakeningIndex) {

		Substitution firstWeakeningSubstitution = new Substitution();
		Substitution secondWeakeningSubstitution = new Substitution();

		for (Map.Entry<Variable, Term> entry :
				this.getPatternSubstitution().getHatFunctionSubstitution()) {
			addWeakeningImages(
					hatWeakeningIndex,
					entry,
					firstWeakeningSubstitution,
					secondWeakeningSubstitution);
		}

		return new WeakeningSubstitutions(
				firstWeakeningSubstitution,
				secondWeakeningSubstitution);
	}

	/**
	 * The two substitutions obtained by weakening a simple pattern term.
	 *
	 * @param first the substitution containing
	 * mappings of the form
	 * <code>x -> c^{a,a*hatWeakeningIndex+b}(u)</code>
	 * @param second the substitution containing
	 * mappings of the form
	 * <code>x -> c^{a,a,a*hatWeakeningIndex+b}(u)</code>
	 */
	public record WeakeningSubstitutions(
			Substitution first,
			Substitution second) {}

	/**
	 * Adds the images derived from one mapping to the two
	 * weakening substitutions.
	 *
	 * @param hatWeakeningIndex a weakening coefficient to use
	 * @param mapping the mapping whose image is copied or weakened
	 * @param firstWeakeningSubstitution the substitution to fill
	 * with the first image
	 * @param secondWeakeningSubstitution the substitution to fill
	 * with the second image
	 */
	private static void addWeakeningImages(
			int hatWeakeningIndex,
			Map.Entry<Variable, Term> mapping,
			Substitution firstWeakeningSubstitution,
			Substitution secondWeakeningSubstitution) {

		Variable variable = mapping.getKey();
		Term image = mapping.getValue();

		if (image instanceof HatFunction hatFunction) {
			addWeakenedHatFunctionImages(
					hatWeakeningIndex,
					variable,
					hatFunction,
					firstWeakeningSubstitution,
					secondWeakeningSubstitution);
			return;
		}

		firstWeakeningSubstitution.add(variable, image);
		secondWeakeningSubstitution.add(variable, image);
	}

	/**
	 * Adds to the specified substitutions the two weakened
	 * variants of the specified hat-function image.
	 *
	 * @param hatWeakeningIndex a weakening coefficient to use
	 * @param variable the variable whose image is weakened
	 * @param hatFunction the image of <code>variable</code> to weaken
	 * @param firstWeakeningSubstitution the substitution to fill
	 * with the first weakened image
	 * @param secondWeakeningSubstitution the substitution to fill
	 * with the second weakened image
	 */
	private static void addWeakenedHatFunctionImages(
			int hatWeakeningIndex,
			Variable variable,
			HatFunction hatFunction,
			Substitution firstWeakeningSubstitution,
			Substitution secondWeakeningSubstitution) {

		HatFunctionSymbol hatSymbol = hatFunction.getRootSymbol();
		Term argument = hatFunction.getArgument();
		int step = hatFunction.getA();
		int offset = hatFunction.getB();
		int weakenedOffset = Math.addExact(
				Math.multiplyExact(step, hatWeakeningIndex), offset);

		List<Integer> firstWeakenedExponents =
				List.of(step, weakenedOffset);
		Term firstWeakenedImage =
				new HatFunction(hatSymbol, argument, firstWeakenedExponents);
		firstWeakeningSubstitution.add(variable, firstWeakenedImage);

		List<Integer> secondWeakenedExponents =
				List.of(step, step, weakenedOffset);
		Term secondWeakenedImage =
				new HatFunction(hatSymbol, argument, secondWeakenedExponents);
		secondWeakeningSubstitution.add(variable, secondWeakenedImage);
	}

	/**
	 * Returns a string representation of this
	 * simple pattern term relatively to the
	 * given set of variable symbols.
	 *
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	@Override
	public String toString(Map<Variable,String> variables) {
		return this.upsilon.toString(variables, false);
	}
}
