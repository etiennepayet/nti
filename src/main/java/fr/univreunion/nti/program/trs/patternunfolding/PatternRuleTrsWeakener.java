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

package fr.univreunion.nti.program.trs.patternunfolding;

import java.util.Collection;
import java.util.LinkedList;

import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * Builds weakened versions of a TRS pattern rule.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class PatternRuleTrsWeakener {

	/**
	 * Attempts to weaken a rule based on the provided pattern terms.
	 *
	 * @param rule the pattern rule to weaken
	 * @param subterm a subterm of the rule
	 * @param patternTerm the pattern term used for weakening
	 * @return the original rule followed by its weakened versions
	 */
	static Collection<PatternRuleTrs> weaken(
			PatternRuleTrs rule,
			SimplePatternTerm subterm,
			SimplePatternTerm patternTerm) {

		Collection<PatternRuleTrs> result = new LinkedList<>();
		result.add(rule);

		SimplePatternTerm left = rule.getLeft();
		SimplePatternTerm right = rule.getRight();
		if (!canWeaken(left, right, subterm, patternTerm)) return result;

		SimplePatternTerm.WeakeningIndexes weakeningIndexes =
				subterm.computeWeakeningIndexes(patternTerm);
		if (weakeningIndexes == null) return result;

		int functionIndex = weakeningIndexes.functionWeakeningIndex();
		int hatIndex = weakeningIndexes.hatWeakeningIndex();
		if (0 <= functionIndex && hatIndex < 0)
			addFunctionWeakening(rule, left, right, functionIndex, result);
		else if (functionIndex < 0 && 0 <= hatIndex)
			addHatWeakenings(rule, left, right, hatIndex, result);

		return result;
	}

	/** Returns whether weakening can be attempted with the provided terms. */
	private static boolean canWeaken(
			SimplePatternTerm left,
			SimplePatternTerm right,
			SimplePatternTerm subterm,
			SimplePatternTerm patternTerm) {

		return subterm != null && patternTerm != null
				&& patternTerm.getArity() == 1
				&& left.getArity() == 1
				&& right.getArity() == 1;
	}

	/** Adds the rule obtained by finite instantiation weakening. */
	private static void addFunctionWeakening(
			PatternRuleTrs rule,
			SimplePatternTerm left,
			SimplePatternTerm right,
			int functionIndex,
			Collection<PatternRuleTrs> result) {

		SimplePatternTerm weakenedLeft =
				SimplePatternTerm.of(left.instantiateAt(functionIndex));
		SimplePatternTerm weakenedRight =
				SimplePatternTerm.of(right.instantiateAt(functionIndex));
		PatternRuleTrs weakenedRule = PatternRuleTrs.tryBuild(
				weakenedLeft, weakenedRight, rule.getIteration());
		if (weakenedRule != null) result.add(weakenedRule);
	}

	/** Adds both rules obtained by hat-function weakening. */
	private static void addHatWeakenings(
			PatternRuleTrs rule,
			SimplePatternTerm left,
			SimplePatternTerm right,
			int hatIndex,
			Collection<PatternRuleTrs> result) {

		// Each x -> c^{a,b}(u) is first replaced by
		// x -> c^{a,a*hatIndex+b}(u), which describes
		// {c^{a*n+b}(u) | n >= hatIndex}.
		// It is then replaced by x -> c^{a,a,a*hatIndex+b}(u),
		// which describes the same set with two pumping parameters.
		SimplePatternTerm.WeakeningSubstitutions leftSubstitutions =
				left.buildWeakeningSubstitutions(hatIndex);
		SimplePatternTerm.WeakeningSubstitutions rightSubstitutions =
				right.buildWeakeningSubstitutions(hatIndex);

		addWeakenedRule(
				rule,
				leftSubstitutions.first(),
				rightSubstitutions.first(),
				result);
		addWeakenedRule(
				rule,
				leftSubstitutions.second(),
				rightSubstitutions.second(),
				result);
	}

	/** Builds one weakened rule from the provided substitutions and adds it. */
	private static void addWeakenedRule(
			PatternRuleTrs rule,
			Substitution leftSubstitution,
			Substitution rightSubstitution,
			Collection<PatternRuleTrs> result) {

		SimplePatternSubstitution leftPatternSubstitution =
				SimplePatternSubstitution.tryBuildTakingOwnership(leftSubstitution);
		if (leftPatternSubstitution == null) return;
		SimplePatternSubstitution rightPatternSubstitution =
				SimplePatternSubstitution.tryBuildTakingOwnership(rightSubstitution);
		if (rightPatternSubstitution == null) return;

		SimplePatternTerm weakenedLeft = SimplePatternTerm.tryBuild(
				rule.getLeft().getBaseTerm(), leftPatternSubstitution);
		SimplePatternTerm weakenedRight = SimplePatternTerm.tryBuild(
				rule.getRight().getBaseTerm(), rightPatternSubstitution);
		PatternRuleTrs weakenedRule = PatternRuleTrs.tryBuild(
				weakenedLeft, weakenedRight, rule.getIteration());
		if (weakenedRule != null) result.add(weakenedRule);
	}

	/** Prevents instantiation of this utility class. */
	private PatternRuleTrsWeakener() {
	}
}
