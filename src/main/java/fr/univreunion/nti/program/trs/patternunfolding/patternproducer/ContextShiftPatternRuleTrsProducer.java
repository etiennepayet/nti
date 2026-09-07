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

import java.util.Collection;
import java.util.LinkedList;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.patternunfolding.PatternRuleTrs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Produces correct TRS pattern rules from the context-shift schema.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class ContextShiftPatternRuleTrsProducer {

	/**
	 * Considers the following situations:
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
	 * Collects the pattern rules obtained by looking for
	 * context-shift candidates in the left-hand side of
	 * the first rule.
	 *
	 * @param r1 the TRS rule whose left-hand side is searched
	 * for candidates
	 * @param r2 the TRS rule used to validate each candidate
	 * @return a collection consisting of the
	 * pattern rules
	 * <code>c'(c(c1^{a,0}(s), y2)) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * or
	 * <code>c'(c(c1^{a,0}(s), y2, c1^{b,0}(y2))) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * for all possible contexts <code>c'</code>
	 * (empty if nothing could be produced)
	 */
	static Collection<PatternRuleTrs> collectFrom(
			RuleTrs r1, RuleTrs r2) {

		// We only consider the following particular case:
		// - c and c1 are ground
		// - c' consists of only one occurrence of \square_1.

		// The collection to be returned at the end.
		LinkedList<PatternRuleTrs> result = new LinkedList<>();

		Function u1 = r1.getLeft();

		// We consider all possible candidates for
		// the subterm c(s,x_1) or c(s,x_1,x_1) of
		// the left-hand side of r1.
		for (Position candidatePosition : u1) {
			Term u1Candidate = u1.get(candidatePosition);
			if (!(u1Candidate instanceof Variable)) {
				// We want the context c to be non empty.
				// Hence, we forbid the case where u1Candidate
				// is a variable.
				PatternRuleTrs patternRule = ContextShiftPatternRuleTrsSearch.tryBuild(
						r1, r2, candidatePosition, u1Candidate);
				if (patternRule != null) result.add(patternRule);
			}
		}

		return result;
	}


	/** Prevents instantiation. */
	private ContextShiftPatternRuleTrsProducer() {}
}
