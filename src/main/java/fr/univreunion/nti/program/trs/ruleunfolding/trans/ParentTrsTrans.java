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

package fr.univreunion.nti.program.trs.ruleunfolding.trans;

import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.term.Position;

/**
 * The parent of an unfolded rule. It embeds several objects
 * from which an unfolded rule was generated.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParentTrsTrans extends ParentTrs {

	/**
	 * Builds a parent for an unfolded rule.
	 *
	 * @param father the rule that is unfolded
	 * @param mother the rule which is used to unfold
	 * @param position the position where the unfolding takes place
	 * @param unfoldsLeftSide whether the unfolding takes place on
	 * the left-hand side
	 */
    public static synchronized ParentTrsTrans of(
			UnfoldedRuleTrsTrans father, RuleTrs mother,
			Position position, boolean unfoldsLeftSide) {

		return new ParentTrsTrans(father, mother, position, unfoldsLeftSide);
	}

	/**
	 * Builds a parent for an unfolded rule.
	 *
	 * @param father the rule that is unfolded
	 * @param mother the rule which is used to unfold
	 * @param position the position where the unfolding takes place
	 * @param unfoldsLeftSide whether the unfolding takes place on
	 * the left-hand side
	 */
	private ParentTrsTrans(UnfoldedRuleTrsTrans father, RuleTrs mother,
			Position position, boolean unfoldsLeftSide) {

		super(father, mother, position, unfoldsLeftSide);
	}

	/**
	 * Returns a String representation of this parent.
	 *
	 * @param indentation the number of single spaces
	 * to print before each line of the returned string
	 * representation
	 * @return a String representation of this parent
	 */
	@Override
	public String toString(int indentation) {
		// The string to return at the end.
		StringBuilder s = new StringBuilder();

		// The spaces for indentation.
		StringBuilder spaces = new StringBuilder(indentation);
        spaces.repeat(" ", Math.max(0, indentation));

		UnfoldedRuleTrs unfoldedRule = this.getFather();
		int it = unfoldedRule.getIteration();
		String t = "L" + it;

		ParentTrs parent = unfoldedRule.getParent();
		if (parent != null) {
			s.append(parent.toString(indentation));
			s.append("\n");
			s.append(spaces);
			s.append("==> ");
		}
		else
			s.append(spaces);
		s.append(t).append(" = ").append(unfoldedRule);
		s.append(" is in U_IR^").append(it).append(".");

		if (this.getMother() == null) {
			// Here, we build a unit triple from a transitory triple.
			s.append("\n");
			s.append(spaces);
			s.append("We build a unit triple from ").append(t).append(".");
		}
		else {
			// Here, we build a composed triple from a transitory triple.
			s.append("\n");
			s.append(spaces);
			s.append("D = ").append(this.getMother());
			s.append(" is a dependency pair of IR.");
			s.append("\n");
			s.append(spaces);
			s.append("We build a composed triple from ").append(t).append(" and D.");
		}

		return s.toString();
	}
}
