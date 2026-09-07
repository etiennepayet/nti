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

package fr.univreunion.nti.program.trs.ruleunfolding.unit;

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

public class ParentTrsUnit extends ParentTrs {

	/**
	 * Builds a parent for an unfolded rule.
	 *
	 * @param father the rule that is unfolded
	 * @param mother the rule which is used to unfold
	 * @param position the position where the unfolding takes place
	 * @param unfoldsLeftSide whether the unfolding takes place on
	 * the left-hand side
	 */
    public static synchronized ParentTrsUnit of(
			UnfoldedRuleTrsUnit father, RuleTrs mother,
			Position position, boolean unfoldsLeftSide) {

		return new ParentTrsUnit(father, mother, position, unfoldsLeftSide);
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
	private ParentTrsUnit(UnfoldedRuleTrsUnit father, RuleTrs mother,
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
		String l = "L" + it;
		String p = "p" + it;

		ParentTrs parent = unfoldedRule.getParent();
		if (parent != null) {
			s.append(parent.toString(indentation));
			s.append("\n");
			s.append(spaces);
			s.append("==> ");
		}
		else
			s.append(spaces);
		s.append(l).append(" = ").append(unfoldedRule);
		s.append(" is in U_IR^").append(it).append(".");

		if (this.getMother() == null) {
			s.append("\n");
			s.append(spaces);
			s.append("Let ").append(p).append(" = ").append(this.getPosition()).append(".");
			s.append("\n");
			s.append(spaces);
			s.append("The subterm at position ");
			s.append(p);
			s.append(" in the left-hand side of the rule of ");
			s.append(l);
			s.append(" unifies with");
			s.append("\n");
			s.append(spaces);
			s.append("the subterm at position ");
			s.append(p);
			s.append(" in the right-hand side of the rule of ");
			s.append(l);
			s.append(".");
		}
		else {
			s.append("\n");
			s.append(spaces);
			s.append("Let ").append(p).append(" = ").append(this.getPosition()).append(".");
			s.append("\n");
			s.append(spaces);
			s.append("We unfold the rule of ").append(l);
			s.append(this.unfoldsLeftSide() ? " backwards" : " forwards");
			s.append(" at position ");
			s.append(p);
			s.append("\n");
			s.append(spaces);
			s.append("with the rule ");
			s.append(this.getMother());
			s.append(".");
		}

		return s.toString();
	}
}
