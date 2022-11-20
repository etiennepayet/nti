/*
 * Copyright 2022 Etienne Payet <etienne.payet at univ-reunion.fr>
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

package fr.univreunion.nti.program.trs.loop.trans;

import fr.univreunion.nti.Options;
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

public class ParentTrsLoopTrans extends ParentTrs {

	/**
	 * Static factory method. Builds a parent for an unfolded rule.
	 * 
	 * @param father the rule that is unfolded
	 * @param mother the rule which is used to unfold
	 * @param position the position where the unfolding takes place
	 * @param leftOrRight the side (left-hand or right-hand) where
	 * the unfolding takes place (<code>true</code> for left,
	 * <code>false</code> for right)
	 */
	public synchronized static ParentTrsLoopTrans getInstance(
			UnfoldedRuleTrsLoopTrans father, RuleTrs mother,
			Position position, boolean leftOrRight) {

		if (Options.getInstance().isInVerboseMode())
			return new ParentTrsLoopTrans(father, mother, position, leftOrRight);

		return null;
	}

	/**
	 * Builds a parent for an unfolded rule.
	 * 
	 * @param father the rule that is unfolded
	 * @param mother the rule which is used to unfold
	 * @param position the position where the unfolding takes place
	 * @param leftOrRight the side (left-hand or right-hand) where
	 * the unfolding takes place (<code>true</code> for left,
	 * <code>false</code> for right)
	 */
	private ParentTrsLoopTrans(UnfoldedRuleTrsLoopTrans father, RuleTrs mother,
			Position position, boolean leftOrRight) {

		super(father, mother, position, leftOrRight);
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
		StringBuffer s = new StringBuffer();

		// The spaces for indentation.
		StringBuffer spaces = new StringBuffer(indentation);
		for (int i = 0; i < indentation; i++) spaces.append(" ");

		UnfoldedRuleTrs U = this.getFather();
		int it = U.getIteration();
		String t = "L" + it;

		ParentTrs parent = U.getParent();
		if (parent != null) {
			s.append(parent.toString(indentation));
			s.append("\n");
			s.append(spaces);
			s.append("==> ");
		}
		else
			s.append(spaces);
		s.append(t + " = " + U);
		s.append(" is in U_IR^" + it + ".");

		if (this.getMother() == null) {
			// Here, we build a unit triple from a transitory triple.
			s.append("\n");
			s.append(spaces);
			s.append("We build a unit triple from " + t + ".");
		}
		else {
			// Here, we build a composed triple from a transitory triple.
			s.append("\n");
			s.append(spaces);
			s.append("D = " + this.getMother());
			s.append(" is a dependency pair of IR.");
			s.append("\n");
			s.append(spaces);
			s.append("We build a composed triple from " + t + " and D.");
		}

		return s.toString();
	}
}
