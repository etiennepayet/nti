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

package fr.univreunion.nti.program.trs.nonloop;

import fr.univreunion.nti.program.trs.ParentTrs;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Position;

/**
 * The parent of an unfolded rule. It embeds several objects
 * from which an unfolded rule was generated.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ParentTrsNonLoop extends ParentTrs {

	/**
	 * The rules (from (I) to (IX)) and lemmas
	 * (4, 6 or 9) of [Emmes, Enger, Giesl, IJCAR'12]
	 * used for generating the unfolded rule whose
	 * parent is this object.
	 */
	private final Eeg12Rule[] rules;

	/**
	 * Builds a parent for an unfolded rule.
	 * 
	 * @param father the rule that is unfolded
	 * @param mother the rule which is used to unfold
	 * @param position the position where the unfolding takes place
	 * @param leftOrRight the side (left-hand or right-hand) where
	 * the unfolding takes place (<code>true</code> for left,
	 * <code>false</code> for right)
	 * @param rules the rules and lemmas used for generating
	 * the unfolded rule whose parent is this object
	 */
	public ParentTrsNonLoop(PatternRule father, RuleTrs mother,
			Position position, boolean leftOrRight, Eeg12Rule... rules) {

		super(father, mother, position, leftOrRight);

		this.rules = rules;
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

		if (0 < this.rules.length) {

			// The spaces for indentation.
			StringBuffer spaces = new StringBuffer(indentation);
			for (int i = 0; i < indentation; i++) spaces.append(" ");

			if (this.rules[0] == Eeg12Rule.I) {
				RuleTrs M = this.getMother();

				String mother = (M.getLeft().getRootSymbol().isTupleSymbol() ?
						"dependency pair" : "rule");

				s.append(spaces);
				s.append("IR contains the " + mother + " " + M);
				s.append(".\n");
				s.append(spaces);
				s.append("We apply " + Eeg12Rule.I.getShortName());
				s.append(" of [Emmes, Enger, Giesl, IJCAR'12] to this " + mother + ".");
			}
			else {
				PatternRule F = (PatternRule) this.getFather();
				int it = F.getIteration();
				String l = "P" + it;

				s.append(F.getParent().toString(indentation));

				s.append("\n");
				s.append(spaces);
				s.append("==> ");
				s.append(l + " = " + F);
				s.append(" is in U_IR^" + it + ".");

				s.append("\n");
				s.append(spaces);
				s.append("We apply ");
				boolean notFirst = false;
				for (Eeg12Rule rule : this.rules) {
					if (notFirst) s.append(" + ");
					else notFirst = true;
					s.append(rule.getShortName());
				}
				s.append(" of [Emmes, Enger, Giesl, IJCAR'12] to this pattern rule");

				Position pos = this.getPosition();
				if (pos == null) {
					s.append("\n");
					s.append(spaces);
				}
				else {
					s.append("\n");
					s.append(spaces);
					s.append("at position " + pos + " ");
				}

				RuleTrs M = this.getMother();
				String motherType, end;
				if (M instanceof PatternRule) {
					motherType = "pattern rule";
					end = "obtained from IR.";
				}
				else {
					motherType = "rule";
					end = "of IR.";
				}
				
				s.append("using the " + motherType);
				s.append("\n");
				s.append(spaces);
				s.append(M);
				s.append("\n");
				s.append(spaces);
				s.append(end);
			}
		}

		return s.toString();
	}
}
