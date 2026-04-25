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

package fr.univreunion.nti.program.trs;

import fr.univreunion.nti.term.Position;

/**
 * The parent of an unfolded rule. It embeds several objects
 * from which an unfolded rule was generated.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class ParentTrs {

	/**
	 * The rule that is unfolded.
	 */
	private final UnfoldedRuleTrs father;

	/**
	 * The rule of the TRS which is used to unfold.
	 */
	private final RuleTrs mother;

	/**
	 * The position where the unfolding takes place.
	 */
	private final Position position;

	/**
	 * The side (left-hand or right-hand) where the unfolding
	 * takes place (<code>true</code> for left, <code>false</code>
	 * for right).
	 */
	private final boolean leftOrRight;
	
	/**
	 * Builds an unfolded rule parent.
	 * 
	 * @param father the rule that is unfolded
	 * @param mother the rule which is used to unfold
	 * @param position the position where the unfolding takes place
	 * @param leftOrRight the side (left-hand or right-hand) where
	 * the unfolding takes place (<code>true</code> for left,
	 * <code>false</code> for right)
	 */
	protected ParentTrs(UnfoldedRuleTrs father, RuleTrs mother,
			Position position, boolean leftOrRight) {
		this.father = father;
		this.mother = mother;
		this.position = position;
		this.leftOrRight = leftOrRight;
	}

	/**
	 * Returns the father enclosed in this parent.
	 * 
	 * @return the father enclosed in this parent
	 */
	public UnfoldedRuleTrs getFather() {
		return this.father;
	}

	/**
	 * Returns the mother enclosed in this parent.
	 * 
	 * @return the mother enclosed in this parent
	 */
	public RuleTrs getMother() {
		return this.mother;
	}

	/**
	 * Returns the position enclosed in this parent.
	 * 
	 * @return the position enclosed in this parent
	 */
	public Position getPosition() {
		return this.position;
	}

	/**
	 * Returns the side (left-hand or right-hand) enclosed
	 * in this parent (<code>true</code> for left and
	 * <code>false</code> for right).
	 * 
	 * @return the side enclosed in this parent
	 */
	public boolean getLeftOrRight() {
		return this.leftOrRight;
	}
	
	/**
	 * Returns a String representation of this parent.
	 * 
	 * @param indentation the number of single spaces
	 * to print before each line of the returned string
	 * representation
	 * @return a String representation of this parent
	 */
	public abstract String toString(int indentation);
}
