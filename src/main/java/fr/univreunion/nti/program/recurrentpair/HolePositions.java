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

package fr.univreunion.nti.program.recurrentpair;

import java.util.LinkedList;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Hole;
import fr.univreunion.nti.term.Term;

/**
 * Selected positions of square and square' in <code>c1</code>,
 * together with the variables at the square position.
 *
 * @param squareIndex the position of square in <code>c1</code>
 * @param squarePrimeIndex the position of square' in <code>c1</code>
 * @param x1 the variable at the square position in <code>u1</code>
 * @param x2 the variable at the square position in <code>u2</code>
 */
record HolePositions(
		int squareIndex,
		int squarePrimeIndex,
		Term x1,
		Term x2) {

	/**
	 * Builds a function by replacing the selected positions with
	 * the provided arguments and copying the other arguments from
	 * the fallback source.
	 *
	 * @param root the root symbol and its arity
	 * @param squareArgument the argument at the square position
	 * @param squarePrimeArgument the argument at the square' position
	 * @param fallbackSource the source for the remaining arguments
	 * @return the built function
	 */
	Function buildFunction(
			RootSymbol root,
			Term squareArgument,
			Term squarePrimeArgument,
			Function fallbackSource) {

		LinkedList<Term> arguments = new LinkedList<>();
		for (int k = 0; k < root.arity(); k++)
			if (k == this.squareIndex)
				arguments.add(squareArgument);
			else if (k == this.squarePrimeIndex)
				arguments.add(squarePrimeArgument);
			else
				arguments.add(fallbackSource.getChild(k));

		return new Function(root.symbol(), arguments);
	}

	/**
	 * Builds the context c1 from the provided root and fallback source.
	 *
	 * @param root the leading function symbol of c1 and its arity
	 * @param fallbackSource the source for the remaining arguments
	 * @return the context c1
	 */
	Term buildContext(RootSymbol root, Function fallbackSource) {

		// 0x25A1 is the UTF-16 encoding of
		// the white square character.
		Hole square = new Hole("" + '□');
		Hole squarePrime = new Hole('□' + "'");

		return this.buildFunction(
				root,
				square,
				squarePrime,
				fallbackSource);
	}

	/**
	 * Checks whether the given term occurs only at the selected positions
	 * of the given function.
	 *
	 * @param term a term whose presence is to be tested
	 * @param function a function where the check occurs
	 * @param root the root function symbol of <code>function</code>
	 * and its arity
	 * @return <code>true</code> iff <code>term</code>
	 * occurs only at the selected positions of <code>function</code>
	 */
	boolean occursOnlyAt(Term term, Function function, RootSymbol root) {

		for (int k = 0; k < root.arity(); k++)
			if (k != this.squareIndex &&
					k != this.squarePrimeIndex &&
					function.getChild(k).contains(term))
				return false;

		return true;
	}
}
