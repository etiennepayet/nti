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

import fr.univreunion.nti.term.FunctionSymbol;

/**
 * A root function symbol together with its arity.
 *
 * @param symbol the root function symbol
 * @param arity the arity of <code>symbol</code>
 */
record RootSymbol(FunctionSymbol symbol, int arity) {

	/**
	 * Builds root-symbol data for the provided symbol.
	 *
	 * @param symbol a function symbol
	 * @return the root-symbol data
	 */
	static RootSymbol of(FunctionSymbol symbol) {
		return new RootSymbol(symbol, symbol.getArity());
	}
}
