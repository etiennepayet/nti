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

package fr.univreunion.nti.program;

/**
 * A program (LP, SRS, TRS, ...)
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class Program {

	/**
	 * The name of this program.
	 */
	private final String name;

	/**
	 * Builds a program.
	 *
	 * @param name the name of this program
	 */
	protected Program(String name) {
		this.name = name;
	}

	/**
	 * Returns the name of this program.
	 *
	 * @return the name of this program
	 */
	public String getName() {
		return this.name;
	}

	/**
	 * Runs a termination proof for this program.
	 *
	 * @param context the context of the analysis
	 * @return the computed proof
	 */
	public abstract Proof proveTermination(AnalysisContext context);

	/**
	 * Returns the size of this program.
	 *
	 * @return the size of this program
	 */
	public abstract int size();

	/**
	 * Returns a String representation of some statistics
	 * about this program.
	 *
	 * @return a String representation of some statistics
	 * about this program
	 */
	public abstract String toStringStat();
}
