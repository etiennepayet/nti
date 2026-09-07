/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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

package fr.univreunion.nti.program.trs.dependencypair;

import java.io.Serial;

/** Indicates that dependency-graph construction exceeded its resource bound. */
public class DependencyGraphLimitException extends RuntimeException {

	@Serial
	private static final long serialVersionUID = 1L;

	/**
	 * Builds an exception for the specified approximate-arc limit.
	 *
	 * @param maximumArcCount the maximum number of approximate arcs
	 */
	public DependencyGraphLimitException(int maximumArcCount) {
		super("Dependency graph construction exceeded " + maximumArcCount +
				" approximate arcs; analysis aborted.");
	}
}
