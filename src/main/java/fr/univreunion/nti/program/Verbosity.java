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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program;

/**
 * The amount of diagnostic detail retained and rendered by an analysis.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public enum Verbosity {
	/** Only the final result and argument are rendered. */
	QUIET,

	/** The decisive proof and concise concurrent-attempt summaries are rendered. */
	VERBOSE,

	/** Retained work from every concurrent attempt is rendered as well. */
	VERY_VERBOSE;

	/**
	 * Returns whether ordinary verbose proof details are enabled.
	 *
	 * @return {@code true} for {@link #VERBOSE} and {@link #VERY_VERBOSE}
	 */
	public boolean includesProofDetails() {
		return this != QUIET;
	}

	/**
	 * Returns whether retained concurrent-attempt traces are enabled.
	 *
	 * @return {@code true} only for {@link #VERY_VERBOSE}
	 */
	public boolean includesAllAttemptTraces() {
		return this == VERY_VERBOSE;
	}
}
