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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.parse;

/**
 * Base class for errors caused by invalid program text.
 *
 * <p>These exceptions are unchecked because parsing methods historically
 * report malformed input without checked-exception declarations. Actual input
 * and output failures remain represented separately.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public abstract class ProgramParseException extends RuntimeException {

	private final int lineNumber;

	/**
	 * Constructs a parsing exception.
	 *
	 * @param message the error message
	 * @param lineNumber the line at which the error was detected
	 */
	protected ProgramParseException(String message, int lineNumber) {
		super(message);
		this.lineNumber = lineNumber;
	}

	/**
	 * Returns the line at which the error was detected.
	 *
	 * @return the one-based line number
	 */
	public int getLineNumber() {
		return this.lineNumber;
	}
}
