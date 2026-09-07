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

package fr.univreunion.nti.parse.trs;

import java.io.BufferedReader;
import java.util.Map;

import fr.univreunion.nti.parse.OldFormatScanner;
import fr.univreunion.nti.parse.Token;


/**
 * A lexical analyzer for reading files storing
 * Term or String Rewrite Systems in the old, 
 * human-readable, format.
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class ScannerTrs extends OldFormatScanner {

	/**
	 * The keywords of the language used to write SRSs.
	 */
	private static final Map<String, Token> KEYWORDS = Map.of(
			"VAR", Token.VAR,
			"RULES", Token.RULES,
			"STRATEGY", Token.STRATEGY,
			"INNERMOST", Token.INNERMOST,
			"OUTERMOST", Token.OUTERMOST,
			"->", Token.ARROW);

	/**
	 * Builds a new lexical analyzer for TRS/SRS
	 * in the old, human-readable, format.
	 * 
	 * @param input the input to read
	 */
	public ScannerTrs(BufferedReader input) {
		super(input, KEYWORDS);
	}
}
