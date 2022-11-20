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

package fr.univreunion.nti.program;

/**
 * A program rule.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public abstract class Rule {
	
	/**
	 * The appearance number of the rule in
	 * the analyzed file.
	 */
	private final Integer numberInFile;
	
	/**
	 * Builds a rule.
	 * 
	 * @param numberInFile the appearance number
	 * of the rule in the analyzed file
	 */
	public Rule(Integer numberInFile) {
		this.numberInFile = numberInFile;
	}
	
	/**
	 * Return the appearance number of the rule in
	 * the analyzed file.
	 * 
	 * @return the appearance number of the rule in
	 * the analyzed file
	 */
	public Integer getNumberInFile() {
		return this.numberInFile;
	}
}
