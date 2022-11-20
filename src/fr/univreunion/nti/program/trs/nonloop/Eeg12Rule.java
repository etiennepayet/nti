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

/**
 * An inference rule or a lemma presented in
 * [Emmes, Enger, Giesl, IJCAR'12].
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public enum Eeg12Rule {
	I("(I)", "Pattern rule from TRS"),
	II("(II)", "Pattern creation 1"),
	III("(III)", "Pattern creation 2"),
	IV("(IV)", "Equivalence"),
	V("(V)", "Instantiation"),
	VI("(VI)", "Narrowing"),
	VII("(VII)", "Instantiating sigma"),
	VIII("(VIII)", "Instantiating mu"),
	IX("(IX)", "Rewriting"),
	Lemma4("Lemma 4", "Equivalence by domain renaming"),
	Lemma6("Lemma 6", "Equivalence by Irrelevant Pattern Substitutions"),
	Lemma9("Lemma 9", "Equivalence by simplifying mu");
	
	private final String shortName;
	
	private final String longName;
	
	/**
	 * Constructs a rule or lemma of [Emmes, Enger, Giesl, IJCAR'12].
	 *
	 * @param shortName the short name of this rule or lemma
	 * @param longName the long name of this rule or lemma
	 */
	private Eeg12Rule(String shortName, String longName) {
		this.shortName = shortName;
		this.longName = longName;
	}
	
	/**
	 * Returns the short name of this rule or lemma.
	 * 
	 * @return the short name of this rule or lemma
	 */
	public String getShortName() {
		return this.shortName;
	}
	
	/**
	 * Returns the long name of this rule or lemma.
	 * 
	 * @return the long name of this rule or lemma
	 */
	public String getLongName() {
		return this.longName;
	}
}
