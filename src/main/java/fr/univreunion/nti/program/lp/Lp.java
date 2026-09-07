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

package fr.univreunion.nti.program.lp;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Map;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.term.Variable;

/**
 * A logic program (LP).
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Lp extends Program implements Iterable<RuleLp> {

	/**
	 * The rules of the program.
	 */
	protected final LinkedList<RuleLp> rules = new LinkedList<>();

	/**
	 * The mode whose nontermination has to be proved.
	 */
	protected final Mode mode;

	/**
	 * Builds a logic program (LP).
	 *
	 * @param name the name of this LP
	 * @param rules the rules of this LP
	 * @param mode the mode whose nontermination has to be proved
	 * @throws IllegalArgumentException if a given rule or {@code mode} is
	 * {@code null}
	 */
	public Lp(String name, Collection<RuleLp> rules, Mode mode) {

		super(name);

		for (RuleLp r : rules)
			if (r != null)
				this.rules.add(r);
			else
				throw new IllegalArgumentException("construction of a LP with a null rule");

		if (mode == null)
			throw new IllegalArgumentException("construction of a LP with a null mode");
		this.mode = mode;
	}

	/**
	 * Returns the size of this program.
	 *
	 * @return the size of this program
	 */
	@Override
	public int size() {
		return this.rules.size();
	}

	/**
	 * Returns an iterator over the rules of this program.
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<RuleLp> iterator() {
		return this.rules.iterator();
	}

	/**
	 * Runs a termination proof for this program.
	 *
	 * @param context the context of the analysis
	 * @return the computed proof
	 */
	@Override
	public Proof proveTermination(AnalysisContext context) {
		return new LpTerminationProver(this).prove(context);
	}

	/**
	 * Returns a string representation of this
	 * program relatively to the given set of
	 * variable symbols.
	 *
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	public String toString(Map<Variable,String> variables) {
		// Introductory message.
		StringBuilder s = new StringBuilder("** BEGIN program: ");
		s.append(this.getName());

		// The mode whose nontermination has to be proved.
		s.append("\n* mode:\n");
		s.append(this.mode);
		s.append('\n');

		// The rules of the program.
		int nbRules = this.rules.size();
		s.append("* ");
		s.append(nbRules);
		s.append(" rule(s)");
		if (0 < nbRules) s.append(":");
		s.append('\n');
		for (RuleLp r : this.rules) {
			s.append(r.toString(variables));
			s.append("\n");
		}

		// Ending message.
		s.append("** END program: ");
		s.append(this.getName());

		return s.toString();
	}

	/**
	 * Returns a String representation of this program.
	 *
	 * @return a String representation of this program
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}

	/**
	 * Returns a String representation of some statistics
	 * about this program.
	 *
	 * @return a String representation of some statistics
	 * about this program
	 */
	@Override
	public String toStringStat() {
		return new LpStatisticsFormatter().format(this);
	}
}
