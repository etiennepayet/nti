/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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

package fr.univreunion.nti.program.trs.argument;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Variable;

/**
 * A nontermination argument provided by a root cycle modulo renaming.
 *
 * @author <A HREF="mailto:etiennepayet@univ-reunion.fr">Etienne Payet</A>
 */

public class ArgumentRootVariantCycle implements Argument {

	/** The first rule of the cycle. */
	private final RuleTrs first;

	/** The second rule of the cycle, possibly equal to the first one. */
	private final RuleTrs second;

	/**
	 * Builds an argument from two rules whose successive right-hand sides are
	 * variants of the following left-hand sides.
	 *
	 * @param first the first rule of the cycle
	 * @param second the second rule of the cycle
	 */
	public ArgumentRootVariantCycle(RuleTrs first, RuleTrs second) {
		this.first = first;
		this.second = second;
	}

	@Override
	public String getDetails(int indentation) {
		return "";
	}

	@Override
	public String getWitnessKind() {
		return "root variant cycle";
	}

	@Override
	public String toString() {
		Map<Variable, String> certificateVariables = new HashMap<>();
		String certificate = this.first.getLeft().toString(
				certificateVariables, false);
		return "* Technique: root variant-cycle search\n" +
				"* Certificate: " + certificate + " is non-terminating\n" +
				"* Description:\n" +
				"The analyzed TRS contains the following root rewrite steps:\n" +
				render(this.first) + "\n" + render(this.second) + "\n" +
				"The first right-hand side is a variant of the second left-hand side,\n" +
				"and the second right-hand side is a variant of the first left-hand side.\n" +
				"Neither rule contains an extra variable on its right-hand side.\n" +
				"Repeating these steps with fresh variable renamings yields an infinite\n" +
				"rewrite sequence starting from " + certificate + ".";
	}

	/** Renders one rule with its own variable dictionary. */
	private static String render(RuleTrs rule) {
		Map<Variable, String> variables = new HashMap<>();
		return rule.toString(variables, false);
	}
}
