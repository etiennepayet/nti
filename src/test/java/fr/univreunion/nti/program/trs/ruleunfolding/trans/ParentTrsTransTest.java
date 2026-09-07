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

package fr.univreunion.nti.program.trs.ruleunfolding.trans;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.term.Variable;

class ParentTrsTransTest {

	@Test
	@DisplayName("render conversion from a transitory to a unit rule")
	void renderConversionToAUnitRule() throws IOException {
		UnfoldedRuleTrsTrans father = transitoryRule("f(X) -> g(X)", 2);
		ParentTrsTrans parent = ParentTrsTrans.of(father, null, null, false);

		assertEquals("  L2 = f(_0) -> g(_0) [trans] is in U_IR^2.\n" +
				"  We build a unit triple from L2.", parent.toString(2));
	}

	@Test
	@DisplayName("render construction of a composed rule")
	void renderConstructionOfAComposedRule() throws IOException {
		UnfoldedRuleTrsTrans father = transitoryRule("f(X) -> g(X)", 2);
		RuleTrs dependencyPair = parseRule("g(Y) -> h(Y)");
		ParentTrsTrans parent = ParentTrsTrans.of(
				father, dependencyPair, null, false);

		assertEquals(" L2 = f(_0) -> g(_0) [trans] is in U_IR^2.\n" +
				" D = g(_0) -> h(_0) is a dependency pair of IR.\n" +
				" We build a composed triple from L2 and D.", parent.toString(1));
	}

	private static UnfoldedRuleTrsTrans transitoryRule(
			String ruleText, int iteration) throws IOException {

		RuleTrs rule = parseRule(ruleText);
		UnfoldedRuleTrs unfolded = UnfoldedRuleTrsTrans.getUnfoldedInstances(
				rule.getLeft(), rule.getRight(), iteration, null,
				List.of(), List.of()).iterator().next();
		return (UnfoldedRuleTrsTrans) unfolded;
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		return parser.parseTrsRule(ruleText, variables);
	}
}
