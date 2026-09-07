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

package fr.univreunion.nti.program.trs.ruleunfolding.comp;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Variable;

class ParentTrsCompTest {

	@Test
	@DisplayName("render unification between the two composed rules")
	void renderUnificationBetweenTheTwoRules() throws IOException {
		UnfoldedRuleTrsComp father = composedRule(2);

		assertEquals("L2 = [f(_0) -> g(_0), h(_1) -> k(_1)] [comp] is in U_IR^2.\n" +
				"Let p2 = [0].\n" +
				"The subterm at position p2 in the right-hand side of the first rule of L2 unifies with\n" +
				"the subterm at position p2 in the left-hand side of the second rule of L2.",
				ParentTrsComp.of(father, null, new Position(0), false).toString(0));
	}

	@Test
	@DisplayName("render merging of the two composed rules")
	void renderMergingOfTheTwoRules() throws IOException {
		UnfoldedRuleTrsComp father = composedRule(2);
		RuleTrs mother = parseRule("g(Y) -> h(Y)");

		assertEquals(" L2 = [f(_0) -> g(_0), h(_1) -> k(_1)] [comp] is in U_IR^2.\n" +
				" We merge the first and the second rule of L2.",
				ParentTrsComp.of(father, mother, new Position(), false).toString(1));
	}

	@Test
	@DisplayName("render forward unfolding of the first rule")
	void renderForwardUnfoldingOfTheFirstRule() throws IOException {
		UnfoldedRuleTrsComp father = composedRule(2);
		RuleTrs mother = parseRule("g(Y) -> h(Y)");

		assertEquals(" L2 = [f(_0) -> g(_0), h(_1) -> k(_1)] [comp] is in U_IR^2.\n" +
				" Let p2 = [0].\n" +
				" We unfold the first rule of L2 forwards at position p2\n" +
				" with the rule g(_0) -> h(_0).",
				ParentTrsComp.of(father, mother, new Position(0), false).toString(1));
	}

	@Test
	@DisplayName("render backward unfolding of the second rule")
	void renderBackwardUnfoldingOfTheSecondRule() throws IOException {
		UnfoldedRuleTrsComp father = composedRule(2);
		RuleTrs mother = parseRule("g(Y) -> h(Y)");

		assertEquals(" L2 = [f(_0) -> g(_0), h(_1) -> k(_1)] [comp] is in U_IR^2.\n" +
				" Let p2 = [0].\n" +
				" We unfold the second rule of L2 backwards at position p2\n" +
				" with the rule g(_0) -> h(_0).",
				ParentTrsComp.of(father, mother, new Position(0), true).toString(1));
	}

	private static UnfoldedRuleTrsComp composedRule(int iteration)
			throws IOException {

		RuleTrs first = parseRule("f(X) -> g(X)");
		RuleTrs second = parseRule("h(Y) -> k(Y)");
		return (UnfoldedRuleTrsComp) UnfoldedRuleTrsComp.getInstances(
				first.getLeft(), first.getRight(), iteration, null,
				second, List.of(), List.of()).iterator().next();
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		return parser.parseTrsRule(ruleText, variables);
	}
}
