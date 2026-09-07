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

package fr.univreunion.nti.program.trs.ruleunfolding.unit;

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

class ParentTrsUnitTest {

	@Test
	@DisplayName("render forward and backward unfolding")
	void renderForwardAndBackwardUnfolding() throws IOException {
		UnfoldedRuleTrsUnit father = unitRule("f(X) -> g(X)", 2, null);
		RuleTrs mother = parseRule("g(Y) -> h(Y)");

		assertEquals(" L2 = f(_0) -> g(_0) [unit] is in U_IR^2.\n" +
				" Let p2 = [0].\n" +
				" We unfold the rule of L2 forwards at position p2\n" +
				" with the rule g(_0) -> h(_0).",
				ParentTrsUnit.of(father, mother, new Position(0), false).toString(1));
		assertEquals(" L2 = f(_0) -> g(_0) [unit] is in U_IR^2.\n" +
				" Let p2 = [0].\n" +
				" We unfold the rule of L2 backwards at position p2\n" +
				" with the rule g(_0) -> h(_0).",
				ParentTrsUnit.of(father, mother, new Position(0), true).toString(1));
	}

	@Test
	@DisplayName("render unification of corresponding subterms")
	void renderUnificationOfCorrespondingSubterms() throws IOException {
		UnfoldedRuleTrsUnit father = unitRule("f(X) -> g(X)", 2, null);

		assertEquals("L2 = f(_0) -> g(_0) [unit] is in U_IR^2.\n" +
				"Let p2 = [0].\n" +
				"The subterm at position p2 in the left-hand side of the rule of L2 unifies with\n" +
				"the subterm at position p2 in the right-hand side of the rule of L2.",
				ParentTrsUnit.of(father, null, new Position(0), false).toString(0));
	}

	@Test
	@DisplayName("render the complete parent chain in order")
	void renderCompleteParentChainInOrder() throws IOException {
		UnfoldedRuleTrsUnit first = unitRule("f(X) -> g(X)", 1, null);
		RuleTrs firstMother = parseRule("g(Y) -> h(Y)");
		ParentTrsUnit firstParent = ParentTrsUnit.of(
				first, firstMother, new Position(0), false);
		UnfoldedRuleTrsUnit second = unitRule("f(X) -> h(X)", 2, firstParent);
		RuleTrs secondMother = parseRule("k(Y) -> h(Y)");

		String rendered = ParentTrsUnit.of(
				second, secondMother, new Position(0), true).toString(1);

		assertEquals(" L1 = f(_0) -> g(_0) [unit] is in U_IR^1.\n" +
				" Let p1 = [0].\n" +
				" We unfold the rule of L1 forwards at position p1\n" +
				" with the rule g(_0) -> h(_0).\n" +
				" ==> L2 = f(_0) -> h(_0) [unit] is in U_IR^2.\n" +
				" Let p2 = [0].\n" +
				" We unfold the rule of L2 backwards at position p2\n" +
				" with the rule k(_0) -> h(_0).", rendered);
	}

	private static UnfoldedRuleTrsUnit unitRule(
			String ruleText, int iteration, ParentTrsUnit parent) throws IOException {

		RuleTrs rule = parseRule(ruleText);
		return new UnfoldedRuleTrsUnit(
				rule.getLeft(), rule.getRight(), iteration, parent, List.of());
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		return parser.parseTrsRule(ruleText, variables);
	}
}
