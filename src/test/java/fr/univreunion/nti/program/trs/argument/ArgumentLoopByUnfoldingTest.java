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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.unit.ParentTrsUnit;
import fr.univreunion.nti.program.trs.ruleunfolding.unit.UnfoldedRuleTrsUnit;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Variable;

class ArgumentLoopByUnfoldingTest {

	@Test
	@DisplayName("render a complete shallow matching certificate")
	void renderACompleteShallowMatchingCertificate() throws IOException {
		UnfoldedRuleTrsUnit rule = unitRule("f(a) -> f(a)", 3, null);
		ArgumentLoopByUnfolding argument =
				UnfoldedRuleTrs.shallowMatchAndUnifyTest(rule);
		assertNotNull(argument);

		assertEquals("loop", argument.getWitnessKind());
		assertEquals("* Technique: [Payet, LOPSTR'18]\n" +
				"* Certificate: f(a) is non-terminating\n" +
				"* Description:\n" +
				"The following rule R was generated while unfolding\n" +
				"the dependency pairs of the analyzed TRS:\n" +
				"[iteration = 3] f(a) -> f(a)\n" +
				"Let l be the left-hand side and r be the right-hand side of R.\n" +
				"Consider the position p = 𝜀 in r and the substitutions\n" +
				"𝛳1 = {} and 𝛳2 = {}.\n" +
				"We have r|p = f(a)\n" +
				"and 𝛳2(𝛳1(l)) = 𝛳1(r|p), i.e., l semi-unifies with r|p.\n" +
				"So, the term 𝛳1(l) = f(a)\n" +
				"starts an infinite rewrite sequence w.r.t. the analyzed TRS.",
				argument.toString());
	}

	@Test
	@DisplayName("render a deep witness position")
	void renderADeepWitnessPosition() throws IOException {
		UnfoldedRuleTrsUnit rule = unitRule("f(X) -> g(f(X))", 1, null);
		ArgumentLoopByUnfolding argument =
				UnfoldedRuleTrs.deepMatchAndUnifyTest(rule);
		assertNotNull(argument);

		String certificate = argument.toString();
		assertTrue(certificate.contains("Consider the position p = [0] in r"));
		assertTrue(certificate.contains("We have r|p = f(_0)"));
		assertTrue(certificate.contains("* Certificate: f(_0) is non-terminating"));
	}

	@Test
	@DisplayName("render substitutions produced by matching")
	void renderSubstitutionsProducedByMatching() throws IOException {
		UnfoldedRuleTrsUnit rule = unitRule("f(X) -> f(a)", 0, null);
		ArgumentLoopByUnfolding argument =
				UnfoldedRuleTrs.shallowMatchAndUnifyTest(rule);
		assertNotNull(argument);

		String certificate = argument.toString();
		assertTrue(certificate.contains("𝛳1 = {} and 𝛳2 = {"));
		assertTrue(certificate.contains("𝛳1(l) = f(_0)"));
	}

	@Test
	@DisplayName("render details without a parent and normalize indentation")
	void renderDetailsWithoutAParentAndNormalizeIndentation() throws IOException {
		UnfoldedRuleTrsUnit rule = unitRule("f(a) -> f(a)", 3, null);
		ArgumentLoopByUnfolding argument =
				UnfoldedRuleTrs.shallowMatchAndUnifyTest(rule);
		assertNotNull(argument);

		assertEquals("Here is the successful unfolding. Let IR be the TRS under analysis.\n" +
				"L3 = f(a) -> f(a) [unit] is in U_IR^3.",
				argument.getDetails(-1));
		assertEquals("  Here is the successful unfolding. Let IR be the TRS under analysis.\n" +
				"  L3 = f(a) -> f(a) [unit] is in U_IR^3.",
				argument.getDetails(2));
	}

	@Test
	@DisplayName("render the complete parent chain in details")
	void renderTheCompleteParentChainInDetails() throws IOException {
		UnfoldedRuleTrsUnit father = unitRule("f(X) -> g(X)", 1, null);
		RuleTrs mother = parseRule("g(Y) -> h(Y)");
		ParentTrsUnit parent = ParentTrsUnit.of(
				father, mother, new Position(), false);
		UnfoldedRuleTrsUnit witness = unitRule("f(X) -> f(X)", 2, parent);
		ArgumentLoopByUnfolding argument =
				UnfoldedRuleTrs.shallowMatchAndUnifyTest(witness);
		assertNotNull(argument);

		assertNotSame(witness, argument.getUnfoldedRule());
		assertEquals(witness.toString(), argument.getUnfoldedRule().toString());
		assertEquals(" Here is the successful unfolding. Let IR be the TRS under analysis.\n" +
				" L1 = f(_0) -> g(_0) [unit] is in U_IR^1.\n" +
				" Let p1 = 𝜀.\n" +
				" We unfold the rule of L1 forwards at position p1\n" +
				" with the rule g(_0) -> h(_0).\n" +
				" ==> L2 = f(_0) -> f(_0) [unit] is in U_IR^2.",
				argument.getDetails(1));
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
