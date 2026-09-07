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

package fr.univreunion.nti.program.trs.prooftech;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Variable;

class TechRootVariantCycleTest {

	@Test
	void findTwoRuleCycleModuloVariableRenaming() throws IOException {
		Proof proof = run("f(X) -> g(X)", "g(Y) -> f(Y)");

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertEquals("root variant cycle", proof.getArgument().getWitnessKind());
		assertTrue(proof.getArgument().toString().contains("fresh variable renamings"));
	}

	@Test
	void findOneRuleVariantCycle() throws IOException {
		Proof proof = run("f(X,Y) -> f(Y,X)");

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertTrue(proof.isSuccess());
	}

	@Test
	void findNonlinearCycleFromNot3258() throws IOException {
		Proof proof = run(
				"iapply(iapply(dot,X),X) -> " +
						"iapply(iapply(realu_pow,iapply(vectoru_norm,X)),six)",
				"iapply(iapply(realu_pow,iapply(vectoru_norm,Y)),six) -> " +
						"iapply(iapply(dot,Y),Y)");

		assertEquals(Proof.ProofResult.NO, proof.getResult());
		assertTrue(proof.getArgument().toString().contains("iapply(iapply(dot,_0),_0)"));
	}

	@Test
	void preserveVariableSharingWhenMatchingVariants() throws IOException {
		Proof proof = run("f(X,X) -> g(X,X)", "g(Y,Z) -> f(Y,Z)");

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	void rejectAPathThatDoesNotReturnToTheFirstLeftHandSide() throws IOException {
		Proof proof = run("f(X) -> g(X)", "g(Y) -> h(Y)");

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	@Test
	void leaveGeneralizedRulesToTheDedicatedTechnique() throws IOException {
		Proof proof = run("f(X) -> g(Y)", "g(Y) -> f(X)");

		assertEquals(Proof.ProofResult.MAYBE, proof.getResult());
		assertFalse(proof.isSuccess());
	}

	private static Proof run(String... ruleTexts) throws IOException {
		return new TechRootVariantCycle().run(
				parseTrs(ruleTexts), new AnalysisContext(true, null));
	}

	private static Trs parseTrs(String... ruleTexts) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		List<RuleTrs> rules = new LinkedList<>();
		for (String ruleText : ruleTexts)
			rules.add(parser.parseTrsRule(ruleText, variables));
		return new Trs("", rules, "FULL");
	}
}
