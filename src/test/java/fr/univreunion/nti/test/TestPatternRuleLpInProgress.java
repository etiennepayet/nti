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

package fr.univreunion.nti.test;

import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.lp.patternunfolding.PatternRuleLpInProgress;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;

class TestPatternRuleLpInProgress {

	@Test
	@DisplayName("reject negative iteration")
	void rejectNegativeIteration() {
		assertThrows(
				IllegalArgumentException.class,
				() -> new PatternRuleLpInProgress(-1));
	}

	@Test
	@DisplayName("format pattern rule in progress")
	void formatPatternRuleInProgress() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		SimplePatternSubstitution patternSubstitution =
				parser.parseSimplePatternSubstitution(
						"{X->s(X)}{X->0}",
						variables);
		PatternRuleLpInProgress rule =
				new PatternRuleLpInProgress(patternSubstitution, 2);

		assertEquals(
				patternSubstitution.toString(reverse(variables)) +
				" -- iteration = 2",
				rule.toString(reverse(variables)));
	}

	@Test
	@DisplayName("deep copy preserves content")
	void deepCopyPreservesContent() throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		SimplePatternSubstitution patternSubstitution =
				parser.parseSimplePatternSubstitution(
						"{X->s(X)}{X->0}",
						variables);
		PatternRuleLpInProgress rule =
				new PatternRuleLpInProgress(patternSubstitution, 3);
		Map<Term, Term> copies = new HashMap<>();

		PatternRuleLpInProgress copy = rule.deepCopy(copies);

		assertNotSame(rule, copy);
		assertNotSame(
				rule.getPatternSubstitution(),
				copy.getPatternSubstitution());
		assertEquals(rule.getIteration(), copy.getIteration());
		assertEquals(rule.toString(), copy.toString());
		assertFalse(copies.isEmpty());
	}

	private static Map<Variable, String> reverse(Map<String, Variable> variables) {
		Map<Variable, String> result = new HashMap<>();
		for (Map.Entry<String, Variable> entry : variables.entrySet())
			result.put(entry.getValue(), entry.getKey());

		return result;
	}
}
