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

package fr.univreunion.nti.program.trs.ruleunfolding;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.string.ParserString;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Variable;

class SimpleCycleRegistryTest {

	@Test
	@DisplayName("store cycles by set equality and clear them")
	void storeCyclesBySetEqualityAndClearThem() throws IOException {
		RuleTrs firstRule = parseRule("f(X) -> g(X)");
		RuleTrs secondRule = parseRule("g(X) -> f(X)");
		Set<RuleTrs> cycle = Set.of(firstRule, secondRule);
		SimpleCycleRegistry registry = new SimpleCycleRegistry();

		assertFalse(registry.contains(cycle));
		assertTrue(registry.add(cycle));
		assertTrue(registry.contains(Set.of(secondRule, firstRule)));

		registry.clear();
		assertFalse(registry.contains(cycle));
	}

	private static RuleTrs parseRule(String ruleText) throws IOException {
		ParserString parser = new ParserString();
		Map<String, Variable> variables = new HashMap<>();
		return parser.parseTrsRule(ruleText, variables);
	}
}
