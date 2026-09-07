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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.family;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.util.List;
import java.util.UUID;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

class FdGraphTest {

	@Test
	@DisplayName("compute families without modifying reusable query terms")
	void computeFamiliesWithoutModifyingQueries() {
		String suffix = UUID.randomUUID().toString();
		FunctionSymbol defined = symbol("family-defined-" + suffix, 1);
		FunctionSymbol constructor = symbol("family-constructor-" + suffix, 1);
		FunctionSymbol firstReachable = symbol("family-first-" + suffix, 0);
		FunctionSymbol secondReachable = symbol("family-second-" + suffix, 0);
		FunctionSymbol thirdReachable = symbol("family-third-" + suffix, 0);
		Variable ruleVariable = new Variable();
		Trs trs = new Trs("", List.of(new RuleTrs(
				function(defined, ruleVariable), ruleVariable)), "FULL");
		FdGraph graph = new FdGraph(trs);
		Function firstConstant = function(symbol("family-a-" + suffix, 0));
		Function secondConstant = function(symbol("family-b-" + suffix, 0));
		graph.addEdge(
				function(constructor, firstConstant), function(firstReachable));
		graph.addEdge(
				function(constructor, secondConstant), function(secondReachable));
		graph.addEdge(
				function(defined, firstConstant), function(thirdReachable));
		Term query = function(
				constructor, function(defined, secondConstant));
		String queryRendering = query.toString();

		Family family = graph.getFamily(query);
		Family repeatedFamily = graph.getFamily(query);
		Family variableFamily = graph.getFamily(new Variable());

		assertTrue(family.isReachable(firstReachable));
		assertTrue(family.isReachable(secondReachable));
		assertFalse(family.isReachable(thirdReachable));
		assertEquals(family.toString(), repeatedFamily.toString());
		assertEquals(queryRendering, query.toString());
		assertTrue(variableFamily.isReachable(firstReachable));
		assertTrue(variableFamily.isReachable(secondReachable));
		assertTrue(variableFamily.isReachable(thirdReachable));
	}

	private static FunctionSymbol symbol(String name, int arity) {
		return FunctionSymbol.intern(name, arity);
	}

	private static Function function(FunctionSymbol symbol, Term... arguments) {
		return new Function(symbol, List.of(arguments));
	}
}
