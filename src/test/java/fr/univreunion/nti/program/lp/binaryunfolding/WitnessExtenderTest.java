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

package fr.univreunion.nti.program.lp.binaryunfolding;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;

import java.util.List;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.program.lp.BinaryRuleLp;
import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.NonTerminationWitness;
import fr.univreunion.nti.program.lp.SoP;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;

class WitnessExtenderTest {

	@Test
	void preservesGlobalOrderAcrossIndexedAndUnknownWitnesses() {
		Function constant = function("witness-index-constant");
		FunctionSymbol link = symbol("witness-index-link", 1);
		LoopingPair firstLoopingPair = loopingPair(rule(
				new Function(link, List.of(constant)),
				function("witness-index-first-body", constant)));
		NamedWitness unknownWitness = new NamedWitness("unknown");
		LoopingPair secondLoopingPair = loopingPair(rule(
				new Function(link, List.of(constant)),
				function("witness-index-second-body", constant)));
		LoopingPair subclassExtension = loopingPair(rule(
				function("witness-index-subclass-extension", constant),
				function("witness-index-subclass-extension-body", constant)));
		PermissiveLoopingPair loopingPairSubclass = new PermissiveLoopingPair(
				rule(
					function("witness-index-subclass", constant),
					function("witness-index-subclass-body", constant)),
				subclassExtension);
		LoopingPair incompatiblePair = loopingPair(rule(
				function("witness-index-incompatible", constant),
				function("witness-index-incompatible-body", constant)));
		BinaryRuleLp candidate = rule(
				function("witness-index-candidate-head", constant),
				new Function(link, List.of(constant)));

		List<NonTerminationWitness> extensions = WitnessExtender.extend(
				List.of(candidate),
				List.of(
						firstLoopingPair,
						unknownWitness,
						loopingPairSubclass,
						secondLoopingPair,
						incompatiblePair));

		assertEquals(4, extensions.size());
		assertInstanceOf(LoopingPair.class, extensions.get(0));
		assertSame(unknownWitness.extension(), extensions.get(1));
		assertSame(subclassExtension, extensions.get(2));
		assertInstanceOf(LoopingPair.class, extensions.get(3));
	}

	private static LoopingPair loopingPair(BinaryRuleLp rule) {
		return new LoopingPair(List.of(rule), new SoP(List.of(rule)));
	}

	private static BinaryRuleLp rule(Function head, Function body) {
		return new BinaryRuleLp(head, body, 0);
	}

	private static Function function(String name, Function... arguments) {
		return new Function(symbol(name, arguments.length), List.of(arguments));
	}

	private static FunctionSymbol symbol(String name, int arity) {
		return FunctionSymbol.intern(name, arity);
	}

	private static final class NamedWitness implements NonTerminationWitness {

		private final String name;
		private final NonTerminationWitness extension;

		private NamedWitness(String name) {
			this(name, null);
		}

		private NamedWitness(String name, NonTerminationWitness extension) {
			this.name = name;
			this.extension = extension == null ?
					new NamedWitness(name + "-extended", this) : extension;
		}

		private NonTerminationWitness extension() {
			return this.extension;
		}

		@Override
		public NonTerminationWitness add(BinaryRuleLp rule) {
			return this.extension;
		}

		@Override
		public Function provesNonTerminationOf(Mode mode) {
			return null;
		}

		@Override
		public String getShortDescription() {
			return this.name;
		}
	}

	private static final class PermissiveLoopingPair extends LoopingPair {

		private final LoopingPair extension;

		private PermissiveLoopingPair(
				BinaryRuleLp rule,
				LoopingPair extension) {
			super(List.of(rule), new SoP(List.of(rule)));
			this.extension = extension;
		}

		@Override
		public LoopingPair add(BinaryRuleLp rule) {
			return this.extension;
		}
	}
}
