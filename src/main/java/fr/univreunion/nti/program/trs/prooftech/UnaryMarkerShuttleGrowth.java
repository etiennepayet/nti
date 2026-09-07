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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech;

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Recognizes the unary-marker shuttle schemas delegated by
 * {@link TechUnaryShuttleGrowth}.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class UnaryMarkerShuttleGrowth {

	/** Maximum number of rules inspected by this bounded detector. */
	private static final int MAX_RULE_COUNT = 200;

	/** Stable name used by the enclosing proof technique. */
	private static final String WITNESS_KIND = "unary shuttle growth";

	/** Prefix of a rendered certificate line. */
	private static final String CERTIFICATE_PREFIX = "* Certificate: ";

	/** Header of a rendered marker-shuttle proof. */
	private static final String TECHNIQUE_HEADER =
			"* Technique: bounded unary-shuttle growth recognition\n";

	/** Shared transition from a replayed step count to its result. */
	private static final String STEPS_TO_RESULT = " steps to\n";

	/** Prevents instantiation of this utility class. */
	private UnaryMarkerShuttleGrowth() {}

	/** Numbers the bounded input prefix, or rejects an input beyond the bound. */
	private static List<NumberedRule> numberRules(Trs trs) {
		List<NumberedRule> rules = new ArrayList<>();
		int ruleNumber = 1;
		for (RuleTrs rule : trs) {
			if (rules.size() >= MAX_RULE_COUNT)
				return null;
			rules.add(new NumberedRule(ruleNumber++, rule));
		}
		return rules;
	}

	/** Finds a unary-marker shuttle schema and builds its proof argument. */
	static Argument findArgument(Trs trs) {
		List<NumberedRule> rules = numberRules(trs);
		if (rules == null)
			return null;

		for (NumberedRule moveLeftRule : rules) {
			LeftMarkerTransportShape leftTransport =
					leftMarkerTransportShape(moveLeftRule);
			if (leftTransport == null)
				continue;

			for (NumberedRule moveRightRule : rules) {
				FunctionSymbol rightMarker = rightMarker(
						moveRightRule, leftTransport.counter());
				if (rightMarker == null)
					continue;
				MarkerTransportCore core = new MarkerTransportCore(
						moveLeftRule, moveRightRule, leftTransport.counter(),
						leftTransport.leftMarker(), rightMarker);

				Argument pathArgument = findPathMarkerGrowthArgument(rules, core);
				if (pathArgument != null)
					return pathArgument;
				Argument binaryArgument = findBinaryMarkerGrowthArgument(rules, core);
				if (binaryArgument != null)
					return binaryArgument;
			}
		}
		return UnaryBlockShuttleGrowth.findArgument(trs);
	}

	/** Extracts {@code a(L(x)) -> L(a(x))}. */
	private static LeftMarkerTransportShape leftMarkerTransportShape(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol counter = left.getRootSymbol();
		if (counter.getArity() != 1 || left.get(0).isVariable() ||
				left.get(0).getRootSymbol().getArity() != 1 ||
				!(left.get(0).get(0) instanceof Variable variable))
			return null;
		FunctionSymbol leftMarker = left.get(0).getRootSymbol();

		Term right = rule.getRight();
		if (lacksRoot(right, leftMarker) ||
				lacksRoot(right.get(0), counter) ||
				!right.get(0).get(0).deepEquals(variable))
			return null;
		return new LeftMarkerTransportShape(counter, leftMarker);
	}

	/** Extracts the marker from {@code R(a(x)) -> a(R(x))}. */
	private static FunctionSymbol rightMarker(
			NumberedRule numberedRule,
			FunctionSymbol counter) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol marker = left.getRootSymbol();
		if (marker.getArity() != 1 || lacksRoot(left.get(0), counter) ||
				!(left.get(0).get(0) instanceof Variable variable))
			return null;

		Term right = rule.getRight();
		if (lacksRoot(right, counter) || lacksRoot(right.get(0), marker) ||
				!right.get(0).get(0).deepEquals(variable))
			return null;
		return marker;
	}

	/** Finds {@code C[L(x)] -> C[R(x)]} and {@code R(t) -> L(a(t))}. */
	private static Argument findPathMarkerGrowthArgument(
			List<NumberedRule> rules,
			MarkerTransportCore core) {

		for (NumberedRule pumpRule : rules) {
			Term tail = markerPumpTail(pumpRule, core);
			if (tail == null)
				continue;
			for (NumberedRule switchRule : rules) {
				Position switchPosition = markerSwitchPosition(switchRule, core);
				if (switchPosition == null)
					continue;
				PathMarkerSchema schema = new PathMarkerSchema(
						core, pumpRule, switchRule, switchPosition, tail);
				PathMarkerGrowthWitness witness = buildPathMarkerWitness(schema);
				if (witness != null)
					return new PathMarkerGrowthArgument(witness);
			}
		}
		return null;
	}

	/** Returns {@code t} when the rule is {@code R(t) -> L(a(t))}. */
	private static Term markerPumpTail(
			NumberedRule numberedRule,
			MarkerTransportCore core) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (lacksRoot(left, core.rightMarker()))
			return null;
		Term tail = left.get(0);

		Term right = rule.getRight();
		if (lacksRoot(right, core.leftMarker()) ||
				lacksRoot(right.get(0), core.counter()) ||
				!right.get(0).get(0).deepEquals(tail))
			return null;
		return tail;
	}

	/** Returns the unique switched position in {@code C[L(x)] -> C[R(x)]}. */
	private static Position markerSwitchPosition(
			NumberedRule numberedRule,
			MarkerTransportCore core) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		for (Position position : left) {
			Term subterm = left.get(position);
			if (lacksRoot(subterm, core.leftMarker()) ||
					!(subterm.get(0) instanceof Variable variable) ||
					!occursOnce(left, variable))
				continue;
			Term switched = new Function(
					core.rightMarker(), List.of(variable));
			if (left.replace(position, switched).deepEquals(rule.getRight()))
				return position;
		}
		return null;
	}

	/** Returns whether the specified variable occurs exactly once in a term. */
	private static boolean occursOnce(Term term, Variable variable) {
		int occurrenceCount = 0;
		for (Position position : term) {
			if (term.get(position) == variable && ++occurrenceCount > 1)
				return false;
		}
		return occurrenceCount == 1;
	}

	/** Finds a binary marker phase and builds its proof argument. */
	private static Argument findBinaryMarkerGrowthArgument(
			List<NumberedRule> rules,
			MarkerTransportCore core) {

		for (NumberedRule resetRule : rules) {
			Term tail = markerResetTail(resetRule, core);
			if (tail == null)
				continue;
			for (NumberedRule triggerRule : rules) {
				BinaryMarkerTrigger trigger =
						binaryMarkerTrigger(triggerRule, core);
				if (trigger == null)
					continue;
				BinaryMarkerSchema schema = new BinaryMarkerSchema(
						core, resetRule, triggerRule, trigger.state(),
						trigger.swapArguments(), tail);
				BinaryMarkerGrowthWitness witness = buildBinaryMarkerWitness(schema);
				if (witness != null)
					return new BinaryMarkerGrowthArgument(witness);
			}
		}
		return null;
	}

	/** Returns {@code t} when the rule is {@code R(t) -> L(t)}. */
	private static Term markerResetTail(
			NumberedRule numberedRule,
			MarkerTransportCore core) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (lacksRoot(left, core.rightMarker()))
			return null;
		Term tail = left.get(0);
		Term right = rule.getRight();
		return !lacksRoot(right, core.leftMarker()) &&
				right.get(0).deepEquals(tail) ? tail : null;
	}

	/**
	 * Extracts either {@code f(L(x),L(y)) -> f(a(R(x)),R(y))} or its
	 * argument-swapping variant.
	 */
	private static BinaryMarkerTrigger binaryMarkerTrigger(
			NumberedRule numberedRule,
			MarkerTransportCore core) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 2 ||
				lacksRoot(left.get(0), core.leftMarker()) ||
				lacksRoot(left.get(1), core.leftMarker()) ||
				!(left.get(0).get(0) instanceof Variable x) ||
				!(left.get(1).get(0) instanceof Variable y) || x.deepEquals(y))
			return null;

		Term right = rule.getRight();
		if (lacksRoot(right, state) ||
				lacksRoot(right.get(0), core.counter()) ||
				lacksRoot(right.get(0).get(0), core.rightMarker()) ||
				lacksRoot(right.get(1), core.rightMarker()))
			return null;
		Term firstSource = right.get(0).get(0).get(0);
		Term secondSource = right.get(1).get(0);
		if (firstSource.deepEquals(x) && secondSource.deepEquals(y))
			return new BinaryMarkerTrigger(state, false);
		if (firstSource.deepEquals(y) && secondSource.deepEquals(x))
			return new BinaryMarkerTrigger(state, true);
		return null;
	}

	/** Builds and replays the first two-step unary-marker growth phase. */
	private static PathMarkerGrowthWitness buildPathMarkerWitness(
			PathMarkerSchema schema) {

		MarkerTransportCore core = schema.core();
		Term startMarker = successor(schema.tail(), core.rightMarker());
		Term start = schema.switchRule().rule().getLeft().replace(
				schema.switchPosition(), startMarker);
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(
				steps, start, schema.pumpRule(), schema.switchPosition());
		current = addStep(
				steps, current, schema.switchRule(), new Position());

		Term grownTail = successor(schema.tail(), core.counter());
		Term expectedMarker = successor(grownTail, core.rightMarker());
		Term expected = schema.switchRule().rule().getLeft().replace(
				schema.switchPosition(), expectedMarker);
		return current != null && current.isVariantOf(expected) ?
				new PathMarkerGrowthWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Builds and replays one binary-marker phase using every matched rule. */
	private static BinaryMarkerGrowthWitness buildBinaryMarkerWitness(
			BinaryMarkerSchema schema) {

		MarkerTransportCore core = schema.core();
		Term tail = schema.tail();
		Term firstCounter = counterPower(tail, core.counter(), 1);
		Term start = state(
				successor(firstCounter, core.leftMarker()),
				successor(tail, core.leftMarker()), schema.state());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(
				steps, start, schema.triggerRule(), new Position());

		int firstExponent = schema.swapArguments() ? 0 : 1;
		int secondExponent = schema.swapArguments() ? 1 : 0;
		current = normalizeMarker(
				steps, current, schema, new Position(0).addLast(0),
				firstExponent, 1);
		current = normalizeMarker(
				steps, current, schema, new Position(1),
				secondExponent, 0);

		Term expectedFirst = successor(
				counterPower(tail, core.counter(), firstExponent + 1),
				core.leftMarker());
		Term expectedSecond = successor(
				counterPower(tail, core.counter(), secondExponent),
				core.leftMarker());
		Term expected = state(expectedFirst, expectedSecond, schema.state());
		return current != null && current.isVariantOf(expected) ?
				new BinaryMarkerGrowthWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Moves one right marker to its tail, resets it, then moves it left. */
	private static Term normalizeMarker(
			List<RewriteStep> steps,
			Term source,
			BinaryMarkerSchema schema,
			Position markerPosition,
			int counterExponent,
			int leadingCounterCount) {

		Term current = source;
		for (int i = 0; i < counterExponent && current != null; i++) {
			current = addStep(steps, current,
					schema.core().moveRightRule(), markerPosition);
			markerPosition = markerPosition.addLast(0);
		}
		current = addStep(
				steps, current, schema.resetRule(), markerPosition);
		for (int i = 0;
				i < counterExponent + leadingCounterCount && current != null;
				i++) {
			Position parentPosition = markerPosition.properPrefix();
			if (parentPosition == null)
				return null;
			markerPosition = parentPosition;
			current = addStep(steps, current,
					schema.core().moveLeftRule(), markerPosition);
		}
		return current;
	}

	/** Wraps the specified term in the unary counter symbol several times. */
	private static Term counterPower(
			Term base,
			FunctionSymbol counter,
			int exponent) {

		Term result = base;
		for (int i = 0; i < exponent; i++)
			result = successor(result, counter);
		return result;
	}

	/** Applies and records one required rewrite step. */
	private static Term addStep(
			List<RewriteStep> steps,
			Term source,
			NumberedRule numberedRule,
			Position position) {

		if (source == null)
			return null;
		Term redex = source.get(position);
		Substitution substitution = new Substitution();
		RuleTrs rule = numberedRule.rule();
		if (redex == null || !rule.getLeft().isMoreGeneralThan(redex, substitution))
			return null;
		Term target = source.replace(position, rule.getRight().apply(substitution));
		steps.add(new RewriteStep(
				source, target, numberedRule.number(), position));
		return target;
	}

	/** Returns whether the term lacks the specified function symbol at its root. */
	private static boolean lacksRoot(Term term, FunctionSymbol root) {
		return term.isVariable() || term.getRootSymbol() != root;
	}

	/** Builds one unary successor term. */
	private static Term successor(Term argument, FunctionSymbol successor) {
		return new Function(successor, List.of(argument));
	}

	/** Builds one binary state term. */
	private static Term state(Term first, Term second, FunctionSymbol state) {
		return new Function(state, List.of(first, second));
	}

	/** One input rule together with its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Counter and left marker extracted from the left transport rule. */
	private record LeftMarkerTransportShape(
			FunctionSymbol counter,
			FunctionSymbol leftMarker) {}

	/** The two marker-transport rules and their unary symbols. */
	private record MarkerTransportCore(
			NumberedRule moveLeftRule,
			NumberedRule moveRightRule,
			FunctionSymbol counter,
			FunctionSymbol leftMarker,
			FunctionSymbol rightMarker) {}

	/** A marker switch in a unary context together with its pumping rule. */
	private record PathMarkerSchema(
			MarkerTransportCore core,
			NumberedRule pumpRule,
			NumberedRule switchRule,
			Position switchPosition,
			Term tail) {}

	/** Shape of a binary marker trigger. */
	private record BinaryMarkerTrigger(
			FunctionSymbol state,
			boolean swapArguments) {}

	/** A binary marker trigger together with its transport and reset rules. */
	private record BinaryMarkerSchema(
			MarkerTransportCore core,
			NumberedRule resetRule,
			NumberedRule triggerRule,
			FunctionSymbol state,
			boolean swapArguments,
			Term tail) {}

	/** One replayed rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** A replayed unary-context marker growth phase. */
	private record PathMarkerGrowthWitness(
			PathMarkerSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** A replayed binary marker growth phase. */
	private record BinaryMarkerGrowthWitness(
			BinaryMarkerSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** Formats a replayed sequence with original rule numbers and positions. */
	private static String formatRewriteSteps(
			List<RewriteStep> steps,
			int indentation) {

		String spaces = " ".repeat(Math.max(0, indentation));
		String[] lines = new String[steps.size()];
		int stepNumber = 1;
		for (RewriteStep step : steps)
			lines[stepNumber - 1] = spaces + stepNumber++ + ". " +
					step.source() + " -> " + step.target() + " (rule " +
					step.ruleNumber() + ", position " + step.position() + ")";
		return String.join("\n", lines);
	}

	/** Proof argument for marker growth inside one unary context. */
	private record PathMarkerGrowthArgument(
			PathMarkerGrowthWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			return formatRewriteSteps(this.witness.steps(), indentation);
		}

		@Override
		public String getWitnessKind() {
			return WITNESS_KIND;
		}

		@Override
		public String toString() {
			PathMarkerSchema schema = this.witness.schema();
			MarkerTransportCore core = schema.core();
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Let C be the context selected in rule " +
					schema.switchRule().number() + ", and write Tn = " +
					core.counter() + "^n(" + schema.tail() + "). " +
					"The matched transport, pump and switch rules imply, for " +
					"every n >= 0,\nC[" + core.rightMarker() + "(Tn)] " +
					"->^(2n+2) C[" + core.rightMarker() + "(T(n+1))].\n" +
					"Starting with n = 0 yields an infinite rewrite sequence.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO_RESULT +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

	/** Proof argument for marker growth between two unary-spine arguments. */
	private record BinaryMarkerGrowthArgument(
			BinaryMarkerGrowthWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			return formatRewriteSteps(this.witness.steps(), indentation);
		}

		@Override
		public String getWitnessKind() {
			return WITNESS_KIND;
		}

		@Override
		public String toString() {
			BinaryMarkerSchema schema = this.witness.schema();
			MarkerTransportCore core = schema.core();
			String firstExponent = schema.swapArguments() ? "q+1" : "p+1";
			String secondExponent = schema.swapArguments() ? "p" : "q";
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write An = " + core.counter() + "^n(" + schema.tail() +
					"). For every p,q >= 0, the matched rules imply\n" +
					schema.state() + "(" + core.leftMarker() + "(Ap)," +
					core.leftMarker() + "(Aq)) ->+ " + schema.state() + "(" +
					core.leftMarker() + "(A(" + firstExponent + "))," +
					core.leftMarker() + "(A(" + secondExponent + "))).\n" +
					"The sum of the two exponents therefore increases by one " +
					"per phase, yielding an infinite rewrite sequence.\n" +
					"The replayed phase rewrites in " +
					this.witness.steps().size() + STEPS_TO_RESULT +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

}
