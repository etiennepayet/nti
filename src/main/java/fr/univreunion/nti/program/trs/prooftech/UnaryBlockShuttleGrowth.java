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
 * Recognizes modular block growth caused by a unary marker shuttling between
 * equal boundaries. This is the block-specialized part of
 * {@link TechUnaryShuttleGrowth}.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class UnaryBlockShuttleGrowth {

	/** Maximum number of rules inspected by this bounded detector. */
	private static final int MAX_RULE_COUNT = 200;

	/** Maximum unary stride inspected in a block-shuttle rule. */
	private static final int MAX_BLOCK_STRIDE = 8;

	/** Maximum number of steps in a replayed block-shuttle prefix. */
	private static final int MAX_BLOCK_REPLAY_STEPS = 256;

	/** Stable name used by the enclosing proof technique. */
	private static final String WITNESS_KIND = "unary shuttle growth";

	/** Prefix of a rendered certificate line. */
	private static final String CERTIFICATE_PREFIX = "* Certificate: ";

	/** Header of a rendered block-shuttle proof. */
	private static final String TECHNIQUE_HEADER =
			"* Technique: bounded unary-shuttle growth recognition\n";

	/** Shared transition from a replayed step count to its result. */
	private static final String STEPS_TO_RESULT = " steps to\n";

	/** Prevents instantiation of this utility class. */
	private UnaryBlockShuttleGrowth() {}

	/** Finds the first replayable modular block-shuttle argument. */
	static Argument findArgument(Trs trs) {
		List<NumberedRule> rules = numberRules(trs);
		if (rules == null)
			return null;
		return findArgument(rules);
	}

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

	/** Finds block growth from the first matching left transport. */
	private static Argument findArgument(List<NumberedRule> rules) {
		for (NumberedRule moveLeftRule : rules) {
			BlockLeftShape left = blockLeftShape(moveLeftRule);
			if (left == null)
				continue;
			Argument argument = findArgument(rules, moveLeftRule, left);
			if (argument != null)
				return argument;
		}
		return null;
	}

	/** Completes a block-shuttle schema from a fixed left-transport rule. */
	private static Argument findArgument(
			List<NumberedRule> rules,
			NumberedRule moveLeftRule,
			BlockLeftShape left) {

		for (NumberedRule moveRightRule : rules) {
			BlockRightShape right = blockRightShape(moveRightRule, left);
			if (right == null)
				continue;
			Argument argument = findArgument(
					rules, moveLeftRule, left, moveRightRule, right);
			if (argument != null)
				return argument;
		}
		return null;
	}

	/** Completes and replays a block schema from fixed transport rules. */
	private static Argument findArgument(
			List<NumberedRule> rules,
			NumberedRule moveLeftRule,
			BlockLeftShape left,
			NumberedRule moveRightRule,
			BlockRightShape right) {

		for (NumberedRule activationRule : rules) {
			BlockActivationShape activation = blockActivationShape(
					activationRule, left, right);
			if (activation == null)
				continue;
			List<BlockSwitch> switches = findBlockSwitches(
					rules, left, right, activation);
			BlockMarkerSchema schema = buildBlockMarkerSchema(
					moveLeftRule, left, moveRightRule, right,
					activationRule, activation, switches);
			Argument argument = schema == null ? null : buildArgument(schema);
			if (argument != null)
				return argument;
		}
		return null;
	}

	/** Extracts {@code a^l(L(x)) -> L(a^l(x))}. */
	private static BlockLeftShape blockLeftShape(NumberedRule numberedRule) {
		RuleTrs rule = numberedRule.rule();
		Function leftTerm = rule.getLeft();
		FunctionSymbol counter = leftTerm.getRootSymbol();
		if (counter.getArity() != 1)
			return null;

		UnaryPower leftPower = unaryPower(leftTerm, counter);
		if (leftPower == null || leftPower.exponent() == 0 ||
				leftPower.base().isVariable() ||
				leftPower.base().getRootSymbol().getArity() != 1 ||
				!(leftPower.base().get(0) instanceof Variable variable))
			return null;
		FunctionSymbol leftMarker = leftPower.base().getRootSymbol();

		Term rightTerm = rule.getRight();
		if (lacksRoot(rightTerm, leftMarker))
			return null;
		UnaryPower rightPower = unaryPower(rightTerm.get(0), counter);
		return rightPower != null &&
				rightPower.exponent() == leftPower.exponent() &&
				rightPower.base().deepEquals(variable) ?
				new BlockLeftShape(
						counter, leftMarker, leftPower.exponent()) : null;
	}

	/** Extracts {@code R(a^r(x)) -> a^m(R(x))}. */
	private static BlockRightShape blockRightShape(
			NumberedRule numberedRule,
			BlockLeftShape left) {

		RuleTrs rule = numberedRule.rule();
		Function leftTerm = rule.getLeft();
		FunctionSymbol rightMarker = leftTerm.getRootSymbol();
		if (rightMarker.getArity() != 1)
			return null;
		UnaryPower input = unaryPower(leftTerm.get(0), left.counter());
		if (input == null || input.exponent() == 0 ||
				!(input.base() instanceof Variable variable))
			return null;

		UnaryPower output = unaryPower(rule.getRight(), left.counter());
		if (output == null || output.exponent() == 0 ||
				lacksRoot(output.base(), rightMarker) ||
				!output.base().get(0).deepEquals(variable))
			return null;
		return new BlockRightShape(
				rightMarker, input.exponent(), output.exponent());
	}

	/** Extracts {@code b(L(x)) -> b(R(a^g(x)))}. */
	private static BlockActivationShape blockActivationShape(
			NumberedRule numberedRule,
			BlockLeftShape left,
			BlockRightShape right) {

		RuleTrs rule = numberedRule.rule();
		Function leftTerm = rule.getLeft();
		FunctionSymbol boundary = leftTerm.getRootSymbol();
		if (boundary.getArity() != 1 ||
				lacksRoot(leftTerm.get(0), left.leftMarker()) ||
				!(leftTerm.get(0).get(0) instanceof Variable variable))
			return null;

		Term rightTerm = rule.getRight();
		if (lacksRoot(rightTerm, boundary) ||
				lacksRoot(rightTerm.get(0), right.rightMarker()))
			return null;
		UnaryPower growth = unaryPower(
				rightTerm.get(0).get(0), left.counter());
		return growth != null && growth.base().deepEquals(variable) ?
				new BlockActivationShape(boundary, growth.exponent()) : null;
	}

	/** Finds every rule switching the right marker at the inner boundary. */
	private static List<BlockSwitch> findBlockSwitches(
			List<NumberedRule> rules,
			BlockLeftShape left,
			BlockRightShape right,
			BlockActivationShape activation) {

		List<BlockSwitch> switches = new ArrayList<>();
		for (NumberedRule numberedRule : rules) {
			BlockSwitch markerSwitch = blockSwitchShape(
					numberedRule, left, right, activation);
			if (markerSwitch != null)
				switches.add(markerSwitch);
		}
		return switches;
	}

	/** Extracts {@code R(a^e(b(x))) -> a^c(L(a^d(b(x))))}. */
	private static BlockSwitch blockSwitchShape(
			NumberedRule numberedRule,
			BlockLeftShape left,
			BlockRightShape right,
			BlockActivationShape activation) {

		RuleTrs rule = numberedRule.rule();
		Function leftTerm = rule.getLeft();
		if (lacksRoot(leftTerm, right.rightMarker()))
			return null;
		UnaryPower residue = unaryPower(leftTerm.get(0), left.counter());
		if (residue == null || lacksRoot(residue.base(), activation.boundary()) ||
				!(residue.base().get(0) instanceof Variable variable))
			return null;

		UnaryPower leading = unaryPower(rule.getRight(), left.counter());
		if (leading == null || lacksRoot(leading.base(), left.leftMarker()))
			return null;
		UnaryPower trailing = unaryPower(
				leading.base().get(0), left.counter());
		if (trailing == null ||
				lacksRoot(trailing.base(), activation.boundary()) ||
				!trailing.base().get(0).deepEquals(variable))
			return null;
		return new BlockSwitch(
				numberedRule, residue.exponent(), leading.exponent(),
				trailing.exponent());
	}

	/** Builds the residue table that certifies strict growth for every block. */
	private static BlockMarkerSchema buildBlockMarkerSchema(
			NumberedRule moveLeftRule,
			BlockLeftShape left,
			NumberedRule moveRightRule,
			BlockRightShape right,
			NumberedRule activationRule,
			BlockActivationShape activation,
			List<BlockSwitch> switches) {

		if (right.outputStride() < right.inputStride() ||
				(left.stride() != 1 && right.inputStride() != 1))
			return null;
		int period = left.stride() == 1 ?
				right.inputStride() : left.stride();
		List<BlockTransition> transitions = new ArrayList<>();
		for (int residue = 0; residue < period; residue++) {
			BlockTransition transition = findBlockTransition(
					residue, period, left, right, activation, switches);
			if (transition == null)
				return null;
			transitions.add(transition);
		}
		return new BlockMarkerSchema(
				moveLeftRule, moveRightRule, activationRule,
				List.copyOf(transitions), left.counter(), left.leftMarker(),
				right.rightMarker(), activation.boundary(), left.stride(),
				right.inputStride(), right.outputStride(), activation.growth(),
				period);
	}

	/** Selects one growing boundary switch for an input residue class. */
	private static BlockTransition findBlockTransition(
			int inputResidue,
			int period,
			BlockLeftShape left,
			BlockRightShape right,
			BlockActivationShape activation,
			List<BlockSwitch> switches) {

		int available = inputResidue + activation.growth();
		int rightMoves = available / right.inputStride();
		int rightResidue = available % right.inputStride();
		for (BlockSwitch markerSwitch : switches) {
			int leftCount = rightMoves * right.outputStride() +
					markerSwitch.leadingCount();
			int result = leftCount + markerSwitch.trailingCount();
			if (markerSwitch.rightResidue() == rightResidue &&
					leftCount % left.stride() == 0 && result > inputResidue)
				return new BlockTransition(
						inputResidue % period, markerSwitch);
		}
		return null;
	}

	/** Peels a bounded number of occurrences of one unary symbol. */
	private static UnaryPower unaryPower(
			Term term,
			FunctionSymbol symbol) {

		int exponent = 0;
		Term base = term;
		while (!lacksRoot(base, symbol)) {
			if (exponent >= MAX_BLOCK_STRIDE)
				return null;
			exponent++;
			base = base.get(0);
		}
		return new UnaryPower(exponent, base);
	}

	/** Builds and replays two complete block-shuttle phases. */
	private static Argument buildArgument(
			BlockMarkerSchema schema) {

		Term tail = new Variable();
		int exponent = 0;
		Term start = blockMarkerState(schema, exponent, tail);
		List<RewriteStep> steps = new ArrayList<>();
		Term current = start;
		for (int phase = 0; phase < 2; phase++) {
			current = applyBlockMarkerPhase(
					steps, current, schema, exponent);
			exponent = blockResultExponent(schema, exponent);
		}

		Term expected = blockMarkerState(schema, exponent, tail);
		return current != null && current.deepEquals(expected) ?
				new BlockMarkerGrowthArgument(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Replays one complete right-and-left marker traversal. */
	private static Term applyBlockMarkerPhase(
			List<RewriteStep> steps,
			Term source,
			BlockMarkerSchema schema,
			int exponent) {

		BlockSwitch markerSwitch = blockTransition(schema, exponent).markerSwitch();
		int rightMoves = (exponent + schema.growth()) /
				schema.rightInputStride();
		int leftCount = rightMoves * schema.rightOutputStride() +
				markerSwitch.leadingCount();
		int leftMoves = leftCount / schema.leftStride();
		if (steps.size() + rightMoves + leftMoves + 2 >
				MAX_BLOCK_REPLAY_STEPS)
			return null;

		Term current = addStep(
				steps, source, schema.activationRule(), new Position());
		Position markerPosition = new Position(0);
		for (int i = 0; i < rightMoves && current != null; i++) {
			current = addStep(
					steps, current, schema.moveRightRule(), markerPosition);
			markerPosition = descend(
					markerPosition, schema.rightOutputStride());
		}
		current = addStep(
				steps, current, markerSwitch.rule(), markerPosition);

		Position leftMarkerPosition = descend(
				markerPosition, markerSwitch.leadingCount());
		for (int i = 0; i < leftMoves && current != null; i++) {
			Position redexPosition = ascend(
					leftMarkerPosition, schema.leftStride());
			if (redexPosition == null)
				return null;
			current = addStep(
					steps, current, schema.moveLeftRule(), redexPosition);
			leftMarkerPosition = redexPosition;
		}
		return current;
	}

	/** Computes the strictly larger block exponent after one phase. */
	private static int blockResultExponent(
			BlockMarkerSchema schema,
			int exponent) {

		BlockSwitch markerSwitch = blockTransition(schema, exponent).markerSwitch();
		int rightMoves = (exponent + schema.growth()) /
				schema.rightInputStride();
		return rightMoves * schema.rightOutputStride() +
				markerSwitch.leadingCount() + markerSwitch.trailingCount();
	}

	/** Returns the selected switch for the exponent's residue class. */
	private static BlockTransition blockTransition(
			BlockMarkerSchema schema,
			int exponent) {

		return schema.transitions().get(exponent % schema.period());
	}

	/** Builds {@code b(L(a^n(b(x))))}. */
	private static Term blockMarkerState(
			BlockMarkerSchema schema,
			int exponent,
			Term tail) {

		Term innerBoundary = unary(tail, schema.boundary());
		Term block = counterPower(innerBoundary, schema.counter(), exponent);
		Term markedBlock = unary(block, schema.leftMarker());
		return unary(markedBlock, schema.boundary());
	}

	/** Descends through the first child the specified number of times. */
	private static Position descend(Position position, int count) {
		Position result = position;
		for (int i = 0; i < count; i++)
			result = result.addLast(0);
		return result;
	}

	/** Ascends the specified number of times, or returns {@code null}. */
	private static Position ascend(Position position, int count) {
		Position result = position;
		for (int i = 0; i < count && result != null; i++)
			result = result.properPrefix();
		return result;
	}

	/** Wraps the specified term in the unary counter symbol several times. */
	private static Term counterPower(
			Term base,
			FunctionSymbol counter,
			int exponent) {

		Term result = base;
		for (int i = 0; i < exponent; i++)
			result = unary(result, counter);
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

	/** Returns whether the term lacks the specified root symbol. */
	private static boolean lacksRoot(Term term, FunctionSymbol root) {
		return term.isVariable() || term.getRootSymbol() != root;
	}

	/** Builds one unary application. */
	private static Term unary(Term argument, FunctionSymbol root) {
		return new Function(root, List.of(argument));
	}

	/** One input rule together with its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** A bounded unary power and the term below it. */
	private record UnaryPower(int exponent, Term base) {}

	/** Left-marker transport and its unary stride. */
	private record BlockLeftShape(
			FunctionSymbol counter,
			FunctionSymbol leftMarker,
			int stride) {}

	/** Right-marker transport and its input/output strides. */
	private record BlockRightShape(
			FunctionSymbol rightMarker,
			int inputStride,
			int outputStride) {}

	/** Equal boundary and block growth extracted from the activation rule. */
	private record BlockActivationShape(
			FunctionSymbol boundary,
			int growth) {}

	/** One marker switch at the inner boundary. */
	private record BlockSwitch(
			NumberedRule rule,
			int rightResidue,
			int leadingCount,
			int trailingCount) {}

	/** Selected switch for one input residue class. */
	private record BlockTransition(
			int inputResidue,
			BlockSwitch markerSwitch) {}

	/** Complete modular block-shuttle schema. */
	private record BlockMarkerSchema(
			NumberedRule moveLeftRule,
			NumberedRule moveRightRule,
			NumberedRule activationRule,
			List<BlockTransition> transitions,
			FunctionSymbol counter,
			FunctionSymbol leftMarker,
			FunctionSymbol rightMarker,
			FunctionSymbol boundary,
			int leftStride,
			int rightInputStride,
			int rightOutputStride,
			int growth,
			int period) {}

	/** One replayed rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** Proof argument for modular block growth between equal boundaries. */
	private record BlockMarkerGrowthArgument(
			BlockMarkerSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) implements Argument {

		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			String[] lines = new String[this.steps.size()];
			int stepNumber = 1;
			for (RewriteStep step : this.steps)
				lines[stepNumber - 1] = spaces + stepNumber++ + ". " +
						step.source() + " -> " + step.target() + " (rule " +
						step.ruleNumber() + ", position " + step.position() + ")";
			return String.join("\n", lines);
		}

		@Override
		public String getWitnessKind() {
			return WITNESS_KIND;
		}

		@Override
		public String toString() {
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.start +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write Tn = " + schema.boundary() + "(" +
					schema.leftMarker() + "(" + schema.counter() + "^n(" +
					schema.boundary() + "(x)))). Let l = " +
					schema.leftStride() + ", r = " +
					schema.rightInputStride() + ", m = " +
					schema.rightOutputStride() + " and g = " +
					schema.growth() + ".\n" +
					"For q = floor((n+g)/r), the right marker crosses q " +
					"blocks. A selected boundary rule contributes c counters " +
					"before the left marker and d after it, so the matched " +
					"rules give Tn ->+ T(qm+c+d).\n" +
					transitionTable(schema) +
					"For each residue class, l divides qm+c and qm+c+d > n. " +
					"Since m >= r and either l = 1 or r = 1, both properties " +
					"persist throughout that class. Thus every Tn rewrites " +
					"to a strictly larger T-term, yielding an infinite " +
					"rewrite sequence.\n" +
					"The replayed two-phase prefix rewrites in " +
					this.steps.size() + STEPS_TO_RESULT +
					this.result + ".\n" + getDetails(0);
		}

		/** Formats the finite residue table used by the induction. */
		private static String transitionTable(BlockMarkerSchema schema) {
			String[] lines = new String[schema.transitions().size()];
			int lineNumber = 0;
			for (BlockTransition transition : schema.transitions()) {
				BlockSwitch markerSwitch = transition.markerSwitch();
				lines[lineNumber++] = "- n mod " + schema.period() + " = " +
						transition.inputResidue() + ": rule " +
						markerSwitch.rule().number() + " (c=" +
						markerSwitch.leadingCount() + ", d=" +
						markerSwitch.trailingCount() + ")";
			}
			return "Selected residue table:\n" + String.join("\n", lines) + "\n";
		}
	}
}
