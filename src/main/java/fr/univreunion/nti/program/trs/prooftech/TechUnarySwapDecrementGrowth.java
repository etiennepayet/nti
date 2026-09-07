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

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Recognizes a bounded five-rule schema that grows a unary counter after
 * swapping and decrementing it.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechUnarySwapDecrementGrowth implements ProofTechnique {

	/** Maximum number of rules inspected by this bounded technique. */
	private static final int MAX_RULE_COUNT = 200;

	/** Message emitted when no certified schema was found. */
	private static final String NOT_FOUND_MESSAGE =
			"No unary swap-decrement growth found!";

	/**
	 * Runs this technique on the specified TRS.
	 *
	 * @param trs the TRS to analyze
	 * @param context the context of the analysis
	 * @return the proof built by this technique
	 */
	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose(
				"## Searching for bounded unary swap-decrement growth...");
		SwapDecrementSchema schema = findSchema(trs);
		SwapDecrementWitness witness =
				schema == null ? null : buildWitness(schema);
		if (witness == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		proof.printlnIfVerbose("Found unary swap-decrement growth!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(new UnarySwapDecrementArgument(witness));
		return proof;
	}

	/** Finds the first complete schema in input-rule order. */
	private static SwapDecrementSchema findSchema(Trs trs) {
		List<NumberedRule> rules = new ArrayList<>();
		int ruleNumber = 1;
		for (RuleTrs rule : trs) {
			if (rules.size() >= MAX_RULE_COUNT)
				return null;
			rules.add(new NumberedRule(ruleNumber++, rule));
		}

		for (NumberedRule growthRule : rules) {
			GrowthRuleShape growth = growthRuleShape(growthRule);
			if (growth != null) {
				NumberedRule swapTransferRule =
						findSwapTransferRule(rules, growth);
				if (swapTransferRule != null) {
					for (NumberedRule swapExitRule : rules) {
						SwapExitShape swapExit =
								swapExitShape(swapExitRule, growth);
						if (swapExit == null)
							continue;
						NumberedRule decrementRule =
								findDecrementRule(rules, growth, swapExit);
						NumberedRule decrementZeroRule =
								findDecrementZeroRule(rules, growth, swapExit);
						if (decrementRule != null && decrementZeroRule != null)
							return new SwapDecrementSchema(
									growthRule, swapTransferRule, swapExitRule,
									decrementRule, decrementZeroRule,
									growth.state(), growth.truth(), growth.swap(),
									growth.successor(), swapExit.decrement(),
									growth.zero());
					}
				}
			}
		}
		return null;
	}

	/** Extracts {@code f(tt,x) -> f(swap(x,0),s(x))}. */
	private static GrowthRuleShape growthRuleShape(NumberedRule numberedRule) {
		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 2 || !isConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable x))
			return null;
		Term truth = left.get(0);

		Term right = rule.getRight();
		if (lacksRoot(right, state) || right.get(0).isVariable() ||
				right.get(0).getRootSymbol().getArity() != 2 ||
				!right.get(0).get(0).deepEquals(x) ||
				!isConstant(right.get(0).get(1)) || right.get(1).isVariable() ||
				right.get(1).getRootSymbol().getArity() != 1 ||
				!right.get(1).get(0).deepEquals(x))
			return null;
		return new GrowthRuleShape(
				state, truth, right.get(0).getRootSymbol(),
				right.get(1).getRootSymbol(), right.get(0).get(1));
	}

	/** Finds {@code swap(s(x),y) -> swap(x,s(y))}. */
	private static NumberedRule findSwapTransferRule(
			List<NumberedRule> rules,
			GrowthRuleShape growth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, growth.swap()) ||
					lacksRoot(left.get(0), growth.successor()) ||
					!(left.get(0).get(0) instanceof Variable x) ||
					!(left.get(1) instanceof Variable y) || x.deepEquals(y))
				continue;

			Term right = rule.getRight();
			if (!lacksRoot(right, growth.swap()) &&
					right.get(0).deepEquals(x) &&
					!lacksRoot(right.get(1), growth.successor()) &&
					right.get(1).get(0).deepEquals(y))
				return numberedRule;
		}
		return null;
	}

	/** Extracts {@code swap(0,s(y)) -> decr(s(y))}. */
	private static SwapExitShape swapExitShape(
			NumberedRule numberedRule,
			GrowthRuleShape growth) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (lacksRoot(left, growth.swap()) ||
				!left.get(0).deepEquals(growth.zero()) ||
				lacksRoot(left.get(1), growth.successor()) ||
				!(left.get(1).get(0) instanceof Variable y))
			return null;

		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 1 ||
				lacksRoot(right.get(0), growth.successor()) ||
				!right.get(0).get(0).deepEquals(y))
			return null;
		return new SwapExitShape(right.getRootSymbol());
	}

	/** Finds {@code decr(s(y)) -> decr(y)}. */
	private static NumberedRule findDecrementRule(
			List<NumberedRule> rules,
			GrowthRuleShape growth,
			SwapExitShape swapExit) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, swapExit.decrement()) ||
					lacksRoot(left.get(0), growth.successor()) ||
					!(left.get(0).get(0) instanceof Variable y))
				continue;

			Term right = rule.getRight();
			if (!lacksRoot(right, swapExit.decrement()) &&
					right.get(0).deepEquals(y))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code decr(0) -> tt}. */
	private static NumberedRule findDecrementZeroRule(
			List<NumberedRule> rules,
			GrowthRuleShape growth,
			SwapExitShape swapExit) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!lacksRoot(left, swapExit.decrement()) &&
					left.get(0).deepEquals(growth.zero()) &&
					rule.getRight().deepEquals(growth.truth()))
				return numberedRule;
		}
		return null;
	}

	/** Builds and replays the first five-step growth phase. */
	private static SwapDecrementWitness buildWitness(
			SwapDecrementSchema schema) {

		Term one = successor(schema.zero(), schema.successor());
		Term two = successor(one, schema.successor());
		Term start = state(schema.truth(), one, schema.state());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(steps, start, schema.growthRule(), position());
		current = addStep(
				steps, current, schema.swapTransferRule(), position(0));
		current = addStep(steps, current, schema.swapExitRule(), position(0));
		current = addStep(steps, current, schema.decrementRule(), position(0));
		current = addStep(
				steps, current, schema.decrementZeroRule(), position(0));

		Term expected = state(schema.truth(), two, schema.state());
		return current != null && current.deepEquals(expected) ?
				new SwapDecrementWitness(schema, start, current, List.copyOf(steps)) :
				null;
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

	/** Returns whether the term is a constant. */
	private static boolean isConstant(Term term) {
		return !term.isVariable() && term.getRootSymbol().getArity() == 0;
	}

	/** Builds one unary successor term. */
	private static Term successor(Term argument, FunctionSymbol successor) {
		return new Function(successor, List.of(argument));
	}

	/** Builds one binary state term. */
	private static Term state(Term first, Term second, FunctionSymbol state) {
		return new Function(state, List.of(first, second));
	}

	/** Builds a position from its successive child indexes. */
	private static Position position(int... indexes) {
		Position position = new Position();
		for (int index : indexes)
			position = position.addLast(index);
		return position;
	}

	/** One input rule together with its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Symbols and constants extracted from the growth rule. */
	private record GrowthRuleShape(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol swap,
			FunctionSymbol successor,
			Term zero) {}

	/** Symbol extracted from the swap-exit rule. */
	private record SwapExitShape(FunctionSymbol decrement) {}

	/** A complete matched rule schema. */
	private record SwapDecrementSchema(
			NumberedRule growthRule,
			NumberedRule swapTransferRule,
			NumberedRule swapExitRule,
			NumberedRule decrementRule,
			NumberedRule decrementZeroRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol swap,
			FunctionSymbol successor,
			FunctionSymbol decrement,
			Term zero) {}

	/** One replayed rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** The matched schema and its concrete first growth phase. */
	private record SwapDecrementWitness(
			SwapDecrementSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** Proof argument for a certified unary swap/decrement schema. */
	private record UnarySwapDecrementArgument(
			SwapDecrementWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			StringBuilder details = new StringBuilder();
			int stepNumber = 1;
			for (RewriteStep step : this.witness.steps()) {
				details.append(spaces).append(stepNumber++).append(". ")
						.append(step.source()).append(" -> ").append(step.target())
						.append(" (rule ").append(step.ruleNumber())
						.append(", position ").append(step.position()).append(")\n");
			}
			if (!details.isEmpty())
				details.setLength(details.length() - 1);
			return details.toString();
		}

		@Override
		public String getWitnessKind() {
			return "unary swap-decrement growth";
		}

		@Override
		public String toString() {
			SwapDecrementSchema schema = this.witness.schema();
			String state = schema.state().toString();
			String truth = schema.truth().toString();
			String swap = schema.swap().toString();
			String successor = schema.successor().toString();
			String decrement = schema.decrement().toString();
			String zero = schema.zero().toString();
			return "* Technique: bounded unary swap-decrement growth " +
					"recognition\n" +
					"* Certificate: " + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write n-bar for " + successor + "^n(" + zero + "). " +
					"For every n >= 1, the matched rules imply\n" +
					state + "(" + truth + ",n-bar) -> " + state + "(" +
					swap + "(n-bar,0-bar),(n+1)-bar)\n" +
					"->^n " + state + "(" + swap +
					"(0-bar,n-bar),(n+1)-bar) -> " + state + "(" +
					decrement + "(n-bar),(n+1)-bar)\n" +
					"->^n " + state + "(" + decrement +
					"(0-bar),(n+1)-bar) -> " + state + "(" + truth +
					",(n+1)-bar).\n" +
					"Thus " + state + "(" + truth +
					",n-bar) rewrites in 2n+3 steps to " + state + "(" +
					truth + ",(n+1)-bar). Starting with n = 1 yields an " +
					"infinite rewrite sequence.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + " steps to\n" +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}
}
