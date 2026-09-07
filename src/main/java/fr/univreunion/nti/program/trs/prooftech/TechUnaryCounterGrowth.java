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
 * Recognizes bounded structural schemas that repeatedly grow unary counters.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechUnaryCounterGrowth implements ProofTechnique {

	/** Maximum number of rules inspected by this bounded technique. */
	private static final int MAX_RULE_COUNT = 200;

	/** Message emitted when no certified schema was found. */
	private static final String NOT_FOUND_MESSAGE =
			"No unary counter growth found!";

	/** Stable name used by proof arguments produced by this technique. */
	private static final String WITNESS_KIND = "unary counter growth";

	/** Header shared by proof arguments produced by this technique. */
	private static final String TECHNIQUE_HEADER =
			"* Technique: bounded unary-counter growth recognition\n";

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
		proof.printlnIfVerbose("## Searching for bounded unary counter growth...");
		List<NumberedRule> rules = numberRules(trs);
		Argument argument = rules == null ? null : findArgument(rules);
		if (argument == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		proof.printlnIfVerbose("Found unary counter growth!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(argument);
		return proof;
	}

	/** Numbers the input rules, provided that the bounded limit is respected. */
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

	/** Finds the first replayable unary-counter argument. */
	private static Argument findArgument(List<NumberedRule> rules) {
		CounterSchema counterSchema = findSchema(rules);
		CounterGrowthWitness counterWitness = counterSchema == null ? null :
				buildWitness(counterSchema);
		if (counterWitness != null)
			return new UnaryCounterGrowthArgument(counterWitness);

		ArithmeticSchema arithmeticSchema = findArithmeticSchema(rules);
		ArithmeticGrowthWitness arithmeticWitness = arithmeticSchema == null ? null :
				buildArithmeticWitness(arithmeticSchema);
		return arithmeticWitness == null ? null :
				new ArithmeticCounterGrowthArgument(arithmeticWitness);
	}

	/** Finds the first complete schema in input-rule order. */
	private static CounterSchema findSchema(List<NumberedRule> rules) {
		for (NumberedRule firstRule : rules) {
			FirstRuleShape first = firstRuleShape(firstRule);
			if (first == null)
				continue;
			for (NumberedRule secondRule : rules) {
				SecondRuleShape second = secondRuleShape(secondRule, first);
				if (second == null)
					continue;
				NumberedRule zeroRule = findZeroRule(rules, first, second);
				NumberedRule doublingRule = findDoublingRule(rules, first);
				if (zeroRule != null && doublingRule != null)
					return new CounterSchema(
							firstRule, secondRule, zeroRule, doublingRule,
							first.state(), first.successor(), first.doubling(),
							second.zero());
			}
		}
		return null;
	}

	/** Finds the arithmetic schema {@code (p,q) -> (2p,q+1)}. */
	private static ArithmeticSchema findArithmeticSchema(
			List<NumberedRule> rules) {

		for (NumberedRule growthRule : rules) {
			ArithmeticGrowthShape growth = arithmeticGrowthShape(growthRule);
			if (growth == null)
				continue;
			for (NumberedRule positiveRule : rules) {
				ArithmeticSchema schema = completeArithmeticSchema(
						rules, growthRule, growth, positiveRule);
				if (schema != null)
					return schema;
			}
		}
		return null;
	}

	/** Completes one arithmetic schema from fixed growth and positive rules. */
	private static ArithmeticSchema completeArithmeticSchema(
			List<NumberedRule> rules,
			NumberedRule growthRule,
			ArithmeticGrowthShape growth,
			NumberedRule positiveRule) {

		PositiveComparisonShape positive = positiveComparisonShape(
				positiveRule, growth);
		if (positive == null)
			return null;

		NumberedRule comparisonRule = findComparisonRule(rules, growth);
		DoubleShape doubling = findDoubleRule(rules, growth, positive.zero());
		if (comparisonRule == null || doubling == null)
			return null;

		NumberedRule timesBaseRule = findTimesBaseRule(
				rules, doubling.times(), positive.zero());
		TimesShape times = findTimesRule(
				rules, doubling.times(), growth.successor());
		if (timesBaseRule == null || times == null)
			return null;

		NumberedRule plusBaseRule = findPlusBaseRule(
				rules, times.plus(), positive.zero());
		AdditionShape addition = findAdditionRule(
				rules, times.plus(), growth.successor());
		if (plusBaseRule == null || addition == null)
			return null;

		return new ArithmeticSchema(
				growthRule, positiveRule, comparisonRule, doubling.rule(),
				timesBaseRule, times.rule(), plusBaseRule, addition.rule(),
				growth.state(), growth.truth(), growth.successor(),
				growth.doubling(), positive.zero(), addition.kind());
	}

	/** Extracts {@code f(true,x,y) -> f(gt(x,y),double(x),s(y))}. */
	private static ArithmeticGrowthShape arithmeticGrowthShape(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 3 || isNotConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable x) ||
				!(left.get(2) instanceof Variable y) || x.deepEquals(y))
			return null;

		Term right = rule.getRight();
		if (!hasRoot(right, state))
			return null;
		Term comparison = right.get(0);
		Term doubling = right.get(1);
		Term successor = right.get(2);
		if (comparison.isVariable() ||
				comparison.getRootSymbol().getArity() != 2 ||
				!comparison.get(0).deepEquals(x) ||
				!comparison.get(1).deepEquals(y) ||
				doubling.isVariable() ||
				doubling.getRootSymbol().getArity() != 1 ||
				!doubling.get(0).deepEquals(x) ||
				successor.isVariable() ||
				successor.getRootSymbol().getArity() != 1 ||
				!successor.get(0).deepEquals(y))
			return null;

		return new ArithmeticGrowthShape(
				state, left.get(0), comparison.getRootSymbol(),
				doubling.getRootSymbol(), successor.getRootSymbol());
	}

	/** Extracts {@code gt(s(x),0) -> true}. */
	private static PositiveComparisonShape positiveComparisonShape(
			NumberedRule numberedRule,
			ArithmeticGrowthShape growth) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, growth.comparison()) ||
				!hasRoot(left.get(0), growth.successor()) ||
				!(left.get(0).get(0) instanceof Variable) ||
				isNotConstant(left.get(1)) ||
				!rule.getRight().deepEquals(growth.truth()))
			return null;
		return new PositiveComparisonShape(left.get(1));
	}

	/** Finds {@code gt(s(x),s(y)) -> gt(x,y)}. */
	private static NumberedRule findComparisonRule(
			List<NumberedRule> rules,
			ArithmeticGrowthShape growth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, growth.comparison()) ||
					!hasRoot(left.get(0), growth.successor()) ||
					!hasRoot(left.get(1), growth.successor()) ||
					!(left.get(0).get(0) instanceof Variable x) ||
					!(left.get(1).get(0) instanceof Variable y) ||
					x.deepEquals(y))
				continue;
			Term right = rule.getRight();
			if (hasRoot(right, growth.comparison()) &&
					right.get(0).deepEquals(x) && right.get(1).deepEquals(y))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code double(x) -> times(x,s(s(0)))}. */
	private static DoubleShape findDoubleRule(
			List<NumberedRule> rules,
			ArithmeticGrowthShape growth,
			Term zero) {

		Term two = successor(successor(zero, growth.successor()),
				growth.successor());
		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, growth.doubling()) ||
					!(left.get(0) instanceof Variable x))
				continue;
			Term right = rule.getRight();
			if (!right.isVariable() && right.getRootSymbol().getArity() == 2 &&
					right.get(0).deepEquals(x) && right.get(1).deepEquals(two))
				return new DoubleShape(numberedRule, right.getRootSymbol());
		}
		return null;
	}

	/** Finds {@code times(0,y) -> 0}. */
	private static NumberedRule findTimesBaseRule(
			List<NumberedRule> rules,
			FunctionSymbol times,
			Term zero) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, times) && left.get(0).deepEquals(zero) &&
					left.get(1) instanceof Variable &&
					rule.getRight().deepEquals(zero))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code times(s(x),y) -> plus(y,times(x,y))}. */
	private static TimesShape findTimesRule(
			List<NumberedRule> rules,
			FunctionSymbol times,
			FunctionSymbol successor) {

		for (NumberedRule numberedRule : rules) {
			TimesShape shape = timesRuleShape(numberedRule, times, successor);
			if (shape != null)
				return shape;
		}
		return null;
	}

	/** Extracts {@code times(s(x),y) -> plus(y,times(x,y))}. */
	private static TimesShape timesRuleShape(
			NumberedRule numberedRule,
			FunctionSymbol times,
			FunctionSymbol successor) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, times) || !hasRoot(left.get(0), successor) ||
				!(left.get(0).get(0) instanceof Variable x) ||
				!(left.get(1) instanceof Variable y) || x.deepEquals(y))
			return null;

		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 2 ||
				!right.get(0).deepEquals(y))
			return null;

		Term recursiveCall = right.get(1);
		return hasRoot(recursiveCall, times) &&
				recursiveCall.get(0).deepEquals(x) &&
				recursiveCall.get(1).deepEquals(y) ?
				new TimesShape(numberedRule, right.getRootSymbol()) : null;
	}

	/** Finds {@code plus(0,y) -> y}. */
	private static NumberedRule findPlusBaseRule(
			List<NumberedRule> rules,
			FunctionSymbol plus,
			Term zero) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, plus) && left.get(0).deepEquals(zero) &&
					left.get(1) instanceof Variable y &&
					rule.getRight().deepEquals(y))
				return numberedRule;
		}
		return null;
	}

	/** Finds either standard recursive presentation of unary addition. */
	private static AdditionShape findAdditionRule(
			List<NumberedRule> rules,
			FunctionSymbol plus,
			FunctionSymbol successor) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, plus) || !hasRoot(left.get(0), successor) ||
					!(left.get(0).get(0) instanceof Variable x) ||
					!(left.get(1) instanceof Variable y) || x.deepEquals(y))
				continue;
			Term right = rule.getRight();
			if (isAccumulatingAddition(right, plus, successor, x, y))
				return new AdditionShape(numberedRule, AdditionKind.ACCUMULATING);
			if (isConstructorAddition(right, plus, successor, x, y))
				return new AdditionShape(numberedRule, AdditionKind.CONSTRUCTOR);
		}
		return null;
	}

	/** Tests {@code plus(x,s(y))}. */
	private static boolean isAccumulatingAddition(
			Term right,
			FunctionSymbol plus,
			FunctionSymbol successor,
			Variable x,
			Variable y) {

		return hasRoot(right, plus) && right.get(0).deepEquals(x) &&
				hasRoot(right.get(1), successor) &&
				right.get(1).get(0).deepEquals(y);
	}

	/** Tests {@code s(plus(x,y))}. */
	private static boolean isConstructorAddition(
			Term right,
			FunctionSymbol plus,
			FunctionSymbol successor,
			Variable x,
			Variable y) {

		return hasRoot(right, successor) && hasRoot(right.get(0), plus) &&
				right.get(0).get(0).deepEquals(x) &&
				right.get(0).get(1).deepEquals(y);
	}

	/** Extracts {@code f(x,s(y)) -> f(d(x),y)}. */
	private static FirstRuleShape firstRuleShape(NumberedRule numberedRule) {
		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 2 || !(left.get(0) instanceof Variable x))
			return null;

		Term successorOfY = left.get(1);
		if (successorOfY.isVariable() ||
				successorOfY.getRootSymbol().getArity() != 1 ||
				!(successorOfY.get(0) instanceof Variable y) || x.deepEquals(y))
			return null;
		FunctionSymbol successor = successorOfY.getRootSymbol();

		Term right = rule.getRight();
		if (!hasRoot(right, state) ||
				!right.get(1).deepEquals(y) || right.get(0).isVariable() ||
				right.get(0).getRootSymbol().getArity() != 1 ||
				!right.get(0).get(0).deepEquals(x))
			return null;

		return new FirstRuleShape(
				state, successor, right.get(0).getRootSymbol());
	}

	/** Extracts {@code f(x,0) -> f(s(0),x)} for fixed {@code f} and {@code s}. */
	private static SecondRuleShape secondRuleShape(
			NumberedRule numberedRule,
			FirstRuleShape first) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, first.state()) ||
				!(left.get(0) instanceof Variable x) || isNotConstant(left.get(1)))
			return null;
		Term zero = left.get(1);

		Term right = rule.getRight();
		if (!hasRoot(right, first.state()) ||
				!hasRoot(right.get(0), first.successor()) ||
				!right.get(0).get(0).deepEquals(zero) ||
				!right.get(1).deepEquals(x))
			return null;
		return new SecondRuleShape(zero);
	}

	/** Finds {@code d(0) -> 0}. */
	private static NumberedRule findZeroRule(
			List<NumberedRule> rules,
			FirstRuleShape first,
			SecondRuleShape second) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, first.doubling()) &&
					left.get(0).deepEquals(second.zero()) &&
					rule.getRight().deepEquals(second.zero()))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code d(s(x)) -> s(s(d(x)))}. */
	private static NumberedRule findDoublingRule(
			List<NumberedRule> rules,
			FirstRuleShape first) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, first.doubling()) ||
					!hasRoot(left.get(0), first.successor()) ||
					!(left.get(0).get(0) instanceof Variable x))
				continue;

			Term right = rule.getRight();
			if (hasRoot(right, first.successor()) &&
					hasRoot(right.get(0), first.successor()) &&
					hasRoot(right.get(0).get(0), first.doubling()) &&
					right.get(0).get(0).get(0).deepEquals(x))
				return numberedRule;
		}
		return null;
	}

	/** Builds and replays the concrete phase from counter two to counter four. */
	private static CounterGrowthWitness buildWitness(CounterSchema schema) {
		Term one = successor(schema.zero(), schema.successor());
		Term two = successor(one, schema.successor());
		Term four = successor(successor(two, schema.successor()),
				schema.successor());
		Term start = state(one, two, schema.state());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = start;

		current = addStep(steps, current, schema.firstRule(), position());
		current = addStep(steps, current, schema.doublingRule(), position(0));
		current = addStep(steps, current, schema.zeroRule(), position(0, 0, 0));
		current = addStep(steps, current, schema.firstRule(), position());
		current = addStep(steps, current, schema.doublingRule(), position(0));
		current = addStep(
				steps, current, schema.doublingRule(), position(0, 0, 0));
		current = addStep(
				steps, current, schema.zeroRule(), position(0, 0, 0, 0, 0));
		current = addStep(steps, current, schema.secondRule(), position());

		Term expected = state(one, four, schema.state());
		return current != null && current.deepEquals(expected) ?
				new CounterGrowthWitness(schema, start, current, List.copyOf(steps)) :
				null;
	}

	/** Builds and replays the arithmetic phase {@code (2,1) -> (4,2)}. */
	private static ArithmeticGrowthWitness buildArithmeticWitness(
			ArithmeticSchema schema) {

		Term one = successor(schema.zero(), schema.successor());
		Term two = successor(one, schema.successor());
		Term four = successor(successor(two, schema.successor()),
				schema.successor());
		Term start = arithmeticState(
				schema.truth(), two, one, schema.state());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = start;

		current = addStep(steps, current, schema.growthRule(), position());
		current = addStep(
				steps, current, schema.comparisonRule(), position(0));
		current = addStep(steps, current, schema.positiveRule(), position(0));
		current = addStep(steps, current, schema.doubleRule(), position(1));
		current = addStep(steps, current, schema.timesRule(), position(1));
		current = addStep(steps, current, schema.timesRule(), position(1, 1));
		current = addStep(
				steps, current, schema.timesBaseRule(), position(1, 1, 1));
		current = addTwo(steps, current, schema, position(1, 1));
		current = addTwo(steps, current, schema, position(1));

		Term expected = arithmeticState(
				schema.truth(), four, two, schema.state());
		return current != null && current.deepEquals(expected) ?
				new ArithmeticGrowthWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Replays {@code plus(2,q) ->* s(s(q))} at the given position. */
	private static Term addTwo(
			List<RewriteStep> steps,
			Term source,
			ArithmeticSchema schema,
			Position additionPosition) {

		Term current = source;
		Position recursivePosition = additionPosition;
		for (int i = 0; i < 2; i++) {
			current = addStep(
					steps, current, schema.plusRule(), recursivePosition);
			if (schema.additionKind() == AdditionKind.CONSTRUCTOR)
				recursivePosition = recursivePosition.addLast(0);
		}
		return addStep(
				steps, current, schema.plusBaseRule(), recursivePosition);
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

	/** Returns whether the term has the specified function symbol at its root. */
	private static boolean hasRoot(Term term, FunctionSymbol root) {
		return !term.isVariable() && term.getRootSymbol() == root;
	}

	/** Returns whether the term is not a constant. */
	private static boolean isNotConstant(Term term) {
		return term.isVariable() || term.getRootSymbol().getArity() != 0;
	}

	/** Builds one successor term. */
	private static Term successor(Term argument, FunctionSymbol successor) {
		return new Function(successor, List.of(argument));
	}

	/** Builds one state term. */
	private static Term state(Term first, Term second, FunctionSymbol state) {
		return new Function(state, List.of(first, second));
	}

	/** Builds one ternary arithmetic state term. */
	private static Term arithmeticState(
			Term guard,
			Term first,
			Term second,
			FunctionSymbol state) {

		return new Function(state, List.of(guard, first, second));
	}

	/** Builds a position from its successive child indexes. */
	private static Position position(int... indexes) {
		Position position = new Position();
		for (int index : indexes)
			position = position.addLast(index);
		return position;
	}

	/** Formats a replayed derivation. */
	private static String formatDetails(
			List<RewriteStep> steps,
			int indentation) {

		String spaces = " ".repeat(Math.max(0, indentation));
		StringBuilder details = new StringBuilder();
		int stepNumber = 1;
		for (RewriteStep step : steps) {
			details.append(spaces).append(stepNumber++).append(". ")
					.append(step.source()).append(" -> ").append(step.target())
					.append(" (rule ").append(step.ruleNumber())
					.append(", position ").append(step.position()).append(")\n");
		}
		if (!details.isEmpty())
			details.setLength(details.length() - 1);
		return details.toString();
	}

	/** One input rule together with its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Symbols extracted from the counter-decrement rule. */
	private record FirstRuleShape(
			FunctionSymbol state,
			FunctionSymbol successor,
			FunctionSymbol doubling) {}

	/** Constant extracted from the counter-reset rule. */
	private record SecondRuleShape(Term zero) {}

	/** Symbols extracted from an arithmetic state-transition rule. */
	private record ArithmeticGrowthShape(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol comparison,
			FunctionSymbol doubling,
			FunctionSymbol successor) {}

	/** Constant extracted from the positive-comparison rule. */
	private record PositiveComparisonShape(Term zero) {}

	/** Rule and multiplication symbol extracted from the double wrapper. */
	private record DoubleShape(
			NumberedRule rule,
			FunctionSymbol times) {}

	/** Rule and addition symbol extracted from multiplication recursion. */
	private record TimesShape(
			NumberedRule rule,
			FunctionSymbol plus) {}

	/** Supported presentations of unary addition. */
	private enum AdditionKind {
		ACCUMULATING,
		CONSTRUCTOR
	}

	/** Recursive addition rule and its presentation. */
	private record AdditionShape(
			NumberedRule rule,
			AdditionKind kind) {}

	/** A complete matched rule schema. */
	private record CounterSchema(
			NumberedRule firstRule,
			NumberedRule secondRule,
			NumberedRule zeroRule,
			NumberedRule doublingRule,
			FunctionSymbol state,
			FunctionSymbol successor,
			FunctionSymbol doubling,
			Term zero) {}

	/** A complete arithmetic-counter schema. */
	private record ArithmeticSchema(
			NumberedRule growthRule,
			NumberedRule positiveRule,
			NumberedRule comparisonRule,
			NumberedRule doubleRule,
			NumberedRule timesBaseRule,
			NumberedRule timesRule,
			NumberedRule plusBaseRule,
			NumberedRule plusRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol successor,
			FunctionSymbol doubling,
			Term zero,
			AdditionKind additionKind) {}

	/** One replayed rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** The matched schema and its concrete first growth phase. */
	private record CounterGrowthWitness(
			CounterSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** The arithmetic schema and its concrete first growth phase. */
	private record ArithmeticGrowthWitness(
			ArithmeticSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** Proof argument for a certified unary-counter growth schema. */
	private record UnaryCounterGrowthArgument(
			CounterGrowthWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			return formatDetails(this.witness.steps(), indentation);
		}

		@Override
		public String getWitnessKind() {
			return WITNESS_KIND;
		}

		@Override
		public String toString() {
			CounterSchema schema = this.witness.schema();
			String state = schema.state().toString();
			String successor = schema.successor().toString();
			String doubling = schema.doubling().toString();
			String zero = schema.zero().toString();
			return TECHNIQUE_HEADER +
					"* Certificate: " + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write n-bar for " + successor + "^n(" + zero + "). " +
					"The matched rules imply " + doubling +
					"(n-bar) ->+ (2n)-bar by induction on n.\n" +
					"Consequently, for every n >= 1, " + state +
					"(1-bar,n-bar) ->+ " + state +
					"(1-bar,(2^n)-bar). Starting with n0 = 2 and setting " +
					"n(k+1) = 2^n(k) yields an infinite rewrite sequence.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + " steps to\n" +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

	/** Proof argument for arithmetic unary-counter growth. */
	private record ArithmeticCounterGrowthArgument(
			ArithmeticGrowthWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			return formatDetails(this.witness.steps(), indentation);
		}

		@Override
		public String getWitnessKind() {
			return WITNESS_KIND;
		}

		@Override
		public String toString() {
			ArithmeticSchema schema = this.witness.schema();
			String state = schema.state().toString();
			String truth = schema.truth().toString();
			String successor = schema.successor().toString();
			String doubling = schema.doubling().toString();
			String zero = schema.zero().toString();
			return TECHNIQUE_HEADER +
					"* Certificate: " + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write n-bar for " + successor + "^n(" + zero + "). " +
					"The matched addition and multiplication rules imply " +
					doubling + "(p-bar) ->+ (2p)-bar. The comparison rules " +
					"reduce positive p-bar > q-bar to " + truth + ".\n" +
					"Hence, whenever p > q, " + state + "(" + truth +
					",p-bar,q-bar) ->+ " + state + "(" + truth +
					",(2p)-bar,(q+1)-bar). Starting with (p0,q0) = (2,1) " +
					"preserves p > q because 2p > q+1, and therefore yields " +
					"an infinite rewrite sequence.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + " steps to\n" +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}
}
