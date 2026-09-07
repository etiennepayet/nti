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
 * Recognizes bounded guarded loops whose state contains a growing unary
 * counter. The supported presentations use a countdown and reset, signed
 * addition, or fixed comparisons followed by addition. In every case the
 * certificate establishes {@code W_n ->+ W_(n+1)} by induction.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechGuardedUnaryCounterGrowth implements ProofTechnique {

	/** Maximum number of rules inspected by this bounded technique. */
	private static final int MAX_RULE_COUNT = 200;

	/** Message emitted when no certified schema was found. */
	private static final String NOT_FOUND_MESSAGE =
			"No guarded unary counter growth found!";

	/** Stable name used by all proof arguments from this technique. */
	private static final String WITNESS_KIND = "guarded unary counter growth";

	/** Header shared by proof arguments produced by this technique. */
	private static final String TECHNIQUE_HEADER =
			"* Technique: bounded guarded unary-counter growth recognition\n";

	/** Prefix shared by all rendered certificates. */
	private static final String CERTIFICATE_PREFIX = "* Certificate: ";

	/** Suffix introducing the target of a replayed first phase. */
	private static final String STEPS_TO = " steps to\n";

	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose(
				"## Searching for bounded guarded unary counter growth...");
		List<NumberedRule> rules = numberRules(trs);
		Argument argument = rules == null ? null : findArgument(rules);
		if (argument == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		proof.printlnIfVerbose("Found guarded unary counter growth!");
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

	/** Finds the first replayable schema, in increasing structural complexity. */
	private static Argument findArgument(List<NumberedRule> rules) {
		CountdownSchema countdown = findCountdownSchema(rules);
		CountdownWitness countdownWitness = countdown == null ? null :
				buildCountdownWitness(countdown);
		if (countdownWitness != null)
			return new CountdownArgument(countdownWitness);

		SignedSchema signed = findSignedSchema(rules);
		SignedWitness signedWitness = signed == null ? null :
				buildSignedWitness(signed);
		if (signedWitness != null)
			return new SignedArgument(signedWitness);

		ComparisonSchema comparison = findComparisonSchema(rules);
		ComparisonWitness comparisonWitness = comparison == null ? null :
				buildComparisonWitness(comparison);
		return comparisonWitness == null ? null :
				new ComparisonArgument(comparisonWitness);
	}

	/** Finds the countdown-and-reset presentation. */
	private static CountdownSchema findCountdownSchema(
			List<NumberedRule> rules) {

		for (NumberedRule transitionRule : rules) {
			CountdownTransition transition =
					countdownTransition(transitionRule);
			if (transition == null)
				continue;
			CountdownSchema schema = completeCountdownSchema(
					rules, transitionRule, transition);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Extracts {@code w(true,x,y) -> c(gt(x,0),x,y)}. */
	private static CountdownTransition countdownTransition(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (left.getRootSymbol().getArity() != 3 ||
				isNotConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable x) ||
				!(left.get(2) instanceof Variable y) || x.deepEquals(y))
			return null;

		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 3 ||
				!right.get(1).deepEquals(x) || !right.get(2).deepEquals(y))
			return null;
		Term comparison = right.get(0);
		if (comparison.isVariable() ||
				comparison.getRootSymbol().getArity() != 2 ||
				!comparison.get(0).deepEquals(x) ||
				isNotConstant(comparison.get(1)))
			return null;

		return new CountdownTransition(
				left.getRootSymbol(), left.get(0), right.getRootSymbol(),
				comparison.getRootSymbol(), comparison.get(1));
	}

	/** Completes one countdown schema from its transition rule. */
	private static CountdownSchema completeCountdownSchema(
			List<NumberedRule> rules,
			NumberedRule transitionRule,
			CountdownTransition transition) {

		for (NumberedRule trueRule : rules) {
			CountdownTrueShape trueShape =
					countdownTrueShape(trueRule, transition);
			if (trueShape == null)
				continue;
			NumberedRule falseRule = findCountdownFalseRule(
					rules, transition, trueShape);
			NumberedRule positiveRule = findUnaryPositiveRule(
					rules, transition.comparison(), trueShape.successor(),
					transition.zero(), transition.truth());
			NumberedRule zeroRule = findCountdownZeroRule(
					rules, transition, trueShape.falseTerm());
			if (falseRule != null && positiveRule != null && zeroRule != null)
				return new CountdownSchema(
						transitionRule, trueRule, falseRule, positiveRule,
						zeroRule, transition.state(), transition.truth(),
						trueShape.falseTerm(), transition.branch(),
						transition.comparison(), trueShape.successor(),
						transition.zero());
		}
		return null;
	}

	/** Extracts {@code c(true,s(x),y) -> w(gt(y,0),x,y)}. */
	private static CountdownTrueShape countdownTrueShape(
			NumberedRule numberedRule,
			CountdownTransition transition) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, transition.branch()) ||
				!left.get(0).deepEquals(transition.truth()) ||
				left.get(1).isVariable() ||
				left.get(1).getRootSymbol().getArity() != 1 ||
				!(left.get(1).get(0) instanceof Variable x) ||
				!(left.get(2) instanceof Variable y) || x.deepEquals(y))
			return null;

		Term right = rule.getRight();
		if (!hasRoot(right, transition.state()) ||
				!right.get(1).deepEquals(x) || !right.get(2).deepEquals(y))
			return null;
		Term comparison = right.get(0);
		if (!hasRoot(comparison, transition.comparison()) ||
				!comparison.get(0).deepEquals(y) ||
				!comparison.get(1).deepEquals(transition.zero()))
			return null;

		return new CountdownTrueShape(left.get(1).getRootSymbol());
	}

	/** Finds and extracts the false branch, completing its false constant. */
	private static NumberedRule findCountdownFalseRule(
			List<NumberedRule> rules,
			CountdownTransition transition,
			CountdownTrueShape trueShape) {

		for (NumberedRule numberedRule : rules) {
			Term falseTerm = countdownFalseTerm(
					numberedRule, transition, trueShape.successor());
			if (falseTerm != null) {
				trueShape.setFalseTerm(falseTerm);
				return numberedRule;
			}
		}
		return null;
	}

	/** Extracts the false constant from one candidate reset rule. */
	private static Term countdownFalseTerm(
			NumberedRule numberedRule,
			CountdownTransition transition,
			FunctionSymbol successor) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, transition.branch()) ||
				isNotConstant(left.get(0)) ||
				left.get(0).deepEquals(transition.truth()) ||
				!(left.get(1) instanceof Variable x) ||
				!(left.get(2) instanceof Variable y) || x.deepEquals(y))
			return null;
		Term successorOfY = unary(y, successor);
		Term right = rule.getRight();
		if (!hasRoot(right, transition.state()) ||
				!right.get(1).deepEquals(successorOfY) ||
				!right.get(2).deepEquals(successorOfY))
			return null;
		Term comparison = right.get(0);
		return hasRoot(comparison, transition.comparison()) &&
				comparison.get(0).deepEquals(successorOfY) &&
				comparison.get(1).deepEquals(transition.zero()) ?
				left.get(0) : null;
	}

	/** Finds {@code gt(0,x) -> false}. */
	private static NumberedRule findCountdownZeroRule(
			List<NumberedRule> rules,
			CountdownTransition transition,
			Term falseTerm) {

		if (falseTerm == null)
			return null;
		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, transition.comparison()) &&
					left.get(0).deepEquals(transition.zero()) &&
					left.get(1) instanceof Variable &&
					rule.getRight().deepEquals(falseTerm))
				return numberedRule;
		}
		return null;
	}

	/** Finds the signed-addition presentation. */
	private static SignedSchema findSignedSchema(List<NumberedRule> rules) {
		for (NumberedRule transitionRule : rules) {
			SignedTransition transition = signedTransition(transitionRule);
			if (transition == null)
				continue;
			SignedSchema schema = completeSignedSchema(
					rules, transitionRule, transition);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Extracts the guarded signed state transition. */
	private static SignedTransition signedTransition(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (left.getRootSymbol().getArity() != 3 ||
				isNotConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable x) ||
				!(left.get(2) instanceof Variable y) || x.deepEquals(y))
			return null;
		Term right = rule.getRight();
		if (!hasRoot(right, left.getRootSymbol()) ||
				!right.get(2).deepEquals(y))
			return null;

		Term conjunction = right.get(0);
		Term difference = right.get(1);
		if (conjunction.isVariable() ||
				conjunction.getRootSymbol().getArity() != 2 ||
				difference.isVariable() ||
				difference.getRootSymbol().getArity() != 2 ||
				!difference.get(0).deepEquals(x) ||
				!difference.get(1).deepEquals(y))
			return null;
		Term nonZero = conjunction.get(0);
		Term positive = conjunction.get(1);
		if (nonZero.isVariable() || nonZero.getRootSymbol().getArity() != 1 ||
				!nonZero.get(0).deepEquals(y) || positive.isVariable() ||
				positive.getRootSymbol().getArity() != 1 ||
				!positive.get(0).deepEquals(x))
			return null;

		return new SignedTransition(
				left.getRootSymbol(), left.get(0),
				conjunction.getRootSymbol(), nonZero.getRootSymbol(),
				positive.getRootSymbol(), difference.getRootSymbol());
	}

	/** Completes one signed-addition schema. */
	private static SignedSchema completeSignedSchema(
			List<NumberedRule> rules,
			NumberedRule transitionRule,
			SignedTransition transition) {

		for (NumberedRule differenceRule : rules) {
			SignedSchema schema = completeSignedSchema(
					rules, transitionRule, transition, differenceRule);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Completes a signed schema from one candidate difference rule. */
	private static SignedSchema completeSignedSchema(
			List<NumberedRule> rules,
			NumberedRule transitionRule,
			SignedTransition transition,
			NumberedRule differenceRule) {

		SignedDifference difference = signedDifference(differenceRule, transition);
		if (difference == null)
			return null;
		AdditionRules addition = findAdditionRules(rules, difference.addition());
		if (addition == null)
			return null;
		NumberedRule nonZeroRule = findWrappedPositiveRule(
				rules, transition.nonZero(), difference.negative(),
				addition.successor(), transition.truth());
		NumberedRule positiveRule = findWrappedPositiveRule(
				rules, transition.positive(), difference.positive(),
				addition.successor(), transition.truth());
		NumberedRule conjunctionRule = findBinaryConstantRule(
				rules, transition.conjunction(), transition.truth(),
				transition.truth(), transition.truth());
		return nonZeroRule != null && positiveRule != null &&
				conjunctionRule != null ? new SignedSchema(
						transitionRule, nonZeroRule, positiveRule,
						conjunctionRule, differenceRule, addition.baseRule(),
						addition.recursiveRule(), transition.state(),
						transition.truth(), difference.positive(),
						difference.negative(), addition.successor(),
						addition.zero(), difference.addition(), addition.kind()) :
				null;
	}

	/** Extracts {@code minus(pos(x),neg(y)) -> pos(add(x,y))}. */
	private static SignedDifference signedDifference(
			NumberedRule numberedRule,
			SignedTransition transition) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, transition.difference()) ||
				left.get(0).isVariable() || left.get(1).isVariable() ||
				left.get(0).getRootSymbol().getArity() != 1 ||
				left.get(1).getRootSymbol().getArity() != 1 ||
				!(left.get(0).get(0) instanceof Variable x) ||
				!(left.get(1).get(0) instanceof Variable y) || x.deepEquals(y))
			return null;
		Term right = rule.getRight();
		if (!hasRoot(right, left.get(0).getRootSymbol()))
			return null;
		Term addition = right.get(0);
		if (addition.isVariable() || addition.getRootSymbol().getArity() != 2 ||
				!addition.get(0).deepEquals(x) ||
				!addition.get(1).deepEquals(y))
			return null;

		return new SignedDifference(
				left.get(0).getRootSymbol(), left.get(1).getRootSymbol(),
				addition.getRootSymbol());
	}

	/** Finds the fixed-comparison-and-addition presentation. */
	private static ComparisonSchema findComparisonSchema(
			List<NumberedRule> rules) {

		for (NumberedRule transitionRule : rules) {
			ComparisonTransition transition =
					comparisonTransition(transitionRule);
			if (transition == null)
				continue;
			ComparisonSchema schema = completeComparisonSchema(
					rules, transitionRule, transition);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Extracts {@code w(true,s^k(x)) -> w(gt(s^k(x),q),f(s^k(x)))}. */
	private static ComparisonTransition comparisonTransition(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (left.getRootSymbol().getArity() != 2 ||
				isNotConstant(left.get(0)))
			return null;
		UnaryVariable counter = unaryVariable(left.get(1));
		if (counter == null || counter.depth() == 0)
			return null;
		Term right = rule.getRight();
		if (!hasRoot(right, left.getRootSymbol()))
			return null;
		Term comparison = right.get(0);
		Term wrapper = right.get(1);
		if (comparison.isVariable() ||
				comparison.getRootSymbol().getArity() != 2 ||
				!comparison.get(0).deepEquals(left.get(1)) ||
				wrapper.isVariable() || wrapper.getRootSymbol().getArity() != 1 ||
				!wrapper.get(0).deepEquals(left.get(1)))
			return null;
		UnaryNumeral threshold = unaryNumeral(
				comparison.get(1), counter.successor());
		if (threshold == null || counter.depth() <= threshold.depth())
			return null;

		return new ComparisonTransition(
				left.getRootSymbol(), left.get(0), counter.successor(),
				counter.depth(), threshold.zero(), threshold.depth(),
				comparison.getRootSymbol(), wrapper.getRootSymbol());
	}

	/** Completes one comparison-and-addition schema. */
	private static ComparisonSchema completeComparisonSchema(
			List<NumberedRule> rules,
			NumberedRule transitionRule,
			ComparisonTransition transition) {

		NumberedRule comparisonRecursive = findComparisonRecursiveRule(
				rules, transition.comparison(), transition.successor());
		NumberedRule comparisonPositive = findUnaryPositiveRule(
				rules, transition.comparison(), transition.successor(),
				transition.zero(), transition.truth());
		if (comparisonRecursive == null || comparisonPositive == null)
			return null;

		for (NumberedRule wrapperRule : rules) {
			ComparisonSchema schema = completeComparisonSchema(
					rules, transitionRule, transition, comparisonRecursive,
					comparisonPositive, wrapperRule);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Completes a comparison schema from one candidate wrapper rule. */
	private static ComparisonSchema completeComparisonSchema(
			List<NumberedRule> rules,
			NumberedRule transitionRule,
			ComparisonTransition transition,
			NumberedRule comparisonRecursive,
			NumberedRule comparisonPositive,
			NumberedRule wrapperRule) {

		WrapperShape wrapper = wrapperShape(wrapperRule, transition);
		if (wrapper == null ||
				wrapper.forbiddenDepth() >= transition.startDepth())
			return null;
		NumberedRule inequalityRecursive = findComparisonRecursiveRule(
				rules, wrapper.inequality(), transition.successor());
		NumberedRule inequalityPositive = findUnaryPositiveRule(
				rules, wrapper.inequality(), transition.successor(),
				transition.zero(), transition.truth());
		ConditionalAddition conditional = findConditionalAddition(
				rules, wrapper.conditional(), transition.truth(),
				transition.successor(), transition.zero());
		if (inequalityRecursive == null || inequalityPositive == null ||
				conditional == null)
			return null;
		AdditionRules addition = findAdditionRules(
				rules, conditional.addition(), transition.successor());
		return addition != null &&
				addition.zero().deepEquals(transition.zero()) ?
				new ComparisonSchema(
						transitionRule, comparisonRecursive, comparisonPositive,
						wrapperRule, inequalityRecursive, inequalityPositive,
						conditional.rule(), addition.baseRule(),
						addition.recursiveRule(), transition.state(),
						transition.truth(), transition.successor(),
						transition.zero(), transition.startDepth(),
						transition.thresholdDepth(), wrapper.forbiddenDepth(),
						addition.kind()) : null;
	}

	/** Extracts {@code f(x) -> if(neq(x,r),x)}. */
	private static WrapperShape wrapperShape(
			NumberedRule numberedRule,
			ComparisonTransition transition) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, transition.wrapper()) ||
				!(left.get(0) instanceof Variable x))
			return null;
		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 2 ||
				!right.get(1).deepEquals(x))
			return null;
		Term inequality = right.get(0);
		if (inequality.isVariable() ||
				inequality.getRootSymbol().getArity() != 2 ||
				!inequality.get(0).deepEquals(x))
			return null;
		UnaryNumeral forbidden = unaryNumeral(
				inequality.get(1), transition.successor());
		return forbidden != null &&
				forbidden.zero().deepEquals(transition.zero()) ?
				new WrapperShape(right.getRootSymbol(),
						inequality.getRootSymbol(), forbidden.depth()) : null;
	}

	/** Finds {@code if(true,x) -> add(x,s(0))}. */
	private static ConditionalAddition findConditionalAddition(
			List<NumberedRule> rules,
			FunctionSymbol conditional,
			Term truth,
			FunctionSymbol successor,
			Term zero) {

		Term one = unary(zero, successor);
		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, conditional) || !left.get(0).deepEquals(truth) ||
					!(left.get(1) instanceof Variable x))
				continue;
			Term right = rule.getRight();
			if (!right.isVariable() && right.getRootSymbol().getArity() == 2 &&
					right.get(0).deepEquals(x) && right.get(1).deepEquals(one))
				return new ConditionalAddition(
						numberedRule, right.getRootSymbol());
		}
		return null;
	}

	/** Finds a positive unary comparison rule. */
	private static NumberedRule findUnaryPositiveRule(
			List<NumberedRule> rules,
			FunctionSymbol comparison,
			FunctionSymbol successor,
			Term zero,
			Term truth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, comparison) &&
					hasRoot(left.get(0), successor) &&
					left.get(0).get(0) instanceof Variable &&
					left.get(1).deepEquals(zero) &&
					rule.getRight().deepEquals(truth))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code p(s(x),s(y)) -> p(x,y)}. */
	private static NumberedRule findComparisonRecursiveRule(
			List<NumberedRule> rules,
			FunctionSymbol comparison,
			FunctionSymbol successor) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, comparison) ||
					!hasRoot(left.get(0), successor) ||
					!hasRoot(left.get(1), successor) ||
					!(left.get(0).get(0) instanceof Variable x) ||
					!(left.get(1).get(0) instanceof Variable y) || x.deepEquals(y))
				continue;
			Term right = rule.getRight();
			if (hasRoot(right, comparison) && right.get(0).deepEquals(x) &&
					right.get(1).deepEquals(y))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code p(w(s(x))) -> true}. */
	private static NumberedRule findWrappedPositiveRule(
			List<NumberedRule> rules,
			FunctionSymbol predicate,
			FunctionSymbol wrapper,
			FunctionSymbol successor,
			Term truth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, predicate) && hasRoot(left.get(0), wrapper) &&
					hasRoot(left.get(0).get(0), successor) &&
					left.get(0).get(0).get(0) instanceof Variable &&
					rule.getRight().deepEquals(truth))
				return numberedRule;
		}
		return null;
	}

	/** Finds a binary ground rule with fixed constant arguments and result. */
	private static NumberedRule findBinaryConstantRule(
			List<NumberedRule> rules,
			FunctionSymbol root,
			Term first,
			Term second,
			Term result) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, root) && left.get(0).deepEquals(first) &&
					left.get(1).deepEquals(second) &&
					rule.getRight().deepEquals(result))
				return numberedRule;
		}
		return null;
	}

	/** Finds base and recursive rules for unary addition. */
	private static AdditionRules findAdditionRules(
			List<NumberedRule> rules,
			FunctionSymbol addition,
			FunctionSymbol successor) {

		for (NumberedRule baseRule : rules) {
			RuleTrs base = baseRule.rule();
			Function left = base.getLeft();
			if (!hasRoot(left, addition) || isNotConstant(left.get(0)) ||
					!(left.get(1) instanceof Variable y) ||
					!base.getRight().deepEquals(y))
				continue;
			for (NumberedRule recursiveRule : rules) {
				AdditionKind kind = additionKind(
						recursiveRule, addition, successor);
				if (kind != null)
					return new AdditionRules(
							baseRule, recursiveRule, left.get(0), successor,
							kind);
			}
		}
		return null;
	}

	/** Finds unary addition and extracts its constructor. */
	private static AdditionRules findAdditionRules(
			List<NumberedRule> rules,
			FunctionSymbol addition) {

		for (NumberedRule numberedRule : rules) {
			Function left = numberedRule.rule().getLeft();
			if (hasRoot(left, addition) && !left.get(0).isVariable() &&
					left.get(0).getRootSymbol().getArity() == 1) {
				AdditionRules additionRules = findAdditionRules(
						rules, addition, left.get(0).getRootSymbol());
				if (additionRules != null)
					return additionRules;
			}
		}
		return null;
	}

	/** Classifies {@code add(s(x),y)} recursion. */
	private static AdditionKind additionKind(
			NumberedRule numberedRule,
			FunctionSymbol addition,
			FunctionSymbol successor) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, addition) || !hasRoot(left.get(0), successor) ||
				!(left.get(0).get(0) instanceof Variable x) ||
				!(left.get(1) instanceof Variable y) || x.deepEquals(y))
			return null;
		Term right = rule.getRight();
		if (hasRoot(right, addition) && right.get(0).deepEquals(x) &&
				hasRoot(right.get(1), successor) &&
				right.get(1).get(0).deepEquals(y))
			return AdditionKind.ACCUMULATING;
		if (hasRoot(right, successor) && hasRoot(right.get(0), addition) &&
				right.get(0).get(0).deepEquals(x) &&
				right.get(0).get(1).deepEquals(y))
			return AdditionKind.CONSTRUCTOR;
		return null;
	}

	/** Builds and replays the phase {@code W_1 ->+ W_2}. */
	private static CountdownWitness buildCountdownWitness(
			CountdownSchema schema) {

		Term one = unary(schema.zero(), schema.successor());
		Term two = unary(one, schema.successor());
		Term start = ternaryState(
				schema.truth(), one, one, schema.state());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = start;
		current = addStep(steps, current, schema.transitionRule(), position());
		current = addStep(steps, current, schema.positiveRule(), position(0));
		current = addStep(steps, current, schema.trueRule(), position());
		current = addStep(steps, current, schema.positiveRule(), position(0));
		current = addStep(steps, current, schema.transitionRule(), position());
		current = addStep(steps, current, schema.zeroRule(), position(0));
		current = addStep(steps, current, schema.falseRule(), position());
		current = addStep(steps, current, schema.positiveRule(), position(0));
		Term expected = ternaryState(
				schema.truth(), two, two, schema.state());
		return current != null && current.deepEquals(expected) ?
				new CountdownWitness(schema, start, current, List.copyOf(steps)) :
				null;
	}

	/** Builds and replays the phase {@code W_1 ->+ W_2}. */
	private static SignedWitness buildSignedWitness(SignedSchema schema) {
		Term one = unary(schema.zero(), schema.successor());
		Term two = unary(one, schema.successor());
		Term negativeOne = unary(one, schema.negative());
		Term start = ternaryState(
				schema.truth(), unary(one, schema.positive()), negativeOne,
				schema.state());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = start;
		current = addStep(steps, current, schema.transitionRule(), position());
		current = addStep(steps, current, schema.nonZeroRule(), position(0, 0));
		current = addStep(steps, current, schema.positiveRule(), position(0, 1));
		current = addStep(steps, current, schema.conjunctionRule(), position(0));
		current = addStep(steps, current, schema.differenceRule(), position(1));
		current = addAdditionStep(
				steps, current, schema.additionRule(), schema.additionKind(),
				position(1, 0));
		Position basePosition = schema.additionKind() == AdditionKind.CONSTRUCTOR ?
				position(1, 0, 0) : position(1, 0);
		current = addStep(steps, current, schema.additionBaseRule(), basePosition);
		Term expected = ternaryState(
				schema.truth(), unary(two, schema.positive()), negativeOne,
				schema.state());
		return current != null && current.deepEquals(expected) ?
				new SignedWitness(schema, start, current, List.copyOf(steps)) : null;
	}

	/** Builds and replays the phase {@code W_k ->+ W_(k+1)}. */
	private static ComparisonWitness buildComparisonWitness(
			ComparisonSchema schema) {

		Term counter = numeral(
				schema.startDepth(), schema.zero(), schema.successor());
		Term nextCounter = unary(counter, schema.successor());
		Term start = binaryState(
				schema.truth(), counter, schema.state());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = start;
		current = addStep(steps, current, schema.transitionRule(), position());
		current = addRepeatedComparison(
				steps, current, schema.comparisonRecursiveRule(),
				schema.thresholdDepth(), position(0));
		current = addStep(
				steps, current, schema.comparisonPositiveRule(), position(0));
		current = addStep(steps, current, schema.wrapperRule(), position(1));
		current = addRepeatedComparison(
				steps, current, schema.inequalityRecursiveRule(),
				schema.forbiddenDepth(), position(1, 0));
		current = addStep(
				steps, current, schema.inequalityPositiveRule(), position(1, 0));
		current = addStep(steps, current, schema.conditionalRule(), position(1));
		current = addRepeatedAddition(
				steps, current, schema.additionRule(), schema.additionKind(),
				schema.startDepth(), position(1));
		Position basePosition = additionBasePosition(
				position(1), schema.additionKind(), schema.startDepth());
		current = addStep(
				steps, current, schema.additionBaseRule(), basePosition);
		Term expected = binaryState(
				schema.truth(), nextCounter, schema.state());
		return current != null && current.deepEquals(expected) ?
				new ComparisonWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Applies one recursive comparison rule repeatedly at a fixed position. */
	private static Term addRepeatedComparison(
			List<RewriteStep> steps,
			Term source,
			NumberedRule rule,
			int repetitions,
			Position position) {

		Term current = source;
		for (int i = 0; i < repetitions; i++)
			current = addStep(steps, current, rule, position);
		return current;
	}

	/** Applies unary-addition recursion repeatedly. */
	private static Term addRepeatedAddition(
			List<RewriteStep> steps,
			Term source,
			NumberedRule rule,
			AdditionKind kind,
			int repetitions,
			Position position) {

		Term current = source;
		Position recursivePosition = position;
		for (int i = 0; i < repetitions; i++) {
			current = addStep(steps, current, rule, recursivePosition);
			if (kind == AdditionKind.CONSTRUCTOR)
				recursivePosition = recursivePosition.addLast(0);
		}
		return current;
	}

	/** Applies one unary-addition recursive step. */
	private static Term addAdditionStep(
			List<RewriteStep> steps,
			Term source,
			NumberedRule rule,
			AdditionKind kind,
			Position position) {

		return addRepeatedAddition(steps, source, rule, kind, 1, position);
	}

	/** Computes the final base-call position of an addition derivation. */
	private static Position additionBasePosition(
			Position position,
			AdditionKind kind,
			int recursiveSteps) {

		Position result = position;
		if (kind == AdditionKind.CONSTRUCTOR)
			for (int i = 0; i < recursiveSteps; i++)
				result = result.addLast(0);
		return result;
	}

	/** Applies and records one required rewrite step. */
	private static Term addStep(
			List<RewriteStep> steps,
			Term source,
			NumberedRule numberedRule,
			Position position) {

		if (source == null || numberedRule == null)
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

	/** Returns a variable-ended unary chain with one repeated constructor. */
	private static UnaryVariable unaryVariable(Term term) {
		if (term.isVariable())
			return new UnaryVariable(null, 0);
		FunctionSymbol successor = term.getRootSymbol();
		if (successor.getArity() != 1)
			return null;
		int depth = 0;
		Term current = term;
		while (hasRoot(current, successor)) {
			depth++;
			current = current.get(0);
		}
		return current instanceof Variable ?
				new UnaryVariable(successor, depth) : null;
	}

	/** Returns a constant-ended numeral over the specified constructor. */
	private static UnaryNumeral unaryNumeral(
			Term term,
			FunctionSymbol successor) {

		int depth = 0;
		Term current = term;
		while (hasRoot(current, successor)) {
			depth++;
			current = current.get(0);
		}
		return isConstant(current) ? new UnaryNumeral(current, depth) : null;
	}

	/** Returns whether the term has the specified root symbol. */
	private static boolean hasRoot(Term term, FunctionSymbol root) {
		return !term.isVariable() && term.getRootSymbol() == root;
	}

	/** Returns whether the term is a constant. */
	private static boolean isConstant(Term term) {
		return !term.isVariable() && term.getRootSymbol().getArity() == 0;
	}

	/** Returns whether the term is not a constant. */
	private static boolean isNotConstant(Term term) {
		return !isConstant(term);
	}

	/** Builds one unary application. */
	private static Term unary(Term argument, FunctionSymbol root) {
		return new Function(root, List.of(argument));
	}

	/** Builds a unary numeral. */
	private static Term numeral(
			int value,
			Term zero,
			FunctionSymbol successor) {

		Term result = zero;
		for (int i = 0; i < value; i++)
			result = unary(result, successor);
		return result;
	}

	/** Builds a binary state term. */
	private static Term binaryState(
			Term first,
			Term second,
			FunctionSymbol state) {

		return new Function(state, List.of(first, second));
	}

	/** Builds a ternary state term. */
	private static Term ternaryState(
			Term first,
			Term second,
			Term third,
			FunctionSymbol state) {

		return new Function(state, List.of(first, second, third));
	}

	/** Builds a position from successive child indexes. */
	private static Position position(int... indexes) {
		Position position = new Position();
		for (int index : indexes)
			position = position.addLast(index);
		return position;
	}

	/** Formats one replayed derivation. */
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

	private record NumberedRule(int number, RuleTrs rule) {}

	private record CountdownTransition(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol branch,
			FunctionSymbol comparison,
			Term zero) {}

	/** Mutable only while the false branch completes the extracted shape. */
	private static final class CountdownTrueShape {
		private final FunctionSymbol successor;
		private Term falseTerm;

		private CountdownTrueShape(FunctionSymbol successor) {
			this.successor = successor;
		}

		private FunctionSymbol successor() {
			return this.successor;
		}

		private Term falseTerm() {
			return this.falseTerm;
		}

		private void setFalseTerm(Term falseTerm) {
			this.falseTerm = falseTerm;
		}
	}

	private record CountdownSchema(
			NumberedRule transitionRule,
			NumberedRule trueRule,
			NumberedRule falseRule,
			NumberedRule positiveRule,
			NumberedRule zeroRule,
			FunctionSymbol state,
			Term truth,
			Term falseTerm,
			FunctionSymbol branch,
			FunctionSymbol comparison,
			FunctionSymbol successor,
			Term zero) {}

	private record SignedTransition(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol conjunction,
			FunctionSymbol nonZero,
			FunctionSymbol positive,
			FunctionSymbol difference) {}

	private record SignedDifference(
			FunctionSymbol positive,
			FunctionSymbol negative,
			FunctionSymbol addition) {}

	private record SignedSchema(
			NumberedRule transitionRule,
			NumberedRule nonZeroRule,
			NumberedRule positiveRule,
			NumberedRule conjunctionRule,
			NumberedRule differenceRule,
			NumberedRule additionBaseRule,
			NumberedRule additionRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol positive,
			FunctionSymbol negative,
			FunctionSymbol successor,
			Term zero,
			FunctionSymbol addition,
			AdditionKind additionKind) {}

	private record ComparisonTransition(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol successor,
			int startDepth,
			Term zero,
			int thresholdDepth,
			FunctionSymbol comparison,
			FunctionSymbol wrapper) {}

	private record WrapperShape(
			FunctionSymbol conditional,
			FunctionSymbol inequality,
			int forbiddenDepth) {}

	private record ConditionalAddition(
			NumberedRule rule,
			FunctionSymbol addition) {}

	private enum AdditionKind {
		ACCUMULATING,
		CONSTRUCTOR
	}

	private record AdditionRules(
			NumberedRule baseRule,
			NumberedRule recursiveRule,
			Term zero,
			FunctionSymbol successor,
			AdditionKind kind) {}

	private record ComparisonSchema(
			NumberedRule transitionRule,
			NumberedRule comparisonRecursiveRule,
			NumberedRule comparisonPositiveRule,
			NumberedRule wrapperRule,
			NumberedRule inequalityRecursiveRule,
			NumberedRule inequalityPositiveRule,
			NumberedRule conditionalRule,
			NumberedRule additionBaseRule,
			NumberedRule additionRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol successor,
			Term zero,
			int startDepth,
			int thresholdDepth,
			int forbiddenDepth,
			AdditionKind additionKind) {}

	private record UnaryVariable(FunctionSymbol successor, int depth) {}

	private record UnaryNumeral(Term zero, int depth) {}

	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	private record CountdownWitness(
			CountdownSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	private record SignedWitness(
			SignedSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	private record ComparisonWitness(
			ComparisonSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	private record CountdownArgument(
			CountdownWitness witness) implements Argument {

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
			CountdownSchema schema = this.witness.schema();
			return TECHNIQUE_HEADER + CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write n-bar for " + schema.successor() + "^n(" +
					schema.zero() + ") and Wn for " + schema.state() + "(" +
					schema.truth() + ",n-bar,n-bar). The true branch decrements " +
					"the first counter to zero while preserving the second; the " +
					"false branch then resets both counters to (n+1)-bar. Hence " +
					"Wn ->+ W(n+1) for every n >= 1.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

	private record SignedArgument(
			SignedWitness witness) implements Argument {

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
			SignedSchema schema = this.witness.schema();
			return TECHNIQUE_HEADER + CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write n-bar for " + schema.successor() + "^n(" +
					schema.zero() + "). Unary addition gives " +
					schema.addition() + "(n-bar,1-bar) " +
					"->+ (n+1)-bar. The matched guards remain true for the " +
					"positive counter and the fixed negative one, so Wn ->+ " +
					"W(n+1) for every n >= 1.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

	private record ComparisonArgument(
			ComparisonWitness witness) implements Argument {

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
			ComparisonSchema schema = this.witness.schema();
			return TECHNIQUE_HEADER + CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write n-bar for " + schema.successor() + "^n(" +
					schema.zero() + "). For n >= " + schema.startDepth() +
					", the fixed comparison and inequality guards reduce to " +
					schema.truth() + ", while unary addition maps n-bar to " +
					"(n+1)-bar. Thus Wn ->+ W(n+1).\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}
}
