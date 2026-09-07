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
 * Recognizes bounded non-looping schemas in which a total evaluator guards a
 * constructor-growing state transition. The supported presentations grow a
 * guarded natural list, guard a unary successor through a generated list, or
 * grow two unary counters through predicates and doubling.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechGuardedEvaluatorGrowth implements ProofTechnique {

	/** Maximum number of rules inspected by this bounded technique. */
	private static final int MAX_RULE_COUNT = 200;

	/** Stable kind shared by all arguments produced here. */
	private static final String WITNESS_KIND = "guarded evaluator growth";

	/** Heading shared by all rendered arguments. */
	private static final String TECHNIQUE_HEADER =
			"* Technique: bounded guarded evaluator-growth recognition\n";

	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose(
				"## Searching for bounded guarded evaluator growth...");
		List<NumberedRule> rules = numberRules(trs);
		Argument argument = rules == null ? null : findArgument(rules);
		if (argument == null) {
			proof.printlnIfVerbose("No guarded evaluator growth found!");
			return proof;
		}

		proof.printlnIfVerbose("Found guarded evaluator growth!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(argument);
		return proof;
	}

	/** Numbers the input rules if the inspection bound is respected. */
	private static List<NumberedRule> numberRules(Trs trs) {
		List<NumberedRule> rules = new ArrayList<>();
		int number = 1;
		for (RuleTrs rule : trs) {
			if (rules.size() >= MAX_RULE_COUNT)
				return null;
			rules.add(new NumberedRule(number++, rule));
		}
		return rules;
	}

	/** Finds the first complete schema in increasing structural complexity. */
	private static Argument findArgument(List<NumberedRule> rules) {
		NaturalListWitness naturalList = findNaturalListWitness(rules);
		if (naturalList != null)
			return new NaturalListArgument(naturalList);

		GeneratedListWitness generatedList = findGeneratedListWitness(rules);
		if (generatedList != null)
			return new GeneratedListArgument(generatedList);

		UnaryDoublingWitness unaryDoubling = findUnaryDoublingWitness(rules);
		return unaryDoubling == null ? null :
				new UnaryDoublingArgument(unaryDoubling);
	}

	/** Finds the guarded natural-list presentation. */
	private static NaturalListWitness findNaturalListWitness(
			List<NumberedRule> rules) {

		for (NumberedRule producerRule : rules) {
			ProducerShape producer = naturalListProducer(producerRule);
			if (producer == null)
				continue;
			for (NumberedRule growthRule : rules) {
				NaturalListGrowthShape growth = naturalListGrowth(
						growthRule, producer);
				if (growth == null)
					continue;
				NaturalListSchema schema = completeNaturalListSchema(
						rules, producerRule, producer, growthRule, growth);
				NaturalListWitness witness = schema == null ? null :
						buildNaturalListWitness(schema);
				if (witness != null)
					return witness;
			}
		}
		return null;
	}

	/** Extracts {@code p(xs) -> b(list(xs),xs)}. */
	private static ProducerShape naturalListProducer(NumberedRule numberedRule) {
		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (left.getRootSymbol().getArity() != 1 ||
				!(left.get(0) instanceof Variable list))
			return null;
		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 2 ||
				!right.get(1).deepEquals(list))
			return null;
		Term guard = right.get(0);
		if (guard.isVariable() || guard.getRootSymbol().getArity() != 1 ||
				!guard.get(0).deepEquals(list))
			return null;
		return new ProducerShape(
				left.getRootSymbol(), right.getRootSymbol(),
				guard.getRootSymbol());
	}

	/** Extracts {@code b(tt,C(x,xs)) -> p(C(s(x),C(x,xs)))}. */
	private static NaturalListGrowthShape naturalListGrowth(
			NumberedRule numberedRule,
			ProducerShape producer) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, producer.branch()) || !isConstant(left.get(0)))
			return null;
		Term oldList = left.get(1);
		if (oldList.isVariable() ||
				oldList.getRootSymbol().getArity() != 2 ||
				!(oldList.get(0) instanceof Variable head) ||
				!(oldList.get(1) instanceof Variable tail) || head.deepEquals(tail))
			return null;

		Term right = rule.getRight();
		if (!hasRoot(right, producer.state()))
			return null;
		Term newList = right.get(0);
		if (!hasRoot(newList, oldList.getRootSymbol()))
			return null;
		Term newHead = newList.get(0);
		Term retainedList = newList.get(1);
		if (newHead.isVariable() ||
				newHead.getRootSymbol().getArity() != 1 ||
				!newHead.get(0).deepEquals(head) ||
				!retainedList.deepEquals(oldList))
			return null;
		return new NaturalListGrowthShape(
				left.get(0), oldList.getRootSymbol(),
				newHead.getRootSymbol());
	}

	/** Completes the evaluator rules for a guarded natural list. */
	private static NaturalListSchema completeNaturalListSchema(
			List<NumberedRule> rules,
			NumberedRule producerRule,
			ProducerShape producer,
			NumberedRule growthRule,
			NaturalListGrowthShape growth) {

		for (NumberedRule listBaseRule : rules) {
			Term empty = predicateBase(
					listBaseRule, producer.guard(), growth.truth());
			if (empty == null)
				continue;
			for (NumberedRule listRule : rules) {
				NaturalListEvaluatorShape evaluator = naturalListEvaluator(
						listRule, producer.guard(), growth.constructor());
				if (evaluator == null)
					continue;
				NumberedRule conjunctionRule = findConjunctionRule(
						rules, evaluator.conjunction(), growth.truth());
				NumberedRule elementBaseRule = findPredicateBaseRule(
						rules, evaluator.elementPredicate(), growth.truth());
				NumberedRule elementRule = findUnaryPredicateRule(
						rules, evaluator.elementPredicate(), growth.successor());
				if (conjunctionRule != null && elementBaseRule != null &&
						elementRule != null)
					return new NaturalListSchema(
							producerRule, growthRule, listRule, listBaseRule,
							elementBaseRule, conjunctionRule,
							producer.state(), growth.truth(), growth.constructor(),
							growth.successor(), empty,
							elementBaseRule.rule().getLeft().get(0));
			}
		}
		return null;
	}

	/** Extracts {@code list(C(x,xs)) -> and(nat(x),list(xs))}. */
	private static NaturalListEvaluatorShape naturalListEvaluator(
			NumberedRule numberedRule,
			FunctionSymbol predicate,
			FunctionSymbol constructor) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, predicate) || !hasRoot(left.get(0), constructor) ||
				!(left.get(0).get(0) instanceof Variable head) ||
				!(left.get(0).get(1) instanceof Variable tail) ||
				head.deepEquals(tail))
			return null;
		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 2)
			return null;
		Term elementGuard = right.get(0);
		Term tailGuard = right.get(1);
		if (elementGuard.isVariable() ||
				elementGuard.getRootSymbol().getArity() != 1 ||
				!elementGuard.get(0).deepEquals(head) ||
				!hasRoot(tailGuard, predicate) ||
				!tailGuard.get(0).deepEquals(tail))
			return null;
		return new NaturalListEvaluatorShape(
				right.getRootSymbol(), elementGuard.getRootSymbol());
	}

	/** Replays the first guarded natural-list phase. */
	private static NaturalListWitness buildNaturalListWitness(
			NaturalListSchema schema) {

		Term list = binary(
				schema.constructor(), schema.zero(), schema.empty());
		Term grownList = binary(
				schema.constructor(), unary(schema.successor(), schema.zero()), list);
		Term start = unary(schema.state(), list);
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(steps, start, schema.producerRule(), root());
		current = addStep(steps, current, schema.listRule(), position(0));
		current = addStep(
				steps, current, schema.elementBaseRule(), position(0, 0));
		current = addStep(steps, current, schema.listBaseRule(), position(0, 1));
		current = addStep(steps, current, schema.conjunctionRule(), position(0));
		current = addStep(steps, current, schema.growthRule(), root());
		Term expected = unary(schema.state(), grownList);
		return current != null && current.deepEquals(expected) ?
				new NaturalListWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Finds the unary state guarded through a generated list. */
	private static GeneratedListWitness findGeneratedListWitness(
			List<NumberedRule> rules) {

		for (NumberedRule transitionRule : rules) {
			GeneratedListWitness witness = generatedListWitness(
					rules, transitionRule);
			if (witness != null)
				return witness;
		}
		return null;
	}

	/** Tries to build one generated-list witness from a transition rule. */
	private static GeneratedListWitness generatedListWitness(
			List<NumberedRule> rules,
			NumberedRule transitionRule) {

		GeneratedTransitionShape transition = generatedTransition(transitionRule);
		if (transition == null)
			return null;
		NumberedRule branchRule = findGeneratedBranchRule(rules, transition);
		if (branchRule == null)
			return null;
		GeneratedListSchema schema = completeGeneratedListSchema(
				rules, transitionRule, branchRule, transition);
		return schema == null ? null : buildGeneratedListWitness(schema);
	}

	/** Extracts {@code p(x) -> b(list(gen(x)),s(x))}. */
	private static GeneratedTransitionShape generatedTransition(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (left.getRootSymbol().getArity() != 1 ||
				!(left.get(0) instanceof Variable counter))
			return null;
		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 2)
			return null;
		Term guard = right.get(0);
		Term grown = right.get(1);
		if (guard.isVariable() || guard.getRootSymbol().getArity() != 1 ||
				guard.get(0).isVariable() ||
				guard.get(0).getRootSymbol().getArity() != 1 ||
				!guard.get(0).get(0).deepEquals(counter) || grown.isVariable() ||
				grown.getRootSymbol().getArity() != 1 ||
				!grown.get(0).deepEquals(counter))
			return null;
		return new GeneratedTransitionShape(
				left.getRootSymbol(), right.getRootSymbol(),
				guard.getRootSymbol(), guard.get(0).getRootSymbol(),
				grown.getRootSymbol());
	}

	/** Finds {@code b(tt,x) -> p(x)} and completes the truth constant. */
	private static NumberedRule findGeneratedBranchRule(
			List<NumberedRule> rules,
			GeneratedTransitionShape transition) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, transition.branch()) ||
					!isConstant(left.get(0)) ||
					!(left.get(1) instanceof Variable result))
				continue;
			Term right = rule.getRight();
			if (hasRoot(right, transition.state()) &&
					right.get(0).deepEquals(result)) {
				transition.setTruth(left.get(0));
				return numberedRule;
			}
		}
		return null;
	}

	/** Completes the generator and list-recognizer rules. */
	private static GeneratedListSchema completeGeneratedListSchema(
			List<NumberedRule> rules,
			NumberedRule transitionRule,
			NumberedRule branchRule,
			GeneratedTransitionShape transition) {

		if (transition.truth() == null)
			return null;
		for (NumberedRule generatorBaseRule : rules) {
			GeneratedListSchema schema = generatedListSchema(
					rules, transitionRule, branchRule, transition,
					generatorBaseRule);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Tries one generator base rule when completing a generated-list schema. */
	private static GeneratedListSchema generatedListSchema(
			List<NumberedRule> rules,
			NumberedRule transitionRule,
			NumberedRule branchRule,
			GeneratedTransitionShape transition,
			NumberedRule generatorBaseRule) {

		ConstantMapping generatorBase = constantMapping(
				generatorBaseRule, transition.generator());
		if (generatorBase == null)
			return null;
		NumberedRule generatorRule = findGeneratorRule(rules, transition);
		if (generatorRule == null)
			return null;
		FunctionSymbol constructor =
				generatorRule.rule().getRight().getRootSymbol();
		NumberedRule listBaseRule = findExactPredicateBaseRule(
				rules, transition.predicate(), generatorBase.result(),
				transition.truth());
		NumberedRule listRule = findListTraversalRule(
				rules, transition.predicate(), constructor);
		return listBaseRule == null || listRule == null ? null :
				new GeneratedListSchema(
						transitionRule, branchRule, generatorBaseRule,
						listBaseRule, transition.state(), transition.truth(),
						transition.successor(), generatorBase.argument());
	}

	/** Finds {@code gen(s(x)) -> C(s(x),gen(x))}. */
	private static NumberedRule findGeneratorRule(
			List<NumberedRule> rules,
			GeneratedTransitionShape transition) {

		for (NumberedRule numberedRule : rules)
			if (isGeneratorRule(numberedRule, transition))
				return numberedRule;
		return null;
	}

	/** Tests whether a rule is {@code gen(s(x)) -> C(s(x),gen(x))}. */
	private static boolean isGeneratorRule(
			NumberedRule numberedRule,
			GeneratedTransitionShape transition) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, transition.generator()) ||
				!hasRoot(left.get(0), transition.successor()) ||
				!(left.get(0).get(0) instanceof Variable counter))
			return false;
		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 2 ||
				!right.get(0).deepEquals(left.get(0)))
			return false;
		Term recursive = right.get(1);
		return hasRoot(recursive, transition.generator()) &&
				recursive.get(0).deepEquals(counter);
	}

	/** Replays the first generated-list guard phase. */
	private static GeneratedListWitness buildGeneratedListWitness(
			GeneratedListSchema schema) {

		Term start = unary(schema.state(), schema.zero());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(steps, start, schema.transitionRule(), root());
		current = addStep(
				steps, current, schema.generatorBaseRule(), position(0, 0));
		current = addStep(steps, current, schema.listBaseRule(), position(0));
		current = addStep(steps, current, schema.branchRule(), root());
		Term expected = unary(
				schema.state(), unary(schema.successor(), schema.zero()));
		return current != null && current.deepEquals(expected) ?
				new GeneratedListWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Finds the four-argument unary-doubling presentation. */
	private static UnaryDoublingWitness findUnaryDoublingWitness(
			List<NumberedRule> rules) {

		for (NumberedRule growthRule : rules) {
			UnaryDoublingWitness witness = unaryDoublingWitness(rules, growthRule);
			if (witness != null)
				return witness;
		}
		return null;
	}

	/** Tries to build one unary-doubling witness from a growth rule. */
	private static UnaryDoublingWitness unaryDoublingWitness(
			List<NumberedRule> rules,
			NumberedRule growthRule) {

		UnaryDoublingGrowthShape growth = unaryDoublingGrowth(growthRule);
		if (growth == null)
			return null;
		NumberedRule firstBaseRule = findPredicateBaseRule(
				rules, growth.firstPredicate(), growth.truth());
		NumberedRule secondBaseRule = findPredicateBaseRule(
				rules, growth.secondPredicate(), growth.truth());
		if (firstBaseRule == null || secondBaseRule == null)
			return null;
		Term zero = firstBaseRule.rule().getLeft().get(0);
		if (!secondBaseRule.rule().getLeft().get(0).deepEquals(zero))
			return null;
		NumberedRule firstPredicateRule = findUnaryPredicateRule(
				rules, growth.firstPredicate(), growth.successor());
		NumberedRule secondPredicateRule = findUnaryPredicateRule(
				rules, growth.secondPredicate(), growth.successor());
		NumberedRule doublingBaseRule = findExactMappingRule(
				rules, growth.doubling(), zero, zero);
		NumberedRule doublingRule = findDoublingRule(rules, growth);
		if (firstPredicateRule == null || secondPredicateRule == null ||
				doublingBaseRule == null || doublingRule == null)
			return null;
		UnaryDoublingSchema schema = new UnaryDoublingSchema(
				growthRule, firstBaseRule, secondBaseRule,
				doublingBaseRule, doublingRule, growth.state(), growth.truth(),
				growth.successor(), zero);
		return buildUnaryDoublingWitness(schema);
	}

	/** Extracts the guarded two-counter root transition. */
	private static UnaryDoublingGrowthShape unaryDoublingGrowth(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (left.getRootSymbol().getArity() != 4 ||
				!isConstant(left.get(0)) ||
				!left.get(1).deepEquals(left.get(0)) ||
				!(left.get(2) instanceof Variable first) ||
				left.get(3).isVariable() ||
				left.get(3).getRootSymbol().getArity() != 1 ||
				!(left.get(3).get(0) instanceof Variable second) ||
				first.deepEquals(second))
			return null;

		Term right = rule.getRight();
		if (!hasRoot(right, left.getRootSymbol()))
			return null;
		Term firstGuard = right.get(0);
		Term secondGuard = right.get(1);
		Term grownFirst = right.get(2);
		Term grownSecond = right.get(3);
		FunctionSymbol successor = left.get(3).getRootSymbol();
		if (firstGuard.isVariable() ||
				firstGuard.getRootSymbol().getArity() != 1 ||
				!firstGuard.get(0).deepEquals(first) ||
				secondGuard.isVariable() ||
				secondGuard.getRootSymbol().getArity() != 1 ||
				!secondGuard.get(0).deepEquals(second) ||
				!hasRoot(grownFirst, successor) ||
				!grownFirst.get(0).deepEquals(first) ||
				grownSecond.isVariable() ||
				grownSecond.getRootSymbol().getArity() != 1 ||
				!grownSecond.get(0).deepEquals(left.get(3)))
			return null;
		return new UnaryDoublingGrowthShape(
				left.getRootSymbol(), left.get(0), successor,
				firstGuard.getRootSymbol(), secondGuard.getRootSymbol(),
				grownSecond.getRootSymbol());
	}

	/** Finds {@code double(s(x)) -> s(s(double(x)))}. */
	private static NumberedRule findDoublingRule(
			List<NumberedRule> rules,
			UnaryDoublingGrowthShape growth) {

		for (NumberedRule numberedRule : rules)
			if (isDoublingRule(numberedRule, growth))
				return numberedRule;
		return null;
	}

	/** Tests whether a rule is {@code double(s(x)) -> s(s(double(x)))}. */
	private static boolean isDoublingRule(
			NumberedRule numberedRule,
			UnaryDoublingGrowthShape growth) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (!hasRoot(left, growth.doubling()) ||
				!hasRoot(left.get(0), growth.successor()) ||
				!(left.get(0).get(0) instanceof Variable counter))
			return false;
		Term right = rule.getRight();
		if (!hasRoot(right, growth.successor()) ||
				!hasRoot(right.get(0), growth.successor()))
			return false;
		Term recursive = right.get(0).get(0);
		return hasRoot(recursive, growth.doubling()) &&
				recursive.get(0).deepEquals(counter);
	}

	/** Replays the first unary-doubling phase. */
	private static UnaryDoublingWitness buildUnaryDoublingWitness(
			UnaryDoublingSchema schema) {

		Term one = unary(schema.successor(), schema.zero());
		Term two = unary(schema.successor(), one);
		Term start = function(
				schema.state(), schema.truth(), schema.truth(), schema.zero(), one);
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(steps, start, schema.growthRule(), root());
		current = addStep(steps, current, schema.firstBaseRule(), position(0));
		current = addStep(steps, current, schema.secondBaseRule(), position(1));
		current = addStep(steps, current, schema.doublingRule(), position(3));
		current = addStep(
				steps, current, schema.doublingBaseRule(), position(3, 0, 0));
		Term expected = function(
				schema.state(), schema.truth(), schema.truth(), one, two);
		return current != null && current.deepEquals(expected) ?
				new UnaryDoublingWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Returns a constant argument of {@code p(c) -> truth}. */
	private static Term predicateBase(
			NumberedRule numberedRule,
			FunctionSymbol predicate,
			Term truth) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		return hasRoot(left, predicate) && isConstant(left.get(0)) &&
				rule.getRight().deepEquals(truth) ? left.get(0) : null;
	}

	/** Finds the first constant predicate base rule. */
	private static NumberedRule findPredicateBaseRule(
			List<NumberedRule> rules,
			FunctionSymbol predicate,
			Term truth) {

		for (NumberedRule numberedRule : rules)
			if (predicateBase(numberedRule, predicate, truth) != null)
				return numberedRule;
		return null;
	}

	/** Finds an exact constant predicate base rule. */
	private static NumberedRule findExactPredicateBaseRule(
			List<NumberedRule> rules,
			FunctionSymbol predicate,
			Term argument,
			Term result) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, predicate) && left.get(0).deepEquals(argument) &&
					rule.getRight().deepEquals(result))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code p(s(x)) -> p(x)}. */
	private static NumberedRule findUnaryPredicateRule(
			List<NumberedRule> rules,
			FunctionSymbol predicate,
			FunctionSymbol successor) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, predicate) ||
					!hasRoot(left.get(0), successor) ||
					!(left.get(0).get(0) instanceof Variable counter))
				continue;
			Term right = rule.getRight();
			if (hasRoot(right, predicate) && right.get(0).deepEquals(counter))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code and(tt,tt) -> tt}. */
	private static NumberedRule findConjunctionRule(
			List<NumberedRule> rules,
			FunctionSymbol conjunction,
			Term truth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, conjunction) && left.get(0).deepEquals(truth) &&
					left.get(1).deepEquals(truth) &&
					rule.getRight().deepEquals(truth))
				return numberedRule;
		}
		return null;
	}

	/** Extracts {@code f(c) -> d} for constants {@code c,d}. */
	private static ConstantMapping constantMapping(
			NumberedRule numberedRule,
			FunctionSymbol function) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		return hasRoot(left, function) && isConstant(left.get(0)) &&
				isConstant(rule.getRight()) ?
				new ConstantMapping(left.get(0), rule.getRight()) : null;
	}

	/** Finds an exact unary mapping rule. */
	private static NumberedRule findExactMappingRule(
			List<NumberedRule> rules,
			FunctionSymbol function,
			Term argument,
			Term result) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (hasRoot(left, function) && left.get(0).deepEquals(argument) &&
					rule.getRight().deepEquals(result))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code list(C(x,xs)) -> list(xs)}. */
	private static NumberedRule findListTraversalRule(
			List<NumberedRule> rules,
			FunctionSymbol predicate,
			FunctionSymbol constructor) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!hasRoot(left, predicate) || !hasRoot(left.get(0), constructor) ||
					!(left.get(0).get(0) instanceof Variable head) ||
					!(left.get(0).get(1) instanceof Variable tail) ||
					head.deepEquals(tail))
				continue;
			Term right = rule.getRight();
			if (hasRoot(right, predicate) && right.get(0).deepEquals(tail))
				return numberedRule;
		}
		return null;
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
		if (redex == null ||
				!rule.getLeft().isMoreGeneralThan(redex, substitution))
			return null;
		Term target = source.replace(
				position, rule.getRight().apply(substitution));
		steps.add(new RewriteStep(
				source, target, numberedRule.number(), position));
		return target;
	}

	/** Returns whether the term has the specified root. */
	private static boolean hasRoot(Term term, FunctionSymbol root) {
		return !term.isVariable() && term.getRootSymbol() == root;
	}

	/** Returns whether the term is a constant. */
	private static boolean isConstant(Term term) {
		return !term.isVariable() && term.getRootSymbol().getArity() == 0;
	}

	/** Builds a unary function term. */
	private static Term unary(FunctionSymbol root, Term argument) {
		return new Function(root, List.of(argument));
	}

	/** Builds a binary function term. */
	private static Term binary(FunctionSymbol root, Term first, Term second) {
		return new Function(root, List.of(first, second));
	}

	/** Builds a function term with the specified arguments. */
	private static Term function(FunctionSymbol root, Term... arguments) {
		return new Function(root, List.of(arguments));
	}

	/** Returns the root position. */
	private static Position root() {
		return new Position();
	}

	/** Builds a position from its successive indexes. */
	private static Position position(int... indexes) {
		Position position = new Position();
		for (int index : indexes)
			position = position.addLast(index);
		return position;
	}

	/** Formats a replayed sequence in proof order. */
	private static String formatRewriteSteps(
			List<RewriteStep> steps,
			int indentation) {

		String spaces = " ".repeat(Math.max(0, indentation));
		StringBuilder details = new StringBuilder();
		int number = 1;
		for (RewriteStep step : steps) {
			details.append(spaces).append(number++).append(". ")
					.append(step.source()).append(" -> ").append(step.target())
					.append(" (rule ").append(step.ruleNumber())
					.append(", position ").append(step.position()).append(")\n");
		}
		if (!details.isEmpty())
			details.setLength(details.length() - 1);
		return details.toString();
	}

	/** Common certificate ending with a replayed first phase. */
	private static String formatArgument(
			Term start,
			Term result,
			List<RewriteStep> steps,
			String description) {

		return TECHNIQUE_HEADER +
				"* Certificate: " + start + " is non-terminating\n" +
				"* Description:\n" + description + "\n" +
				"The first growth phase rewrites in " + steps.size() +
				" steps to\n" + result + ".\n" + formatRewriteSteps(steps, 0);
	}

	/** One input rule and its one-based input number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Roots extracted from the natural-list producer. */
	private record ProducerShape(
			FunctionSymbol state,
			FunctionSymbol branch,
			FunctionSymbol guard) {}

	/** Terms and roots extracted from natural-list growth. */
	private record NaturalListGrowthShape(
			Term truth,
			FunctionSymbol constructor,
			FunctionSymbol successor) {}

	/** Roots extracted from natural-list guard traversal. */
	private record NaturalListEvaluatorShape(
			FunctionSymbol conjunction,
			FunctionSymbol elementPredicate) {}

	/** Complete guarded natural-list schema. */
	private record NaturalListSchema(
			NumberedRule producerRule,
			NumberedRule growthRule,
			NumberedRule listRule,
			NumberedRule listBaseRule,
			NumberedRule elementBaseRule,
			NumberedRule conjunctionRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol constructor,
			FunctionSymbol successor,
			Term empty,
			Term zero) {}

	/** Replayed guarded natural-list witness. */
	private record NaturalListWitness(
			NaturalListSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** Mutable extraction of the generated-list transition. */
	private static final class GeneratedTransitionShape {

		private final FunctionSymbol state;
		private final FunctionSymbol branch;
		private final FunctionSymbol predicate;
		private final FunctionSymbol generator;
		private final FunctionSymbol successor;
		private Term truth;

		private GeneratedTransitionShape(
				FunctionSymbol state,
				FunctionSymbol branch,
				FunctionSymbol predicate,
				FunctionSymbol generator,
				FunctionSymbol successor) {
			this.state = state;
			this.branch = branch;
			this.predicate = predicate;
			this.generator = generator;
			this.successor = successor;
		}

		private FunctionSymbol state() { return this.state; }
		private FunctionSymbol branch() { return this.branch; }
		private FunctionSymbol predicate() { return this.predicate; }
		private FunctionSymbol generator() { return this.generator; }
		private FunctionSymbol successor() { return this.successor; }
		private Term truth() { return this.truth; }
		private void setTruth(Term truth) { this.truth = truth; }
	}

	/** A unary constant-to-constant mapping. */
	private record ConstantMapping(Term argument, Term result) {}

	/** Complete generated-list guard schema. */
	private record GeneratedListSchema(
			NumberedRule transitionRule,
			NumberedRule branchRule,
			NumberedRule generatorBaseRule,
			NumberedRule listBaseRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol successor,
			Term zero) {}

	/** Replayed generated-list guard witness. */
	private record GeneratedListWitness(
			GeneratedListSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** Roots extracted from unary-doubling growth. */
	private record UnaryDoublingGrowthShape(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol successor,
			FunctionSymbol firstPredicate,
			FunctionSymbol secondPredicate,
			FunctionSymbol doubling) {}

	/** Complete unary-doubling schema. */
	private record UnaryDoublingSchema(
			NumberedRule growthRule,
			NumberedRule firstBaseRule,
			NumberedRule secondBaseRule,
			NumberedRule doublingBaseRule,
			NumberedRule doublingRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol successor,
			Term zero) {}

	/** Replayed unary-doubling witness. */
	private record UnaryDoublingWitness(
			UnaryDoublingSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** One independently replayed rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** Proof argument for guarded natural-list growth. */
	private record NaturalListArgument(
			NaturalListWitness witness) implements Argument {

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
			NaturalListSchema schema = this.witness.schema();
			String description =
					"Let L0 be the displayed one-element natural list and let " +
					"L(n+1) prepend the successor of its head while retaining Ln. " +
					"The matched element and list evaluators reduce the guard of " +
					"each Ln to " + schema.truth() + ". Hence the producer and " +
					"branch rules establish Wn ->+ W(n+1) for every n >= 0. " +
					"Starting with W0 yields an infinite rewrite sequence.";
			return formatArgument(
					this.witness.start(), this.witness.result(),
					this.witness.steps(), description);
		}
	}

	/** Proof argument for generated-list guarded successor growth. */
	private record GeneratedListArgument(
			GeneratedListWitness witness) implements Argument {

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
			GeneratedListSchema schema = this.witness.schema();
			String description =
					"Write N0 = " + schema.zero() + " and N(n+1) for its " +
					"successor. The matched generator maps every Nn to a finite " +
					"list, and the matched traversal reduces its guard to " +
					schema.truth() + ". Therefore Wn ->+ W(n+1) for every " +
					"n >= 0. Starting with W0 yields an infinite rewrite sequence.";
			return formatArgument(
					this.witness.start(), this.witness.result(),
					this.witness.steps(), description);
		}
	}

	/** Proof argument for guarded unary doubling. */
	private record UnaryDoublingArgument(
			UnaryDoublingWitness witness) implements Argument {

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
			UnaryDoublingSchema schema = this.witness.schema();
			String description =
					"Let W(p,q) use unary counters p >= 0 and q >= 1. The " +
					"matched predicates reduce both guards to " + schema.truth() +
					", while the matched evaluator maps q to 2q. Thus " +
					"W(p,q) ->+ W(p+1,2q), which gives Wn ->+ W(n+1) and an " +
					"infinite rewrite sequence from the displayed ground state.";
			return formatArgument(
					this.witness.start(), this.witness.result(),
					this.witness.steps(), description);
		}
	}
}
