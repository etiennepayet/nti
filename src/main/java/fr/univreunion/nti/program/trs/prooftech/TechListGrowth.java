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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 * Recognizes bounded direct and guarded schemas that repeatedly grow a list.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechListGrowth implements ProofTechnique {

	/** Maximum number of rules inspected by this bounded technique. */
	private static final int MAX_RULE_COUNT = 200;

	/** Maximum length of a symbolic evaluator path. */
	private static final int MAX_EVALUATOR_SEARCH_DEPTH = 10;

	/** Maximum number of symbolic evaluator states. */
	private static final int MAX_EVALUATOR_STATE_COUNT = 2_048;

	/** Maximum depth of a retained symbolic evaluator term. */
	private static final int MAX_EVALUATOR_TERM_DEPTH = 32;

	/** Maximum rendering length of a retained symbolic evaluator term. */
	private static final int MAX_EVALUATOR_TERM_LENGTH = 8_192;

	/** Message emitted when no certified schema was found. */
	private static final String NOT_FOUND_MESSAGE = "No list growth found!";

	/** Kind shared by the list-growth proof arguments. */
	private static final String WITNESS_KIND = "list growth";

	/** Heading shared by the list-growth proof arguments. */
	private static final String TECHNIQUE_HEADER =
			"* Technique: bounded list-growth recognition\n";

	/** Certificate prefix shared by the list-growth proof arguments. */
	private static final String CERTIFICATE_PREFIX = "* Certificate: ";

	/** Shared suffix for the list-traversal derivation. */
	private static final String LIST_TRAVERSAL_RESULT = "(Ln) ->^(n+1) ";

	/** Shared transition from a step count to the first-phase result. */
	private static final String STEPS_TO_RESULT = " steps to\n";

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
		proof.printlnIfVerbose("## Searching for bounded list growth...");
		List<NumberedRule> rules = numberRules(trs);
		Argument argument = rules == null ? null : findArgument(rules);
		if (argument == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		proof.printlnIfVerbose("Found list growth!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(argument);
		return proof;
	}

	/** Finds the first replayable list-growth argument. */
	private static Argument findArgument(List<NumberedRule> rules) {
		Argument argument = buildDirectArgument(rules);
		if (argument == null)
			argument = buildGuardedArgument(rules);
		if (argument == null)
			argument = buildEvaluatorArgument(rules);
		if (argument == null)
			argument = buildLengthGuardedArgument(rules);
		return argument;
	}

	/** Builds the first replayable direct argument. */
	private static Argument buildDirectArgument(List<NumberedRule> rules) {
		ListGrowthSchema schema = findSchema(rules);
		ListGrowthWitness witness =
				schema == null ? null : buildWitness(schema);
		return witness == null ? null : new ListGrowthArgument(witness);
	}

	/** Builds the first replayable guarded argument. */
	private static Argument buildGuardedArgument(List<NumberedRule> rules) {
		GuardedListGrowthSchema schema = findGuardedSchema(rules);
		GuardedListGrowthWitness witness =
				schema == null ? null : buildGuardedWitness(schema);
		return witness == null ? null : new GuardedListGrowthArgument(witness);
	}

	/** Builds the first replayable evaluator-mediated argument. */
	private static Argument buildEvaluatorArgument(List<NumberedRule> rules) {
		EvaluatorListGrowthSchema schema = findEvaluatorSchema(rules);
		EvaluatorListGrowthWitness witness =
				schema == null ? null : buildEvaluatorWitness(schema);
		return witness == null ? null :
				new EvaluatorListGrowthArgument(witness);
	}

	/** Builds the first replayable length-guarded argument. */
	private static Argument buildLengthGuardedArgument(
			List<NumberedRule> rules) {

		LengthGuardedListGrowthSchema schema =
				findLengthGuardedSchema(rules);
		LengthGuardedListGrowthWitness witness = schema == null ? null :
				buildLengthGuardedWitness(schema);
		return witness == null ? null :
				new LengthGuardedListGrowthArgument(witness);
	}

	/** Numbers at most {@link #MAX_RULE_COUNT} rules in input order. */
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

	/** Finds the first complete direct schema in input-rule order. */
	private static ListGrowthSchema findSchema(List<NumberedRule> rules) {
		for (NumberedRule growthRule : rules) {
			GrowthRuleShape growth = growthRuleShape(growthRule);
			if (growth == null)
				continue;
			NumberedRule traversalRule = findTraversalRule(
					rules, growth.predicate(), growth.constructor());
			NumberedRule baseRule = findBaseRule(
					rules, growth.predicate(), growth.truth());
			if (traversalRule != null && baseRule != null)
				return new ListGrowthSchema(
						growthRule, traversalRule, baseRule,
						growth.state(), growth.truth(), growth.predicate(),
						growth.constructor(), growth.extensionKind(),
						baseRule.rule().getLeft().get(0));
		}
		return null;
	}

	/**
	 * Extracts {@code f(tt,x) -> f(isList(x),Cons(h,x))}, where {@code h}
	 * is either {@code tt} or {@code x}.
	 */
	private static GrowthRuleShape growthRuleShape(NumberedRule numberedRule) {
		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 2 || !isConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable tail))
			return null;
		Term truth = left.get(0);

		Term right = rule.getRight();
		if (lacksRoot(right, state))
			return null;
		Term predicateOfTail = right.get(0);
		if (predicateOfTail.isVariable() ||
				predicateOfTail.getRootSymbol().getArity() != 1 ||
				!predicateOfTail.get(0).deepEquals(tail))
			return null;
		FunctionSymbol predicate = predicateOfTail.getRootSymbol();

		Term extendedList = right.get(1);
		if (extendedList.isVariable() ||
				extendedList.getRootSymbol().getArity() != 2 ||
				!extendedList.get(1).deepEquals(tail))
			return null;
		ExtensionKind extensionKind;
		if (extendedList.get(0).deepEquals(truth))
			extensionKind = ExtensionKind.PREPEND_TRUTH;
		else if (extendedList.get(0).deepEquals(tail))
			extensionKind = ExtensionKind.DUPLICATE_TAIL;
		else
			return null;
		return new GrowthRuleShape(
				state, truth, predicate, extendedList.getRootSymbol(),
				extensionKind);
	}

	/** Finds {@code isList(Cons(x,xs)) -> isList(xs)}. */
	private static NumberedRule findTraversalRule(
			List<NumberedRule> rules,
			FunctionSymbol predicate,
			FunctionSymbol constructor) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, predicate) ||
					lacksRoot(left.get(0), constructor) ||
					!(left.get(0).get(0) instanceof Variable head) ||
					!(left.get(0).get(1) instanceof Variable tail) ||
					head.deepEquals(tail))
				continue;

			Term right = rule.getRight();
			if (!lacksRoot(right, predicate) &&
					right.get(0).deepEquals(tail))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code isList(nil) -> tt}. */
	private static NumberedRule findBaseRule(
			List<NumberedRule> rules,
			FunctionSymbol predicate,
			Term truth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!lacksRoot(left, predicate) &&
					isConstant(left.get(0)) &&
					rule.getRight().deepEquals(truth))
				return numberedRule;
		}
		return null;
	}

	/** Finds the first complete guarded schema in input-rule order. */
	private static GuardedListGrowthSchema findGuardedSchema(
			List<NumberedRule> rules) {

		for (NumberedRule growthRule : rules) {
			GuardedGrowthRuleShape growth =
					guardedGrowthRuleShape(growthRule);
			if (growth == null)
				continue;
			NumberedRule traversalRule = findTraversalRule(
					rules, growth.listPredicate(), growth.constructor());
			NumberedRule listBaseRule = findBaseRule(
					rules, growth.listPredicate(), growth.truth());
			NumberedRule elementBaseRule = findBaseRule(
					rules, growth.elementPredicate(), growth.truth());
			NumberedRule conjunctionRule = findConjunctionRule(
					rules, growth.conjunction(), growth.truth());
			if (traversalRule != null && listBaseRule != null &&
					elementBaseRule != null && conjunctionRule != null)
				return new GuardedListGrowthSchema(
						growthRule, traversalRule, listBaseRule,
						elementBaseRule, conjunctionRule, growth.state(),
						growth.truth(), growth.elementPredicate(),
						growth.listPredicate(), growth.constructor(),
						growth.elementVariable(), growth.tailVariable(),
						growth.newHead(),
						elementBaseRule.rule().getLeft().get(0),
						listBaseRule.rule().getLeft().get(0));
		}
		return null;
	}

	/**
	 * Extracts a rule of the form
	 * {@code f(tt,e,xs) -> f(and(isElement(e),isList(xs)),e,Cons(h,xs))}.
	 */
	private static GuardedGrowthRuleShape guardedGrowthRuleShape(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 3 || !isConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable element) ||
				!(left.get(2) instanceof Variable tail) ||
				element.deepEquals(tail))
			return null;
		Term truth = left.get(0);

		Term right = rule.getRight();
		if (lacksRoot(right, state) || !right.get(1).deepEquals(element))
			return null;
		Term guard = right.get(0);
		if (guard.isVariable() || guard.getRootSymbol().getArity() != 2)
			return null;
		Term elementGuard = guard.get(0);
		Term listGuard = guard.get(1);
		if (elementGuard.isVariable() ||
				elementGuard.getRootSymbol().getArity() != 1 ||
				!elementGuard.get(0).deepEquals(element) ||
				listGuard.isVariable() ||
				listGuard.getRootSymbol().getArity() != 1 ||
				!listGuard.get(0).deepEquals(tail))
			return null;

		Term extendedList = right.get(2);
		if (extendedList.isVariable() ||
				extendedList.getRootSymbol().getArity() != 2 ||
				!extendedList.get(1).deepEquals(tail))
			return null;
		return new GuardedGrowthRuleShape(
				state, truth, guard.getRootSymbol(),
				elementGuard.getRootSymbol(), listGuard.getRootSymbol(),
				extendedList.getRootSymbol(), element, tail,
				extendedList.get(0));
	}

	/** Finds {@code and(tt,tt) -> tt}. */
	private static NumberedRule findConjunctionRule(
			List<NumberedRule> rules,
			FunctionSymbol conjunction,
			Term truth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!lacksRoot(left, conjunction) &&
					left.get(0).deepEquals(truth) &&
					left.get(1).deepEquals(truth) &&
					rule.getRight().deepEquals(truth))
				return numberedRule;
		}
		return null;
	}

	/** Finds the first schema whose list extension is symbolically evaluated. */
	private static EvaluatorListGrowthSchema findEvaluatorSchema(
			List<NumberedRule> rules) {

		Map<FunctionSymbol, List<NumberedRule>> rulesByRoot =
				indexRulesByRoot(rules);
		for (NumberedRule growthRule : rules) {
			EvaluatorListGrowthSchema schema = findEvaluatorSchema(
					growthRule, rules, rulesByRoot);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Tries one candidate evaluator-mediated growth rule. */
	private static EvaluatorListGrowthSchema findEvaluatorSchema(
			NumberedRule growthRule,
			List<NumberedRule> rules,
			Map<FunctionSymbol, List<NumberedRule>> rulesByRoot) {

		EvaluatorGrowthRuleShape growth =
				evaluatorGrowthRuleShape(growthRule);
		if (growth == null)
			return null;
		NumberedRule baseRule = findBaseRule(
				rules, growth.predicate(), growth.truth());
		if (baseRule == null)
			return null;
		Term emptyList = baseRule.rule().getLeft().get(0);
		for (TraversalRuleShape traversal :
				findTraversalRules(rules, growth.predicate())) {
			EvaluatorPath evaluatorPath = new EvaluatorSearch(
					growth.evaluator(), growth.tailVariable(), emptyList,
					traversal.constructor(), rulesByRoot).search();
			if (evaluatorPath != null)
				return new EvaluatorListGrowthSchema(
						growthRule, traversal.rule(), baseRule,
						growth.state(), growth.truth(), growth.predicate(),
						traversal.constructor(), growth.tailVariable(),
						growth.evaluator(), emptyList, evaluatorPath);
		}
		return null;
	}

	/** Extracts {@code f(tt,xs) -> f(isList(xs),E(xs))}. */
	private static EvaluatorGrowthRuleShape evaluatorGrowthRuleShape(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 2 || !isConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable tail))
			return null;
		Term right = rule.getRight();
		if (lacksRoot(right, state))
			return null;
		Term predicateOfTail = right.get(0);
		if (predicateOfTail.isVariable() ||
				predicateOfTail.getRootSymbol().getArity() != 1 ||
				!predicateOfTail.get(0).deepEquals(tail))
			return null;
		return new EvaluatorGrowthRuleShape(
				state, left.get(0), predicateOfTail.getRootSymbol(), tail,
				right.get(1));
	}

	/** Finds all exact {@code isList(Cons(x,xs)) -> isList(xs)} rules. */
	private static List<TraversalRuleShape> findTraversalRules(
			List<NumberedRule> rules,
			FunctionSymbol predicate) {

		List<TraversalRuleShape> traversals = new ArrayList<>();
		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, predicate) || left.get(0).isVariable() ||
					left.get(0).getRootSymbol().getArity() != 2 ||
					!(left.get(0).get(0) instanceof Variable head) ||
					!(left.get(0).get(1) instanceof Variable tail) ||
					head.deepEquals(tail))
				continue;
			Term right = rule.getRight();
			if (!lacksRoot(right, predicate) && right.get(0).deepEquals(tail))
				traversals.add(new TraversalRuleShape(
						numberedRule, left.get(0).getRootSymbol()));
		}
		return List.copyOf(traversals);
	}

	/** Indexes rules by left-root symbol while preserving input order. */
	private static Map<FunctionSymbol, List<NumberedRule>> indexRulesByRoot(
			List<NumberedRule> rules) {

		Map<FunctionSymbol, List<NumberedRule>> rulesByRoot =
				new LinkedHashMap<>();
		for (NumberedRule numberedRule : rules)
			rulesByRoot.computeIfAbsent(
					numberedRule.rule().getLeft().getRootSymbol(),
					ignored -> new ArrayList<>()).add(numberedRule);
		return rulesByRoot;
	}

	/** Finds the first schema guarded by equality of two list lengths. */
	private static LengthGuardedListGrowthSchema findLengthGuardedSchema(
			List<NumberedRule> rules) {

		Map<FunctionSymbol, List<NumberedRule>> rulesByRoot =
				indexRulesByRoot(rules);
		for (NumberedRule growthRule : rules) {
			LengthGuardedListGrowthSchema schema = findLengthGuardedSchema(
					growthRule, rules, rulesByRoot);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Tries one candidate length-guarded growth rule. */
	private static LengthGuardedListGrowthSchema findLengthGuardedSchema(
			NumberedRule growthRule,
			List<NumberedRule> rules,
			Map<FunctionSymbol, List<NumberedRule>> rulesByRoot) {

		LengthGuardedGrowthRuleShape growth =
				lengthGuardedGrowthRuleShape(growthRule);
		if (growth == null)
			return null;
		NumberedRule lengthTraversalRule = findLengthTraversalRule(rules, growth);
		NumberedRule equalityTraversalRule =
				findEqualityTraversalRule(rules, growth);
		if (lengthTraversalRule == null || equalityTraversalRule == null)
			return null;
		for (LengthBaseRuleShape lengthBase :
				findLengthBaseRules(rules, growth.length())) {
			LengthGuardedListGrowthSchema schema = buildLengthGuardedSchema(
					growthRule, growth, lengthTraversalRule,
					equalityTraversalRule, lengthBase, rules, rulesByRoot);
			if (schema != null)
				return schema;
		}
		return null;
	}

	/** Completes one length-guarded candidate from a length-base rule. */
	private static LengthGuardedListGrowthSchema buildLengthGuardedSchema(
			NumberedRule growthRule,
			LengthGuardedGrowthRuleShape growth,
			NumberedRule lengthTraversalRule,
			NumberedRule equalityTraversalRule,
			LengthBaseRuleShape lengthBase,
			List<NumberedRule> rules,
			Map<FunctionSymbol, List<NumberedRule>> rulesByRoot) {

		NumberedRule equalityBaseRule = findEqualityBaseRule(
				rules, growth.equality(), lengthBase.zero(), growth.truth());
		if (equalityBaseRule == null)
			return null;
		EvaluatorPath evaluatorPath = new EvaluatorSearch(
				growth.evaluator(), growth.tailVariable(), lengthBase.emptyList(),
				growth.constructor(), rulesByRoot).search();
		return evaluatorPath == null ? null : new LengthGuardedListGrowthSchema(
				growthRule, lengthTraversalRule, lengthBase.rule(),
				equalityTraversalRule, equalityBaseRule, growth.state(),
				growth.truth(), growth.length(), growth.tailVariable(),
				lengthBase.emptyList(), evaluatorPath);
	}

	/**
	 * Extracts
	 * {@code f(tt,xs) -> f(eq(s(length(xs)),length(Cons(h,xs))),E(xs))}.
	 */
	private static LengthGuardedGrowthRuleShape lengthGuardedGrowthRuleShape(
			NumberedRule numberedRule) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol state = left.getRootSymbol();
		if (state.getArity() != 2 || !isConstant(left.get(0)) ||
				!(left.get(1) instanceof Variable tail))
			return null;
		Term right = rule.getRight();
		if (lacksRoot(right, state))
			return null;
		Term guard = right.get(0);
		if (guard.isVariable() || guard.getRootSymbol().getArity() != 2)
			return null;
		Term successorOfLength = guard.get(0);
		if (successorOfLength.isVariable() ||
				successorOfLength.getRootSymbol().getArity() != 1)
			return null;
		Term lengthOfTail = successorOfLength.get(0);
		if (lengthOfTail.isVariable() ||
				lengthOfTail.getRootSymbol().getArity() != 1 ||
				!lengthOfTail.get(0).deepEquals(tail))
			return null;

		FunctionSymbol length = lengthOfTail.getRootSymbol();
		Term lengthOfExtendedTail = guard.get(1);
		if (lacksRoot(lengthOfExtendedTail, length))
			return null;
		Term extendedTail = lengthOfExtendedTail.get(0);
		if (extendedTail.isVariable() ||
				extendedTail.getRootSymbol().getArity() != 2 ||
				!extendedTail.get(1).deepEquals(tail))
			return null;
		return new LengthGuardedGrowthRuleShape(
				state, left.get(0), guard.getRootSymbol(),
				successorOfLength.getRootSymbol(), length,
				extendedTail.getRootSymbol(), tail, right.get(1));
	}

	/** Finds {@code length(Cons(x,xs)) -> s(length(xs))}. */
	private static NumberedRule findLengthTraversalRule(
			List<NumberedRule> rules,
			LengthGuardedGrowthRuleShape growth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, growth.length()) ||
					lacksRoot(left.get(0), growth.constructor()) ||
					!(left.get(0).get(0) instanceof Variable head) ||
					!(left.get(0).get(1) instanceof Variable tail) ||
					head.deepEquals(tail))
				continue;
			Term right = rule.getRight();
			if (!lacksRoot(right, growth.successor()) &&
					!lacksRoot(right.get(0), growth.length()) &&
					right.get(0).get(0).deepEquals(tail))
				return numberedRule;
		}
		return null;
	}

	/** Finds all {@code length(nil) -> zero} constant-base rules. */
	private static List<LengthBaseRuleShape> findLengthBaseRules(
			List<NumberedRule> rules,
			FunctionSymbol length) {

		List<LengthBaseRuleShape> bases = new ArrayList<>();
		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!lacksRoot(left, length) && isConstant(left.get(0)) &&
					isConstant(rule.getRight()))
				bases.add(new LengthBaseRuleShape(
						numberedRule, left.get(0), rule.getRight()));
		}
		return List.copyOf(bases);
	}

	/** Finds {@code eq(s(x),s(y)) -> eq(x,y)}. */
	private static NumberedRule findEqualityTraversalRule(
			List<NumberedRule> rules,
			LengthGuardedGrowthRuleShape growth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, growth.equality()) ||
					lacksRoot(left.get(0), growth.successor()) ||
					lacksRoot(left.get(1), growth.successor()) ||
					!(left.get(0).get(0) instanceof Variable first) ||
					!(left.get(1).get(0) instanceof Variable second) ||
					first.deepEquals(second))
				continue;
			Term right = rule.getRight();
			if (!lacksRoot(right, growth.equality()) &&
					right.get(0).deepEquals(first) &&
					right.get(1).deepEquals(second))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code eq(zero,zero) -> tt}. */
	private static NumberedRule findEqualityBaseRule(
			List<NumberedRule> rules,
			FunctionSymbol equality,
			Term zero,
			Term truth) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (!lacksRoot(left, equality) &&
					left.get(0).deepEquals(zero) &&
					left.get(1).deepEquals(zero) &&
					rule.getRight().deepEquals(truth))
				return numberedRule;
		}
		return null;
	}

	/** Builds and replays the concrete growth phase from the empty list. */
	private static ListGrowthWitness buildWitness(ListGrowthSchema schema) {
		Term listOne = new Function(
				schema.constructor(),
				List.of(extensionHead(schema, schema.emptyList()), schema.emptyList()));
		Term start = new Function(
				schema.state(), List.of(schema.truth(), schema.emptyList()));
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(
				steps, start, schema.growthRule(), new Position());
		current = addStep(
				steps, current, schema.baseRule(), new Position(0));

		Term expected = new Function(
				schema.state(), List.of(schema.truth(), listOne));
		return current != null && current.deepEquals(expected) ?
				new ListGrowthWitness(schema, start, current, List.copyOf(steps)) :
				null;
	}

	/** Builds and replays the first concrete guarded growth phase. */
	private static GuardedListGrowthWitness buildGuardedWitness(
			GuardedListGrowthSchema schema) {

		Substitution substitution = new Substitution();
		if (!substitution.add(
				schema.elementVariable(), schema.fixedElement()) ||
				!substitution.add(schema.tailVariable(), schema.emptyList()))
			return null;
		Term newHead = schema.newHead().apply(substitution);
		if (!newHead.isGround())
			return null;
		Term listOne = new Function(
				schema.constructor(), List.of(newHead, schema.emptyList()));
		Term start = new Function(schema.state(), List.of(
				schema.truth(), schema.fixedElement(), schema.emptyList()));
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(
				steps, start, schema.growthRule(), new Position());
		current = addStep(steps, current, schema.elementBaseRule(),
				new Position(0).addLast(0));
		current = addStep(steps, current, schema.listBaseRule(),
				new Position(0).addLast(1));
		current = addStep(
				steps, current, schema.conjunctionRule(), new Position(0));

		Term expected = new Function(schema.state(), List.of(
				schema.truth(), schema.fixedElement(), listOne));
		return current != null && current.deepEquals(expected) ?
				new GuardedListGrowthWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Builds and replays the first evaluator-mediated growth phase. */
	private static EvaluatorListGrowthWitness buildEvaluatorWitness(
			EvaluatorListGrowthSchema schema) {

		Substitution substitution = new Substitution();
		if (!substitution.add(schema.tailVariable(), schema.emptyList()))
			return null;
		Term evaluator = schema.evaluator().apply(substitution);
		Term evaluatedList = schema.evaluatorPath().result().apply(substitution);
		if (!evaluator.isGround() || !evaluatedList.isGround())
			return null;

		Term start = new Function(
				schema.state(), List.of(schema.truth(), schema.emptyList()));
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(
				steps, start, schema.growthRule(), new Position());
		current = addStep(steps, current, schema.baseRule(), new Position(0));
		for (EvaluatorStep evaluatorStep : schema.evaluatorPath().steps())
			current = addStep(
					steps, current, evaluatorStep.rule(),
					new Position(1).append(evaluatorStep.position()));

		Term expected = new Function(
				schema.state(), List.of(schema.truth(), evaluatedList));
		return current != null && current.deepEquals(expected) ?
				new EvaluatorListGrowthWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Builds and replays the first length-guarded growth phase. */
	private static LengthGuardedListGrowthWitness buildLengthGuardedWitness(
			LengthGuardedListGrowthSchema schema) {

		Substitution substitution = new Substitution();
		if (!substitution.add(schema.tailVariable(), schema.emptyList()))
			return null;
		Term instantiatedRight =
				schema.growthRule().rule().getRight().apply(substitution);
		Term evaluatedList = schema.evaluatorPath().result().apply(substitution);
		if (!instantiatedRight.isGround() || !evaluatedList.isGround())
			return null;

		Term start = new Function(
				schema.state(), List.of(schema.truth(), schema.emptyList()));
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(
				steps, start, schema.growthRule(), new Position());
		current = addStep(steps, current, schema.lengthTraversalRule(),
				new Position(0).addLast(1));
		current = addStep(steps, current, schema.equalityTraversalRule(),
				new Position(0));
		current = addStep(steps, current, schema.lengthBaseRule(),
				new Position(0).addLast(0));
		current = addStep(steps, current, schema.lengthBaseRule(),
				new Position(0).addLast(1));
		current = addStep(steps, current, schema.equalityBaseRule(),
				new Position(0));
		for (EvaluatorStep evaluatorStep : schema.evaluatorPath().steps())
			current = addStep(
					steps, current, evaluatorStep.rule(),
					new Position(1).append(evaluatorStep.position()));

		Term expected = new Function(
				schema.state(), List.of(schema.truth(), evaluatedList));
		return current != null && current.deepEquals(expected) ?
				new LengthGuardedListGrowthWitness(
						schema, start, current, List.copyOf(steps)) : null;
	}

	/** Returns the head used when extending the specified list. */
	private static Term extensionHead(ListGrowthSchema schema, Term list) {
		return schema.extensionKind() == ExtensionKind.DUPLICATE_TAIL ?
				list : schema.truth();
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

	/** Formats a replayed sequence of rewrite steps. */
	private static String formatRewriteSteps(
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

	/** Bounded breadth-first search for one symbolic evaluator path. */
	private static final class EvaluatorSearch {

		private final Term source;
		private final Variable tailVariable;
		private final Term emptyList;
		private final FunctionSymbol constructor;
		private final Map<FunctionSymbol, List<NumberedRule>> rulesByRoot;
		private final ArrayDeque<EvaluatorSearchNode> pending =
				new ArrayDeque<>();
		private final Set<String> visited = new HashSet<>();

		private EvaluatorSearch(
				Term source,
				Variable tailVariable,
				Term emptyList,
				FunctionSymbol constructor,
				Map<FunctionSymbol, List<NumberedRule>> rulesByRoot) {
			this.source = source;
			this.tailVariable = tailVariable;
			this.emptyList = emptyList;
			this.constructor = constructor;
			this.rulesByRoot = rulesByRoot;
		}

		/** Searches for {@code E(xs) ->* Cons(H(xs),xs)}. */
		private EvaluatorPath search() {
			if (exceedsTermBounds(this.source))
				return null;
			EvaluatorSearchNode initial = new EvaluatorSearchNode(
					this.source, null, null, null, 0);
			if (isTarget(this.source))
				return buildPath(initial);
			this.pending.add(initial);
			this.visited.add(this.source.toString());

			while (!this.pending.isEmpty() &&
					this.visited.size() < MAX_EVALUATOR_STATE_COUNT) {
				EvaluatorSearchNode current = this.pending.remove();
				if (current.depth() < MAX_EVALUATOR_SEARCH_DEPTH) {
					EvaluatorPath path = expand(current);
					if (path != null)
						return path;
				}
			}
			return null;
		}

		/** Expands one symbolic term in position and input-rule order. */
		private EvaluatorPath expand(EvaluatorSearchNode current) {
			for (Position position : current.term()) {
				Term redex = current.term().get(position);
				if (redex.isVariable())
					continue;
				List<NumberedRule> candidates =
						this.rulesByRoot.get(redex.getRootSymbol());
				if (candidates != null)
					for (NumberedRule numberedRule : candidates) {
						EvaluatorPath path = apply(
								current, position, redex, numberedRule);
						if (path != null)
							return path;
					}
			}
			return null;
		}

		/** Applies and retains one admissible symbolic rewrite. */
		private EvaluatorPath apply(
				EvaluatorSearchNode current,
				Position position,
				Term redex,
				NumberedRule numberedRule) {

			Substitution substitution = new Substitution();
			RuleTrs rule = numberedRule.rule();
			if (!rule.getLeft().isMoreGeneralThan(redex, substitution))
				return null;
			Term target = current.term().replace(
					position, rule.getRight().apply(substitution));
			if (exceedsTermBounds(target))
				return null;
			EvaluatorSearchNode next = new EvaluatorSearchNode(
					target, current, numberedRule, position, current.depth() + 1);
			if (isTarget(target))
				return buildPath(next);
			String key = target.toString();
			if (this.visited.add(key))
				this.pending.add(next);
			return null;
		}

		/** Tests whether a term exceeds a symbolic-search size bound. */
		private static boolean exceedsTermBounds(Term term) {
			return term.depth() > MAX_EVALUATOR_TERM_DEPTH ||
					term.toString().length() > MAX_EVALUATOR_TERM_LENGTH;
		}

		/** Tests for {@code Cons(H(xs),xs)} with a ground first instance. */
		private boolean isTarget(Term term) {
			if (lacksRoot(term, this.constructor) ||
					!term.get(1).deepEquals(this.tailVariable))
				return false;
			Substitution substitution = new Substitution();
			return substitution.add(this.tailVariable, this.emptyList) &&
					term.get(0).apply(substitution).isGround();
		}

		/** Reconstructs a successful symbolic path. */
		private EvaluatorPath buildPath(EvaluatorSearchNode last) {
			List<EvaluatorStep> steps = new ArrayList<>();
			for (EvaluatorSearchNode node = last; node.parent() != null;
					node = node.parent())
				steps.add(new EvaluatorStep(node.rule(), node.position()));
			Collections.reverse(steps);
			return new EvaluatorPath(
					this.source, last.term(), List.copyOf(steps));
		}
	}

	/** One input rule together with its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Symbols and the constant extracted from the growth rule. */
	private record GrowthRuleShape(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol predicate,
			FunctionSymbol constructor,
			ExtensionKind extensionKind) {}

	/** A complete matched rule schema. */
	private record ListGrowthSchema(
			NumberedRule growthRule,
			NumberedRule traversalRule,
			NumberedRule baseRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol predicate,
			FunctionSymbol constructor,
			ExtensionKind extensionKind,
			Term emptyList) {}

	/** Symbols and terms extracted from a guarded growth rule. */
	private record GuardedGrowthRuleShape(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol conjunction,
			FunctionSymbol elementPredicate,
			FunctionSymbol listPredicate,
			FunctionSymbol constructor,
			Variable elementVariable,
			Variable tailVariable,
			Term newHead) {}

	/** A complete matched guarded schema. */
	private record GuardedListGrowthSchema(
			NumberedRule growthRule,
			NumberedRule traversalRule,
			NumberedRule listBaseRule,
			NumberedRule elementBaseRule,
			NumberedRule conjunctionRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol elementPredicate,
			FunctionSymbol listPredicate,
			FunctionSymbol constructor,
			Variable elementVariable,
			Variable tailVariable,
			Term newHead,
			Term fixedElement,
			Term emptyList) {}

	/** Symbols and terms extracted from an evaluator-mediated growth rule. */
	private record EvaluatorGrowthRuleShape(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol predicate,
			Variable tailVariable,
			Term evaluator) {}

	/** One exact list-traversal rule and its constructor. */
	private record TraversalRuleShape(
			NumberedRule rule,
			FunctionSymbol constructor) {}

	/** One rewrite in a symbolic evaluator path. */
	private record EvaluatorStep(
			NumberedRule rule,
			Position position) {}

	/** A symbolic evaluator derivation. */
	private record EvaluatorPath(
			Term source,
			Term result,
			List<EvaluatorStep> steps) {}

	/** One node of the bounded symbolic evaluator search. */
	private record EvaluatorSearchNode(
			Term term,
			EvaluatorSearchNode parent,
			NumberedRule rule,
			Position position,
			int depth) {}

	/** A complete evaluator-mediated list-growth schema. */
	private record EvaluatorListGrowthSchema(
			NumberedRule growthRule,
			NumberedRule traversalRule,
			NumberedRule baseRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol predicate,
			FunctionSymbol constructor,
			Variable tailVariable,
			Term evaluator,
			Term emptyList,
			EvaluatorPath evaluatorPath) {}

	/** Symbols and terms extracted from a length-guarded growth rule. */
	private record LengthGuardedGrowthRuleShape(
			FunctionSymbol state,
			Term truth,
			FunctionSymbol equality,
			FunctionSymbol successor,
			FunctionSymbol length,
			FunctionSymbol constructor,
			Variable tailVariable,
			Term evaluator) {}

	/** One constant base rule for a length computation. */
	private record LengthBaseRuleShape(
			NumberedRule rule,
			Term emptyList,
			Term zero) {}

	/** A complete length-guarded list-growth schema. */
	private record LengthGuardedListGrowthSchema(
			NumberedRule growthRule,
			NumberedRule lengthTraversalRule,
			NumberedRule lengthBaseRule,
			NumberedRule equalityTraversalRule,
			NumberedRule equalityBaseRule,
			FunctionSymbol state,
			Term truth,
			FunctionSymbol length,
			Variable tailVariable,
			Term emptyList,
			EvaluatorPath evaluatorPath) {}

	/** Supported shapes of the new list head. */
	private enum ExtensionKind {
		PREPEND_TRUTH,
		DUPLICATE_TAIL
	}

	/** One replayed rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** The matched schema and its concrete first growth phase. */
	private record ListGrowthWitness(
			ListGrowthSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** The matched guarded schema and its concrete first growth phase. */
	private record GuardedListGrowthWitness(
			GuardedListGrowthSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** The evaluator schema and its concrete first growth phase. */
	private record EvaluatorListGrowthWitness(
			EvaluatorListGrowthSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** The length-guarded schema and its concrete first growth phase. */
	private record LengthGuardedListGrowthWitness(
			LengthGuardedListGrowthSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** Proof argument for a certified list-growth schema. */
	private record ListGrowthArgument(
			ListGrowthWitness witness) implements Argument {

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
			ListGrowthSchema schema = this.witness.schema();
			String state = schema.state().toString();
			String truth = schema.truth().toString();
			String predicate = schema.predicate().toString();
			String constructor = schema.constructor().toString();
			String emptyList = schema.emptyList().toString();
			String newHead = schema.extensionKind() ==
					ExtensionKind.DUPLICATE_TAIL ? "Ln" : truth;
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write L0 = " + emptyList + " and L(n+1) = " +
					constructor + "(" + newHead + ",Ln). The matched traversal " +
					"and base rules imply " + predicate +
					LIST_TRAVERSAL_RESULT + truth + ".\n" +
					"Consequently, for every n >= 0, " + state + "(" +
					truth + ",Ln) ->^(n+2) " + state + "(" + truth +
					",L(n+1)). Starting with L0 yields an infinite rewrite " +
					"sequence.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO_RESULT +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

	/** Proof argument for a certified guarded list-growth schema. */
	private record GuardedListGrowthArgument(
			GuardedListGrowthWitness witness) implements Argument {

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
			GuardedListGrowthSchema schema = this.witness.schema();
			String state = schema.state().toString();
			String truth = schema.truth().toString();
			String elementPredicate = schema.elementPredicate().toString();
			String listPredicate = schema.listPredicate().toString();
			String fixedElement = schema.fixedElement().toString();
			String emptyList = schema.emptyList().toString();
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Fix e = " + fixedElement + ", write L0 = " + emptyList +
					" and let L(n+1) be the list built by the matched growth " +
					"rule. The matched base rules give " + elementPredicate +
					"(e) -> " + truth + ", while the traversal and list-base " +
					"rules imply " + listPredicate + LIST_TRAVERSAL_RESULT + truth +
					".\nConsequently, for every n >= 0, " + state + "(" + truth +
					",e,Ln) ->^(n+4) " + state + "(" + truth +
					",e,L(n+1)). Starting with L0 yields an infinite rewrite " +
					"sequence.\nThe first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO_RESULT +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

	/** Proof argument for an evaluator-mediated list-growth schema. */
	private record EvaluatorListGrowthArgument(
			EvaluatorListGrowthWitness witness) implements Argument {

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
			EvaluatorListGrowthSchema schema = this.witness.schema();
			EvaluatorPath evaluatorPath = schema.evaluatorPath();
			int phaseOffset = evaluatorPath.steps().size() + 2;
			String state = schema.state().toString();
			String truth = schema.truth().toString();
			String predicate = schema.predicate().toString();
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write L0 = " + schema.emptyList() +
					". The matched symbolic evaluator path rewrites " +
					evaluatorPath.source() + " in " + evaluatorPath.steps().size() +
					" steps to " + evaluatorPath.result() +
					". This path remains valid after substituting any Ln for its " +
					"list variable and therefore defines L(n+1).\n" +
					"The traversal and base rules imply " + predicate +
					LIST_TRAVERSAL_RESULT + truth + ". Consequently, for every " +
					"n >= 0, " + state + "(" + truth + ",Ln) ->^(n+" +
					phaseOffset + ") " + state + "(" + truth +
					",L(n+1)). Starting with L0 yields an infinite rewrite " +
					"sequence.\nThe first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO_RESULT +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

	/** Proof argument for a length-guarded list-growth schema. */
	private record LengthGuardedListGrowthArgument(
			LengthGuardedListGrowthWitness witness) implements Argument {

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
			LengthGuardedListGrowthSchema schema = this.witness.schema();
			EvaluatorPath evaluatorPath = schema.evaluatorPath();
			int phaseOffset = evaluatorPath.steps().size() + 6;
			String state = schema.state().toString();
			String truth = schema.truth().toString();
			String length = schema.length().toString();
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write L0 = " + schema.emptyList() +
					". The matched symbolic evaluator path rewrites " +
					evaluatorPath.source() + " in " + evaluatorPath.steps().size() +
					" steps to " + evaluatorPath.result() +
					" and remains valid after substituting any Ln for its list " +
					"variable; this defines L(n+1).\n" +
					"The matched length rules reduce each " + length +
					"(Ln) in n+1 steps. The equality traversal is then used n " +
					"times, with three fixed guard steps, so the guard reduces " +
					"to " + truth + " in 3n+5 steps. Consequently, for every " +
					"n >= 0, " + state + "(" + truth + ",Ln) ->^(3n+" +
					phaseOffset + ") " + state + "(" + truth +
					",L(n+1)). Starting with L0 yields an infinite rewrite " +
					"sequence.\nThe first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO_RESULT +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}
}
