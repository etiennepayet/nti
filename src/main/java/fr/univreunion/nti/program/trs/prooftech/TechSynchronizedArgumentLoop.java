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
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.Parameters;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.UnfoldedRuleTrs;
import fr.univreunion.nti.program.trs.ruleunfolding.unit.UnfoldedRuleTrsUnit;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Searches for a bounded instantiation loop obtained by unfolding two
 * symmetric arguments of a recursive rule in lockstep.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechSynchronizedArgumentLoop implements ProofTechnique {

	/** Maximum number of rules handled by this bounded search. */
	private static final int MAX_RULE_COUNT = 200;

	/** Maximum number of synchronized backward-unfolding phases. */
	private static final int MAX_BACKWARD_PHASE_COUNT = 6;

	/** Maximum number of synchronized forward-unfolding phases. */
	private static final int MAX_FORWARD_PHASE_COUNT = 2;

	/** Maximum number of unfolded relations retained by the technique. */
	private static final int MAX_STATE_COUNT = 8_192;

	/** Maximum depth of a retained unfolded relation. */
	private static final int MAX_RULE_DEPTH = 24;

	/** Maximum rendered length of a retained unfolded relation. */
	private static final int MAX_RULE_LENGTH = 8_192;

	/** Runs the bounded synchronized-argument search. */
	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose(
				"## Searching for a bounded synchronized argument loop...");
		SearchSystem system = extractSystem(trs);
		if (system == null) {
			proof.printlnIfVerbose("No synchronized argument loop found!");
			return proof;
		}

		SearchBudget budget = new SearchBudget();
		for (NumberedRule recursiveRule : system.rules()) {
			if (isSymmetricRecursiveRule(recursiveRule.rule())) {
				LoopWitness witness = search(recursiveRule, system, budget);
				if (witness != null) {
					proof.printlnIfVerbose("Found a synchronized argument loop!");
					proof.setResult(Proof.ProofResult.NO);
					proof.setArgument(new SynchronizedArgumentLoopArgument(witness));
					return proof;
				}
			}
			if (budget.stateCount >= MAX_STATE_COUNT)
				break;
		}
		proof.printlnIfVerbose("No synchronized argument loop found!");
		return proof;
	}

	/** Extracts eligible rules and indexes their two unfolding directions. */
	private static SearchSystem extractSystem(Trs trs) {
		List<NumberedRule> rules = new ArrayList<>();
		Map<FunctionSymbol, List<NumberedRule>> forwardRules = new LinkedHashMap<>();
		Map<FunctionSymbol, List<NumberedRule>> backwardRules = new LinkedHashMap<>();
		List<NumberedRule> variableRightRules = new ArrayList<>();
		int ruleNumber = 1;
		for (RuleTrs rule : trs) {
			if (ruleNumber > MAX_RULE_COUNT)
				return null;
			if (!rule.isGeneralized()) {
				NumberedRule numberedRule = new NumberedRule(ruleNumber, rule);
				rules.add(numberedRule);
				forwardRules.computeIfAbsent(
						rule.getLeft().getRootSymbol(), ignored -> new ArrayList<>())
						.add(numberedRule);
				if (rule.getRight().isVariable())
					variableRightRules.add(numberedRule);
				else
					backwardRules.computeIfAbsent(
							rule.getRight().getRootSymbol(), ignored -> new ArrayList<>())
							.add(numberedRule);
			}
			ruleNumber++;
		}
		if (rules.isEmpty())
			return null;
		return new SearchSystem(
				List.copyOf(rules), forwardRules, backwardRules,
				List.copyOf(variableRightRules));
	}

	/** Tests the exact two-argument symmetry required by this technique. */
	private static boolean isSymmetricRecursiveRule(RuleTrs rule) {
		if (rule.isGeneralized() || !(rule.getRight() instanceof Function right) ||
				rule.getLeft().getRootSymbol() != right.getRootSymbol() ||
				rule.getLeft().getRootSymbol().getArity() != 2)
			return false;

		Term leftFirst = rule.getLeft().getChild(0);
		Term leftSecond = rule.getLeft().getChild(1);
		Term rightFirst = right.getChild(0);
		Term rightSecond = right.getChild(1);
		return !leftFirst.isVariable() && !rightFirst.isVariable() &&
				leftFirst.isVariantOf(leftSecond) &&
				rightFirst.isVariantOf(rightSecond) &&
				relationKey(leftFirst, rightFirst).equals(
						relationKey(leftSecond, rightSecond));
	}

	/** Builds a variable-renaming-invariant key for one argument relation. */
	private static String relationKey(Term left, Term right) {
		Map<Variable, String> variables = new HashMap<>();
		return left.toString(variables, false) + " -> " +
				right.toString(variables, false);
	}

	/** Searches the bounded synchronized unfolding graph of one rule. */
	private static LoopWitness search(
			NumberedRule recursiveRule,
			SearchSystem system,
			SearchBudget budget) {

		RuleTrs copy = recursiveRule.rule().deepCopy();
		UnfoldedRuleTrsUnit initial = new UnfoldedRuleTrsUnit(
				copy.getLeft(), copy.getRight(), 0, null,
				List.of(recursiveRule.rule()));
		SearchNode root = new SearchNode(
				initial, List.of(), List.of(), 0, 0, false);
		ArrayDeque<SearchNode> pending = new ArrayDeque<>();
		Set<String> visited = new HashSet<>();
		pending.add(root);
		visited.add(stateKey(root));
		budget.stateCount++;
		Parameters parameters = new Parameters();

		while (!pending.isEmpty() && budget.stateCount < MAX_STATE_COUNT) {
			SearchNode current = pending.remove();
			LoopWitness witness = certify(recursiveRule, current);
			if (witness != null)
				return witness;

			if (current.forwardDepth() < MAX_FORWARD_PHASE_COUNT)
				retainAll(expandForwards(current, system, parameters),
						pending, visited, budget);
			if (!current.forwardOnly() &&
					current.backwardDepth() < MAX_BACKWARD_PHASE_COUNT)
				retainAll(expandBackwards(current, system, parameters),
						pending, visited, budget);
		}
		return null;
	}

	/** Generates all synchronized forward unfoldings of one relation. */
	private static List<SearchNode> expandForwards(
			SearchNode node,
			SearchSystem system,
			Parameters parameters) {

		List<SearchNode> result = new ArrayList<>();
		Function right = (Function) node.rule().getRight();
		for (Position relative : right.getChild(0)) {
			Term redex = right.getChild(0).get(relative);
			if (redex.isVariable())
				continue;
			List<NumberedRule> candidates =
					system.forwardRules().get(redex.getRootSymbol());
			if (candidates != null)
				for (NumberedRule candidate : candidates) {
					SearchNode successor = unfoldForwards(
							node, candidate, relative, parameters);
					if (successor != null)
						result.add(successor);
				}
		}
		return result;
	}

	/** Applies one forward unfolding to both symmetric arguments. */
	private static SearchNode unfoldForwards(
			SearchNode node,
			NumberedRule candidate,
			Position relative,
			Parameters parameters) {

		Position firstPosition = relative.addFirst(0);
		Position secondPosition = relative.addFirst(1);
		int iteration = node.backwardDepth() + node.forwardDepth() + 1;
		UnfoldedRuleTrsUnit first = unfoldOne(
				node.rule().unfoldForwardsWith(
						parameters, candidate.rule(), firstPosition,
						iteration));
		if (first == null)
			return null;
		UnfoldedRuleTrsUnit second = unfoldOne(
				first.unfoldForwardsWith(
						parameters, candidate.rule(), secondPosition,
						iteration));
		if (second == null || hasAsymmetricSides(second))
			return null;

		List<UnfoldingAction> suffix = new ArrayList<>(node.forwardActions());
		suffix.add(new UnfoldingAction(candidate, firstPosition));
		suffix.add(new UnfoldingAction(candidate, secondPosition));
		return new SearchNode(
				second, node.backwardActions(), List.copyOf(suffix),
				node.backwardDepth(), node.forwardDepth() + 1, true);
	}

	/** Generates all synchronized backward unfoldings of one relation. */
	private static List<SearchNode> expandBackwards(
			SearchNode node,
			SearchSystem system,
			Parameters parameters) {

		List<SearchNode> result = new ArrayList<>();
		Function left = node.rule().getLeft();
		for (Position relative : left.getChild(0)) {
			Term redex = left.getChild(0).get(relative);
			if (redex.isVariable())
				continue;
			for (NumberedRule candidate : backwardCandidates(redex, system)) {
				SearchNode successor = unfoldBackwards(
						node, candidate, relative, parameters);
				if (successor != null)
					result.add(successor);
			}
		}
		return result;
	}

	/** Returns possible backward rules in their original input order. */
	private static List<NumberedRule> backwardCandidates(
			Term redex,
			SearchSystem system) {

		List<NumberedRule> candidates = new ArrayList<>(system.variableRightRules());
		List<NumberedRule> rooted =
				system.backwardRules().get(redex.getRootSymbol());
		if (rooted != null)
			candidates.addAll(rooted);
		candidates.sort(Comparator.comparingInt(NumberedRule::number));
		return candidates;
	}

	/** Applies one backward unfolding to both symmetric arguments. */
	private static SearchNode unfoldBackwards(
			SearchNode node,
			NumberedRule candidate,
			Position relative,
			Parameters parameters) {

		Position firstPosition = relative.addFirst(0);
		Position secondPosition = relative.addFirst(1);
		UnfoldedRuleTrsUnit first = unfoldOne(
				node.rule().unfoldBackwardsWith(
						parameters, candidate.rule(), firstPosition,
						node.backwardDepth() + 1));
		if (first == null)
			return null;
		UnfoldedRuleTrsUnit second = unfoldOne(
				first.unfoldBackwardsWith(
						parameters, candidate.rule(), secondPosition,
						node.backwardDepth() + 1));
		if (second == null || hasAsymmetricSides(second))
			return null;

		List<UnfoldingAction> prefix = new ArrayList<>();
		prefix.add(new UnfoldingAction(candidate, secondPosition));
		prefix.add(new UnfoldingAction(candidate, firstPosition));
		prefix.addAll(node.backwardActions());
		return new SearchNode(
				second, List.copyOf(prefix), node.forwardActions(),
				node.backwardDepth() + 1, node.forwardDepth(), false);
	}

	/** Returns the sole unit unfolding result, or {@code null}. */
	private static UnfoldedRuleTrsUnit unfoldOne(
			Collection<UnfoldedRuleTrs> unfolded) {
		if (unfolded.isEmpty())
			return null;
		return (UnfoldedRuleTrsUnit) unfolded.iterator().next();
	}

	/** Tests whether either side no longer has symmetric arguments. */
	private static boolean hasAsymmetricSides(UnfoldedRuleTrsUnit rule) {
		if (!(rule.getRight() instanceof Function right) ||
				rule.getLeft().getRootSymbol().getArity() != 2 ||
				right.getRootSymbol().getArity() != 2)
			return true;
		return !rule.getLeft().getChild(0).isVariantOf(rule.getLeft().getChild(1)) ||
				!right.getChild(0).isVariantOf(right.getChild(1));
	}

	/** Retains bounded, previously unseen successors. */
	private static void retainAll(
			List<SearchNode> successors,
			ArrayDeque<SearchNode> pending,
			Set<String> visited,
			SearchBudget budget) {

		for (SearchNode successor : successors) {
			String rendering = successor.rule().toString();
			String key = stateKey(successor);
			if (successor.rule().depth() <= MAX_RULE_DEPTH &&
					rendering.length() <= MAX_RULE_LENGTH && visited.add(key)) {
				pending.add(successor);
				budget.stateCount++;
				if (budget.stateCount >= MAX_STATE_COUNT)
					return;
			}
		}
	}

	/** Builds a canonical state key modulo variable renaming. */
	private static String stateKey(SearchNode node) {
		return relationKey(node.rule().getLeft(), node.rule().getRight()) + '|' +
				node.forwardOnly() + '|' + node.backwardDepth() + '|' +
				node.forwardDepth();
	}

	/** Checks semi-unification and validates the complete rewrite replay. */
	private static LoopWitness certify(
			NumberedRule recursiveRule,
			SearchNode node) {

		Substitution semiunifier = new Substitution();
		Substitution matcher = new Substitution();
		if (!node.rule().getLeft().leftUnifyWith(
				node.rule().getRight(), semiunifier, matcher))
			return null;

		Term seed = node.rule().getLeft().apply(semiunifier);
		Term expected = node.rule().getRight().apply(semiunifier);
		List<UnfoldingAction> actions = new ArrayList<>(node.backwardActions());
		actions.add(new UnfoldingAction(recursiveRule, new Position()));
		actions.addAll(node.forwardActions());
		List<RewriteStep> steps = replay(seed, actions);
		if (steps == null || steps.isEmpty())
			return null;
		Term result = steps.getLast().target();
		if (!result.deepEquals(expected) ||
				!result.deepEquals(seed.apply(matcher)))
			return null;
		return new LoopWitness(
				seed, result, semiunifier, matcher, List.copyOf(steps));
	}

	/** Replays every unfolding action as an original TRS rewrite step. */
	private static List<RewriteStep> replay(
			Term seed,
			List<UnfoldingAction> actions) {

		List<RewriteStep> steps = new ArrayList<>();
		Term current = seed;
		for (UnfoldingAction action : actions) {
			Term redex = current.get(action.position());
			Substitution substitution = new Substitution();
			RuleTrs rule = action.rule().rule();
			if (!rule.getLeft().isMoreGeneralThan(redex, substitution))
				return null;
			Term target = current.replace(
					action.position(), rule.getRight().apply(substitution));
			steps.add(new RewriteStep(
					current, target, action.rule().number(), action.position()));
			current = target;
		}
		return steps;
	}

	/** One analyzed input rule and its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Rules and direction-specific root indexes. */
	private record SearchSystem(
			List<NumberedRule> rules,
			Map<FunctionSymbol, List<NumberedRule>> forwardRules,
			Map<FunctionSymbol, List<NumberedRule>> backwardRules,
			List<NumberedRule> variableRightRules) {}

	/** One unfolding action together with its replay position. */
	private record UnfoldingAction(NumberedRule rule, Position position) {}

	/** One node of the synchronized unfolding graph. */
	private record SearchNode(
			UnfoldedRuleTrsUnit rule,
			List<UnfoldingAction> backwardActions,
			List<UnfoldingAction> forwardActions,
			int backwardDepth,
			int forwardDepth,
			boolean forwardOnly) {}

	/** Mutable state budget shared by all recursive-rule searches. */
	private static final class SearchBudget {
		private int stateCount;
	}

	/** One certified original-TRS rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** A complete instantiation-loop certificate. */
	private record LoopWitness(
			Term seed,
			Term result,
			Substitution semiunifier,
			Substitution matcher,
			List<RewriteStep> steps) {}

	/** Proof argument built from a replayed synchronized argument loop. */
	private record SynchronizedArgumentLoopArgument(LoopWitness witness)
			implements Argument {

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
			return "synchronized argument loop";
		}

		@Override
		public String toString() {
			Map<Variable, String> variables = new HashMap<>();
			return "* Technique: bounded synchronized argument-loop search\n" +
					"* Certificate: " + this.witness.seed().toString(variables, false) +
					" is non-terminating\n* Description:\n" +
					this.witness.seed().toString(variables, false) + " rewrites in " +
					this.witness.steps().size() + " steps to\n" +
					this.witness.result().toString(variables, false) + ".\n" +
					"The latter is the image of the starting term by the matcher " +
					this.witness.matcher().toString(variables) +
					" (semiunifier " +
					this.witness.semiunifier().toString(variables) +
					"). Iterating this instantiated derivation yields an infinite " +
					"rewrite sequence.\n" + getDetails(0);
		}
	}
}
