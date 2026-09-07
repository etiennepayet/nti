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
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Searches a bounded ground context loop {@code s ->+ C[s]}.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechGroundContextLoop implements ProofTechnique {

	/** Maximum number of rules handled by this bounded search. */
	private static final int MAX_RULE_COUNT = 200;

	/** Maximum number of distinct constants used to ground candidate terms. */
	private static final int MAX_CONSTANT_COUNT = 16;

	/** Maximum number of ground left-hand sides used to ground candidates. */
	private static final int MAX_GROUND_LEFT_HAND_SIDE_COUNT = 16;

	/** Maximum number of grounded left-hand sides considered. */
	private static final int MAX_SEED_COUNT = 512;

	/** Maximum number of grounding terms used for mixed substitutions. */
	private static final int MAX_MIXED_GROUNDING_TERM_COUNT = 16;

	/** Maximum number of mixed ground seeds considered. */
	private static final int MAX_MIXED_SEED_COUNT = 256;

	/** Maximum number of independently grounded variables in a mixed seed. */
	private static final int MAX_MIXED_VARIABLE_COUNT = 3;

	/** Maximum search depth from one seed. */
	private static final int MAX_SEARCH_DEPTH = 16;

	/** Maximum number of distinct terms retained for one seed. */
	private static final int MAX_SEED_STATE_COUNT = 256;

	/** Maximum states for one seed grounded by a structured term. */
	private static final int MAX_STRUCTURED_SEED_STATE_COUNT = 1_024;

	/** Maximum number of distinct terms retained across all seeds. */
	private static final int MAX_STATE_COUNT = 30_000;

	/** Maximum depth of a retained descendant. */
	private static final int MAX_TERM_DEPTH = 64;

	/** Maximum rendered length of a retained descendant. */
	private static final int MAX_TERM_LENGTH = 4_096;

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
		proof.printlnIfVerbose("## Searching for a bounded ground context loop...");
		SearchSystem system = extractSystem(trs);
		if (system == null) {
			proof.printlnIfVerbose("No ground context loop found!");
			return proof;
		}

		SearchBudget budget = new SearchBudget();
		LoopWitness witness = searchSeeds(
				groundedLeftHandSides(system.rules(), system.constants()),
				system.rulesByRoot(), budget, MAX_SEED_STATE_COUNT, false);
		if (witness == null)
			witness = searchSeeds(enrichedGroundedLeftHandSides(system),
					system.rulesByRoot(), budget, MAX_STRUCTURED_SEED_STATE_COUNT,
					false);
		if (witness == null)
			witness = searchSeeds(mixedGroundedLeftHandSides(system),
					system.rulesByRoot(), new SearchBudget(),
					MAX_STRUCTURED_SEED_STATE_COUNT, true);
		if (witness != null) {
			proof.printlnIfVerbose("Found a ground context loop!");
			proof.setResult(Proof.ProofResult.NO);
			proof.setArgument(new GroundContextLoopArgument(witness));
		}
		else
			proof.printlnIfVerbose("No ground context loop found!");
		return proof;
	}

	/** Extracts eligible rules, their root index and their grounding terms. */
	private static SearchSystem extractSystem(Trs trs) {
		List<NumberedRule> rules = new ArrayList<>();
		Map<FunctionSymbol, List<NumberedRule>> rulesByRoot = new LinkedHashMap<>();
		Map<String, Term> constants = new LinkedHashMap<>();
		int ruleNumber = 1;
		for (RuleTrs rule : trs) {
			if (ruleNumber > MAX_RULE_COUNT)
				return null;
			if (!rule.isGeneralized()) {
				NumberedRule numberedRule = new NumberedRule(ruleNumber, rule);
				rules.add(numberedRule);
				rulesByRoot.computeIfAbsent(
						rule.getLeft().getRootSymbol(), ignored -> new ArrayList<>())
						.add(numberedRule);
			}
			collectConstants(rule.getLeft(), constants);
			collectConstants(rule.getRight(), constants);
			ruleNumber++;
		}
		if (rules.isEmpty() || constants.isEmpty())
			return null;

		Map<String, Term> groundingTerms = new LinkedHashMap<>(constants);
		collectGroundLeftHandSides(rules, groundingTerms);
		return new SearchSystem(rules, rulesByRoot,
				List.copyOf(constants.values()),
				List.copyOf(groundingTerms.values()),
				hasTriplicatedSiblingVariable(rules) ?
						mixedGroundingTerms(
								rules, List.copyOf(constants.values())) :
						List.of());
	}

	/** Collects the first bounded set of constants in prefix order. */
	private static void collectConstants(Term term, Map<String, Term> constants) {
		if (constants.size() >= MAX_CONSTANT_COUNT)
			return;
		term.forEachSubterm(subterm -> {
			if (constants.size() < MAX_CONSTANT_COUNT && !subterm.isVariable() &&
					subterm.getRootSymbol().getArity() == 0)
				constants.putIfAbsent(subterm.toString(), subterm);
		});
	}

	/** Appends a bounded set of ground left-hand sides in input order. */
	private static void collectGroundLeftHandSides(
			List<NumberedRule> rules,
			Map<String, Term> groundingTerms) {

		int count = 0;
		for (NumberedRule numberedRule : rules) {
			Term left = numberedRule.rule().getLeft();
			if (left.isGround() && !groundingTerms.containsKey(left.toString())) {
				groundingTerms.put(left.toString(), left);
				if (++count >= MAX_GROUND_LEFT_HAND_SIDE_COUNT)
					return;
			}
		}
	}

	/** Builds distinct ground instances of the analyzed left-hand sides. */
	private static List<Term> groundedLeftHandSides(
			List<NumberedRule> rules,
			List<Term> groundingTerms) {

		Map<String, Term> seeds = new LinkedHashMap<>();
		addUniformGroundInstances(rules, groundingTerms, seeds);
		return List.copyOf(seeds.values());
	}

	/** Builds only the seeds introduced by structured grounding terms. */
	private static List<Term> enrichedGroundedLeftHandSides(SearchSystem system) {
		Map<String, Term> historical = new LinkedHashMap<>();
		addUniformGroundInstances(system.rules(), system.constants(), historical);

		Map<String, Term> enriched = new LinkedHashMap<>();
		addUniformGroundInstances(
				system.rules(), system.groundingTerms(), enriched);
		enriched.keySet().removeAll(historical.keySet());
		return List.copyOf(enriched.values());
	}

	/** Collects bounded structured terms for heterogeneous substitutions. */
	private static List<Term> mixedGroundingTerms(
			List<NumberedRule> rules,
			List<Term> constants) {

		Map<String, Term> terms = new LinkedHashMap<>();
		for (NumberedRule numberedRule : rules) {
			Term right = numberedRule.rule().getRight();
			if (right.isGround())
				addMixedGroundingTerm(right, terms);
		}
		for (Term seed : groundedLeftHandSides(rules, constants))
			if (seed.getRootSymbol().getArity() > 0)
				addMixedGroundingTerm(seed, terms);
		for (Term constant : constants)
			addMixedGroundingTerm(constant, terms);
		return List.copyOf(terms.values());
	}

	/** Returns whether three sibling arguments are the same variable. */
	private static boolean hasTriplicatedSiblingVariable(
			List<NumberedRule> rules) {

		for (NumberedRule numberedRule : rules) {
			Term right = numberedRule.rule().getRight();
			for (Position position : right)
				if (hasTriplicatedSiblingVariable(right.get(position)))
					return true;
		}
		return false;
	}

	/** Checks one function term for three equal variable arguments. */
	private static boolean hasTriplicatedSiblingVariable(Term term) {
		int arity = term.isVariable() ? 0 : term.getRootSymbol().getArity();
		for (int i = 0; i < arity; i++) {
			Term argument = term.get(i);
			if (argument instanceof Variable variable) {
				int occurrenceCount = 1;
				for (int j = i + 1; j < arity; j++)
					if (term.get(j).deepEquals(variable) && ++occurrenceCount >= 3)
						return true;
			}
		}
		return false;
	}

	/** Adds one term while the mixed grounding-term bound permits it. */
	private static void addMixedGroundingTerm(
			Term term,
			Map<String, Term> terms) {

		if (terms.size() < MAX_MIXED_GROUNDING_TERM_COUNT)
			terms.putIfAbsent(term.toString(), term);
	}

	/** Builds bounded instances whose variables may receive distinct terms. */
	private static List<Term> mixedGroundedLeftHandSides(SearchSystem system) {
		Map<String, Term> uniform = new LinkedHashMap<>();
		addUniformGroundInstances(
				system.rules(), system.mixedGroundingTerms(), uniform);

		Map<String, Term> mixed = new LinkedHashMap<>();
		for (NumberedRule numberedRule : system.rules()) {
			List<Variable> variables = variablesInPrefixOrder(
					numberedRule.rule().getLeft());
			if (variables.size() > 1 &&
					variables.size() <= MAX_MIXED_VARIABLE_COUNT)
				addMixedGroundInstances(numberedRule.rule().getLeft(), variables,
						0, system.mixedGroundingTerms(), new Substitution(),
						uniform, mixed);
			if (mixed.size() >= MAX_MIXED_SEED_COUNT)
				break;
		}
		return List.copyOf(mixed.values());
	}

	/** Returns distinct variables in order of first occurrence. */
	private static List<Variable> variablesInPrefixOrder(Term term) {
		Set<Variable> variables = new LinkedHashSet<>();
		for (Position position : term) {
			Term subterm = term.get(position);
			if (subterm instanceof Variable variable)
				variables.add(variable);
		}
		return List.copyOf(variables);
	}

	/** Recursively enumerates bounded heterogeneous substitutions. */
	private static void addMixedGroundInstances(
			Term left,
			List<Variable> variables,
			int variableIndex,
			List<Term> groundingTerms,
			Substitution substitution,
			Map<String, Term> uniform,
			Map<String, Term> mixed) {

		if (mixed.size() >= MAX_MIXED_SEED_COUNT)
			return;
		if (variableIndex >= variables.size()) {
			Term seed = left.apply(substitution);
			String key = seed.toString();
			if (!uniform.containsKey(key))
				mixed.putIfAbsent(key, seed);
			return;
		}

		Variable variable = variables.get(variableIndex);
		for (Term groundingTerm : groundingTerms) {
			Substitution extended = new Substitution(substitution);
			extended.add(variable, groundingTerm);
			addMixedGroundInstances(left, variables, variableIndex + 1,
					groundingTerms, extended, uniform, mixed);
			if (mixed.size() >= MAX_MIXED_SEED_COUNT)
				return;
		}
	}

	/** Adds the historical same-term ground instances before enriched seeds. */
	private static void addUniformGroundInstances(
			List<NumberedRule> rules,
			List<Term> constants,
			Map<String, Term> seeds) {

		for (NumberedRule numberedRule : rules) {
			if (seeds.size() >= MAX_SEED_COUNT)
				return;
			Term left = numberedRule.rule().getLeft();
			if (left.isGround())
				seeds.putIfAbsent(left.toString(), left);
			else
				for (Term constant : constants) {
					Term seed = left.replaceVariables(constant);
					seeds.putIfAbsent(seed.toString(), seed);
					if (seeds.size() >= MAX_SEED_COUNT)
						return;
				}
		}
	}

	/** Searches seeds with breadth-first or goal-directed scheduling. */
	private static LoopWitness searchSeeds(
			List<Term> seeds,
			Map<FunctionSymbol, List<NumberedRule>> rulesByRoot,
			SearchBudget budget,
			int maxSeedStateCount,
			boolean goalDirected) {

		for (Term seed : seeds) {
			if (budget.stateCount >= MAX_STATE_COUNT)
				return null;
			LoopWitness witness = new GroundSearch(
					seed, rulesByRoot, budget, maxSeedStateCount,
					goalDirected).search();
			if (witness != null)
				return witness;
		}
		return null;
	}

	/** One analyzed rule together with its one-based input position. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Immutable data extracted from the TRS. */
	private record SearchSystem(
			List<NumberedRule> rules,
			Map<FunctionSymbol, List<NumberedRule>> rulesByRoot,
			List<Term> constants,
			List<Term> groundingTerms,
			List<Term> mixedGroundingTerms) {}

	/** One node of a bounded seed search. */
	private record SearchNode(
			Term term,
			SearchNode parent,
			NumberedRule rule,
			Position position,
			int depth,
			int priority,
			long insertionOrder) {}

	/** Mutable budget shared by all seed searches. */
	private static final class SearchBudget {
		private int stateCount;
	}

	/** Mutable state of the breadth-first search from one ground seed. */
	private static final class GroundSearch {

		/** The term whose embedded occurrence constitutes a loop. */
		private final Term seed;

		/** Eligible rules indexed by their left root symbol. */
		private final Map<FunctionSymbol, List<NumberedRule>> rulesByRoot;

		/** The budget shared by all seed searches. */
		private final SearchBudget budget;

		/** Maximum number of states retained for this seed. */
		private final int maxSeedStateCount;

		/** Whether descendants are scheduled by distance to the seed. */
		private final boolean goalDirected;

		/** Nodes waiting for expansion in the selected order. */
		private final Queue<SearchNode> pending;

		/** Next stable insertion order for the prioritized queue. */
		private long nextInsertionOrder;

		/** Canonical renderings already reached from this seed. */
		private final Set<String> visited = new HashSet<>();

		/** Builds the search state and inserts its root node. */
		private GroundSearch(
				Term seed,
				Map<FunctionSymbol, List<NumberedRule>> rulesByRoot,
				SearchBudget budget,
				int maxSeedStateCount,
				boolean goalDirected) {

			this.seed = seed;
			this.rulesByRoot = rulesByRoot;
			this.budget = budget;
			this.maxSeedStateCount = maxSeedStateCount;
			this.goalDirected = goalDirected;
			this.pending = goalDirected ? new PriorityQueue<>(
					Comparator.comparingInt(SearchNode::priority)
							.thenComparingInt(SearchNode::depth)
							.thenComparingLong(SearchNode::insertionOrder)) :
					new ArrayDeque<>();
			this.pending.add(new SearchNode(seed, null, null, null, 0, 0,
					this.nextInsertionOrder++));
			this.visited.add(seed.toString());
			this.budget.stateCount++;
		}

		/** Runs the bounded search in the configured scheduling order. */
		private LoopWitness search() {
			while (hasPendingWork()) {
				SearchNode current = this.pending.remove();
				if (current.depth() < MAX_SEARCH_DEPTH) {
					LoopWitness witness = expand(current);
					if (witness != null)
						return witness;
				}
			}
			return null;
		}

		/** Expands one node at each of its positions. */
		private LoopWitness expand(SearchNode current) {
			for (Position position : current.term()) {
				LoopWitness witness = expandAtPosition(current, position);
				if (witness != null || !hasCapacity())
					return witness;
			}
			return null;
		}

		/** Expands one node with all rules eligible at one position. */
		private LoopWitness expandAtPosition(SearchNode current, Position position) {
			Term redex = current.term().get(position);
			if (redex.isVariable())
				return null;

			List<NumberedRule> candidates = this.rulesByRoot.get(redex.getRootSymbol());
			if (candidates == null)
				return null;

			for (NumberedRule rule : candidates) {
				LoopWitness witness = apply(current, position, redex, rule);
				if (witness != null || !hasCapacity())
					return witness;
			}
			return null;
		}

		/** Applies one matching rule and records an admissible descendant. */
		private LoopWitness apply(
				SearchNode current,
				Position position,
				Term redex,
				NumberedRule numberedRule) {

			Substitution substitution = new Substitution();
			RuleTrs rule = numberedRule.rule();
			if (!rule.getLeft().isMoreGeneralThan(redex, substitution))
				return null;

			Term target = current.term().replace(
					position, rule.getRight().apply(substitution));
			SearchNode next = new SearchNode(target, current, numberedRule,
					position, current.depth() + 1, priorityOf(target),
					this.nextInsertionOrder++);
			Position occurrence = occurrenceOf(target);
			if (occurrence != null)
				return buildWitness(occurrence, next);

			retain(target, next);
			return null;
		}

		/** Retains one bounded, previously unseen descendant. */
		private void retain(Term target, SearchNode node) {
			String key = target.toString();
			if (target.depth() <= MAX_TERM_DEPTH && key.length() <= MAX_TERM_LENGTH &&
					this.visited.add(key)) {
				this.budget.stateCount++;
				this.pending.add(node);
			}
		}

		/** Returns the goal-directed priority of one retained term. */
		private int priorityOf(Term term) {
			return this.goalDirected ? structuralDistance(term, this.seed) : 0;
		}

		/** Computes a simple structural mismatch distance. */
		private static int structuralDistance(Term left, Term right) {
			if (left.deepEquals(right))
				return 0;
			if (left.isVariable() || right.isVariable())
				return 1;

			FunctionSymbol leftRoot = left.getRootSymbol();
			FunctionSymbol rightRoot = right.getRootSymbol();
			int leftArity = leftRoot.getArity();
			int rightArity = rightRoot.getArity();
			int distance = leftRoot == rightRoot ? 0 : 2;
			int sharedArity = Math.min(leftArity, rightArity);
			for (int i = 0; i < sharedArity; i++)
				distance += structuralDistance(left.get(i), right.get(i));
			return distance + Math.abs(leftArity - rightArity);
		}

		/** Returns the first structural occurrence of the seed in a term. */
		private Position occurrenceOf(Term term) {
			for (Position position : term)
				if (term.get(position).deepEquals(this.seed))
					return position;
			return null;
		}

		/** Reconstructs the successful derivation. */
		private LoopWitness buildWitness(Position occurrence, SearchNode last) {
			List<LoopStep> steps = new ArrayList<>();
			for (SearchNode node = last; node.parent() != null; node = node.parent())
				steps.add(new LoopStep(node.parent().term(), node.term(),
						node.rule().number(), node.position()));
			Collections.reverse(steps);
			return new LoopWitness(
					this.seed, last.term(), occurrence, List.copyOf(steps));
		}

		/** Returns whether another node can be expanded. */
		private boolean hasPendingWork() {
			return !this.pending.isEmpty() && hasCapacity();
		}

		/** Returns whether the local and shared state bounds permit more work. */
		private boolean hasCapacity() {
			return this.visited.size() < this.maxSeedStateCount &&
					this.budget.stateCount < MAX_STATE_COUNT;
		}
	}

	/** One certified rewrite step. */
	private record LoopStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** A complete ground context-loop certificate. */
	private record LoopWitness(
			Term seed,
			Term result,
			Position occurrence,
			List<LoopStep> steps) {}

	/** Proof argument built from a certified ground context loop. */
	private record GroundContextLoopArgument(LoopWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			StringBuilder details = new StringBuilder();
			int stepNumber = 1;
			for (LoopStep step : this.witness.steps()) {
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
			return "ground context loop";
		}

		@Override
		public String toString() {
			return "* Technique: bounded ground context-loop search\n" +
					"* Certificate: " + this.witness.seed() + " is non-terminating\n" +
					"* Description:\n" + this.witness.seed() + " rewrites in " +
					this.witness.steps().size() + " steps to\n" +
					this.witness.result() + ".\nThe latter contains " +
					this.witness.seed() + " at position " + this.witness.occurrence() +
					". Repeating the derivation in that embedded occurrence yields " +
					"an infinite rewrite sequence.\n" + getDetails(0);
		}
	}
}
