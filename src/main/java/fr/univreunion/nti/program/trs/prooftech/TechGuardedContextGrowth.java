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

/**
 * Searches for a bounded guarded context-growth certificate.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechGuardedContextGrowth implements ProofTechnique {

	/** Message emitted when the bounded search remains inconclusive. */
	private static final String NOT_FOUND_MESSAGE =
			"No guarded context growth found!";

	/** Maximum number of rules handled by this bounded search. */
	private static final int MAX_RULE_COUNT = 200;

	/** Maximum number of constants used to ground active cores. */
	private static final int MAX_CONSTANT_COUNT = 16;

	/** Maximum number of initial ground cores considered. */
	private static final int MAX_CORE_SEED_COUNT = 512;

	/** Maximum number of core phases in one certificate. */
	private static final int MAX_CORE_PHASE_COUNT = 8;

	/** Maximum number of distinct cores retained from one initial core. */
	private static final int MAX_CORE_STATE_COUNT = 64;

	/** Maximum depth of one local ground derivation. */
	private static final int MAX_LOCAL_SEARCH_DEPTH = 8;

	/** Maximum number of states retained by one local search. */
	private static final int MAX_LOCAL_STATE_COUNT = 256;

	/** Maximum number of phase targets returned by one local search. */
	private static final int MAX_LOCAL_TARGET_COUNT = 32;

	/** Maximum number of states retained across the complete technique. */
	private static final int MAX_STATE_COUNT = 30_000;

	/** Maximum depth of a retained local term. */
	private static final int MAX_TERM_DEPTH = 64;

	/** Maximum rendered length of a retained local term. */
	private static final int MAX_TERM_LENGTH = 4_096;

	/** Runs the bounded guarded-growth search. */
	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose(
				"## Searching for bounded guarded context growth...");
		SearchSystem system = extractSystem(trs);
		if (system == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		List<Shell> shells = findShells(system.rules());
		if (shells.isEmpty()) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		SearchBudget budget = new SearchBudget();
		for (Shell shell : shells)
			for (Term initialCore : groundedActiveCores(
					system.rules(), system.constants(), shell.active())) {
				GrowthWitness witness = searchFrom(
						initialCore, shell, system.rulesByRoot(), budget);
				if (witness != null) {
					proof.printlnIfVerbose("Found guarded context growth!");
					proof.setResult(Proof.ProofResult.NO);
					proof.setArgument(new GuardedGrowthArgument(witness));
					return proof;
				}
				if (budget.stateCount >= MAX_STATE_COUNT) {
					proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
					return proof;
				}
			}
		proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
		return proof;
	}

	/** Extracts eligible rules, their root index and the available constants. */
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
		return new SearchSystem(
				List.copyOf(rules), rulesByRoot, List.copyOf(constants.values()));
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

	/** Finds all exact guarded transport shells in rule order. */
	private static List<Shell> findShells(List<NumberedRule> rules) {
		List<GuardTransition> guards = new ArrayList<>();
		Map<SymbolPair, NumberedRule> commutations = new LinkedHashMap<>();
		classifyShellRules(rules, guards, commutations);

		Map<String, Shell> shells = new LinkedHashMap<>();
		for (GuardTransition markedToProper : guards)
			for (GuardTransition okToActive : guards)
				addShells(
						markedToProper, okToActive, commutations, shells);
		return List.copyOf(shells.values());
	}

	/** Classifies rules which may participate in a guarded transport shell. */
	private static void classifyShellRules(
			List<NumberedRule> rules,
			List<GuardTransition> guards,
			Map<SymbolPair, NumberedRule> commutations) {
		for (NumberedRule rule : rules) {
			GuardTransition guard = parseGuardTransition(rule);
			if (guard != null)
				guards.add(guard);
			SymbolPair commutation = parseCommutation(rule.rule());
			if (commutation != null)
				commutations.putIfAbsent(commutation, rule);
		}
	}

	/** Adds all shells for one ordered pair of guarded transitions. */
	private static void addShells(
			GuardTransition markedToProper,
			GuardTransition okToActive,
			Map<SymbolPair, NumberedRule> commutations,
			Map<String, Shell> shells) {
		if (markedToProper.guard() != okToActive.guard())
			return;
		for (Map.Entry<SymbolPair, NumberedRule> entry : commutations.entrySet()) {
			Shell shell = buildShell(
					markedToProper, okToActive, entry, commutations);
			if (shell != null)
				shells.putIfAbsent(shell.key(), shell);
		}
	}

	/** Builds one complete shell from a possible marked-output rule. */
	private static Shell buildShell(
			GuardTransition markedToProper,
			GuardTransition okToActive,
			Map.Entry<SymbolPair, NumberedRule> entry,
			Map<SymbolPair, NumberedRule> commutations) {
		SymbolPair markedOut = entry.getKey();
		if (markedOut.second() != markedToProper.source())
			return null;
		FunctionSymbol pump = markedOut.first();
		NumberedRule properIn = commutations.get(new SymbolPair(
				markedToProper.target(), pump));
		NumberedRule okOut = commutations.get(new SymbolPair(
				pump, okToActive.source()));
		NumberedRule activeIn = commutations.get(new SymbolPair(
				okToActive.target(), pump));
		if (properIn == null || okOut == null || activeIn == null)
			return null;
		return new Shell(
				markedToProper.guard(), pump,
				okToActive.target(), markedToProper.source(),
				markedToProper.target(), okToActive.source(),
				entry.getValue(), properIn, okOut, activeIn,
				markedToProper.rule(), okToActive.rule());
	}

	/** Parses {@code G(F(x)) -> G(H(x))}. */
	private static GuardTransition parseGuardTransition(NumberedRule rule) {
		Function left = unaryFunction(rule.rule().getLeft());
		Function right = unaryFunction(rule.rule().getRight());
		if (left == null || right == null || left.getRootSymbol() != right.getRootSymbol())
			return null;
		Function leftChild = unaryFunction(left.getChild(0));
		Function rightChild = unaryFunction(right.getChild(0));
		if (leftChild == null || rightChild == null ||
				differentVariables(leftChild.getChild(0), rightChild.getChild(0)))
			return null;
		return new GuardTransition(
				left.getRootSymbol(), leftChild.getRootSymbol(),
				rightChild.getRootSymbol(), rule);
	}

	/** Parses {@code F(G(x)) -> G(F(x))}. */
	private static SymbolPair parseCommutation(RuleTrs rule) {
		Function left = unaryFunction(rule.getLeft());
		Function right = unaryFunction(rule.getRight());
		if (left == null || right == null)
			return null;
		Function leftChild = unaryFunction(left.getChild(0));
		Function rightChild = unaryFunction(right.getChild(0));
		if (leftChild == null || rightChild == null ||
				left.getRootSymbol() != rightChild.getRootSymbol() ||
				leftChild.getRootSymbol() != right.getRootSymbol() ||
				differentVariables(leftChild.getChild(0), rightChild.getChild(0)))
			return null;
		return new SymbolPair(left.getRootSymbol(), leftChild.getRootSymbol());
	}

	/** Returns the term as a unary function, or {@code null}. */
	private static Function unaryFunction(Term term) {
		return term instanceof Function function &&
				function.getRootSymbol().getArity() == 1 ? function : null;
	}

	/** Tests whether two positions do not contain the same variable object. */
	private static boolean differentVariables(Term first, Term second) {
		return first != second || !first.isVariable();
	}

	/** Grounds arguments of active left-hand sides in deterministic order. */
	private static List<Term> groundedActiveCores(
			List<NumberedRule> rules,
			List<Term> constants,
			FunctionSymbol active) {

		Map<String, Term> cores = new LinkedHashMap<>();
		for (NumberedRule numberedRule : rules) {
			Function left = numberedRule.rule().getLeft();
			if (left.getRootSymbol() != active)
				continue;
			if (left.isGround())
				addCore(left.getChild(0), cores);
			else
				for (Term constant : constants) {
					Function grounded = (Function) left.replaceVariables(constant);
					if (!addCore(grounded.getChild(0), cores))
						return List.copyOf(cores.values());
				}
		}
		return List.copyOf(cores.values());
	}

	/** Adds one distinct core while the seed bound permits it. */
	private static boolean addCore(Term core, Map<String, Term> cores) {
		if (cores.size() >= MAX_CORE_SEED_COUNT)
			return false;
		cores.putIfAbsent(core.toString(), core);
		return cores.size() < MAX_CORE_SEED_COUNT;
	}

	/** Searches the finite core graph for one context-growing cycle. */
	private static GrowthWitness searchFrom(
			Term initialCore,
			Shell shell,
			Map<FunctionSymbol, List<NumberedRule>> rulesByRoot,
			SearchBudget budget) {
		return new CoreSearch(initialCore, shell, rulesByRoot, budget).search();
	}

	/** Builds one unary application. */
	private static Term wrap(FunctionSymbol wrapper, Term argument) {
		return new Function(wrapper, List.of(argument));
	}

	/** One analyzed input rule and its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Extracted rules, root index and constants. */
	private record SearchSystem(
			List<NumberedRule> rules,
			Map<FunctionSymbol, List<NumberedRule>> rulesByRoot,
			List<Term> constants) {}

	/** An ordered pair of unary symbols. */
	private record SymbolPair(FunctionSymbol first, FunctionSymbol second) {}

	/** An exact transition under one unary guard. */
	private record GuardTransition(
			FunctionSymbol guard,
			FunctionSymbol source,
			FunctionSymbol target,
			NumberedRule rule) {}

	/** The six exact rules which transport phases through the pumping context. */
	private record Shell(
			FunctionSymbol guard,
			FunctionSymbol pump,
			FunctionSymbol active,
			FunctionSymbol marked,
			FunctionSymbol proper,
			FunctionSymbol ok,
			NumberedRule markedOut,
			NumberedRule properIn,
			NumberedRule okOut,
			NumberedRule activeIn,
			NumberedRule markedToProper,
			NumberedRule okToActive) {

		private String key() {
			return this.guard + "|" + this.pump + "|" + this.active + "|" +
					this.marked + "|" + this.proper + "|" + this.ok;
		}
	}

	/** One node of a local ground rewrite search. */
	private record SearchNode(
			Term term,
			SearchNode parent,
			NumberedRule rule,
			Position position,
			int depth) {}

	/** One checked local rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			NumberedRule rule,
			Position position) {}

	/** One complete local ground derivation. */
	private record RewritePath(
			Term source,
			Term target,
			List<RewriteStep> steps) {}

	/** One phase in the finite core graph. */
	private record CoreEdge(
			Term sourceCore,
			Term markedCore,
			Term targetCore,
			RewritePath activeToMarked,
			RewritePath properToOk) {}

	/** One node in the bounded core-graph search. */
	private record CoreNode(
			Term core,
			CoreNode parent,
			CoreEdge edge,
			int depth) {}

	/** Shared retained-state budget. */
	private static final class SearchBudget {
		private int stateCount;
	}

	/** State of one bounded search in the finite core graph. */
	private static final class CoreSearch {

		private final Term initialCore;
		private final Term pumpedInitialCore;
		private final Shell shell;
		private final Map<FunctionSymbol, List<NumberedRule>> rulesByRoot;
		private final SearchBudget budget;
		private final ArrayDeque<CoreNode> pending = new ArrayDeque<>();
		private final Set<String> visited = new HashSet<>();

		private CoreSearch(
				Term initialCore,
				Shell shell,
				Map<FunctionSymbol, List<NumberedRule>> rulesByRoot,
				SearchBudget budget) {
			this.initialCore = initialCore;
			this.pumpedInitialCore = wrap(shell.pump(), initialCore);
			this.shell = shell;
			this.rulesByRoot = rulesByRoot;
			this.budget = budget;
			this.pending.add(new CoreNode(initialCore, null, null, 0));
			this.visited.add(initialCore.toString());
		}

		/** Searches until a witness is found or a core bound is reached. */
		private GrowthWitness search() {
			while (!this.pending.isEmpty() &&
					this.visited.size() < MAX_CORE_STATE_COUNT &&
					this.budget.stateCount < MAX_STATE_COUNT) {
				CoreNode current = this.pending.remove();
				if (current.depth() < MAX_CORE_PHASE_COUNT) {
					GrowthWitness witness = expand(current);
					if (witness != null)
						return witness;
				}
			}
			return null;
		}

		/** Expands one core node in deterministic local-path order. */
		private GrowthWitness expand(CoreNode current) {
			for (RewritePath activePath : findTargets(
					wrap(this.shell.active(), current.core()), this.shell.marked())) {
				GrowthWitness witness = expand(current, activePath);
				if (witness != null)
					return witness;
			}
			return null;
		}

		/** Expands all proper-to-ok paths for one marked core. */
		private GrowthWitness expand(CoreNode current, RewritePath activePath) {
			Term markedCore = childOf(activePath.target());
			for (RewritePath properPath : findTargets(
					wrap(this.shell.proper(), markedCore), this.shell.ok())) {
				Term nextCore = childOf(properPath.target());
				CoreEdge edge = new CoreEdge(
						current.core(), markedCore, nextCore, activePath, properPath);
				CoreNode next = new CoreNode(
						nextCore, current, edge, current.depth() + 1);
				if (nextCore.deepEquals(this.pumpedInitialCore))
					return buildWitness(next);
				if (this.visited.add(nextCore.toString()))
					this.pending.add(next);
			}
			return null;
		}

		/** Finds bounded ground descendants with the requested unary root. */
		private List<RewritePath> findTargets(
				Term source, FunctionSymbol targetRoot) {
			return new LocalSearch(
					source, targetRoot, this.rulesByRoot, this.budget).search();
		}

		/** Returns the argument of a term known to be unary. */
		private static Term childOf(Term term) {
			return ((Function) term).getChild(0);
		}

		/** Reconstructs the successful core cycle. */
		private GrowthWitness buildWitness(CoreNode last) {
			List<CoreEdge> edges = new ArrayList<>();
			for (CoreNode node = last; node.parent() != null; node = node.parent())
				edges.add(node.edge());
			Collections.reverse(edges);
			return new GrowthWitness(
					this.initialCore, this.shell, List.copyOf(edges));
		}
	}

	/** State of one bounded local ground rewrite search. */
	private static final class LocalSearch {

		private final Term source;
		private final FunctionSymbol targetRoot;
		private final Map<FunctionSymbol, List<NumberedRule>> rulesByRoot;
		private final SearchBudget budget;
		private final ArrayDeque<SearchNode> pending = new ArrayDeque<>();
		private final Set<String> visited = new HashSet<>();
		private final Map<String, RewritePath> targets = new LinkedHashMap<>();

		private LocalSearch(
				Term source,
				FunctionSymbol targetRoot,
				Map<FunctionSymbol, List<NumberedRule>> rulesByRoot,
				SearchBudget budget) {
			this.source = source;
			this.targetRoot = targetRoot;
			this.rulesByRoot = rulesByRoot;
			this.budget = budget;
			this.pending.add(new SearchNode(source, null, null, null, 0));
			this.visited.add(source.toString());
			this.budget.stateCount++;
		}

		/** Searches until all local bounds or the frontier are exhausted. */
		private List<RewritePath> search() {
			while (!this.pending.isEmpty() &&
					this.visited.size() < MAX_LOCAL_STATE_COUNT &&
					this.budget.stateCount < MAX_STATE_COUNT &&
					this.targets.size() < MAX_LOCAL_TARGET_COUNT) {
				SearchNode current = this.pending.remove();
				if (current.depth() < MAX_LOCAL_SEARCH_DEPTH)
					expand(current);
			}
			return List.copyOf(this.targets.values());
		}

		/** Expands all rewrite positions of one local-search node. */
		private void expand(SearchNode current) {
			for (Position position : current.term())
				expand(current, position);
		}

		/** Expands all rules applicable at one local rewrite position. */
		private void expand(SearchNode current, Position position) {
			Term redex = current.term().get(position);
			if (!redex.isVariable()) {
				List<NumberedRule> candidates =
						this.rulesByRoot.get(redex.getRootSymbol());
				if (candidates != null)
					for (NumberedRule rule : candidates)
						addRewrite(current, position, redex, rule);
			}
		}

		/** Adds one matching rewrite to the target set or search frontier. */
		private void addRewrite(
				SearchNode current,
				Position position,
				Term redex,
				NumberedRule numberedRule) {
			Substitution substitution = new Substitution();
			RuleTrs rule = numberedRule.rule();
			if (!rule.getLeft().isMoreGeneralThan(redex, substitution))
				return;
			Term target = current.term().replace(
					position, rule.getRight().apply(substitution));
			SearchNode next = new SearchNode(
					target, current, numberedRule, position, current.depth() + 1);
			if (isGroundWrapper(target))
				this.targets.putIfAbsent(
						target.toString(), buildPath(next));
			else
				addSearchState(target, next);
		}

		/** Tests whether a term is a ground unary target wrapper. */
		private boolean isGroundWrapper(Term term) {
			Function function = unaryFunction(term);
			return function != null &&
					function.getRootSymbol() == this.targetRoot && term.isGround();
		}

		/** Reconstructs one local ground derivation. */
		private RewritePath buildPath(SearchNode last) {
			List<RewriteStep> steps = new ArrayList<>();
			for (SearchNode node = last; node.parent() != null; node = node.parent())
				steps.add(new RewriteStep(
						node.parent().term(), node.term(), node.rule(), node.position()));
			Collections.reverse(steps);
			return new RewritePath(
					this.source, last.term(), List.copyOf(steps));
		}

		/** Retains one bounded ground local-search state. */
		private void addSearchState(Term target, SearchNode next) {
			String key = target.toString();
			if (target.isGround() && target.depth() <= MAX_TERM_DEPTH &&
					key.length() <= MAX_TERM_LENGTH && this.visited.add(key)) {
				this.budget.stateCount++;
				this.pending.add(next);
			}
		}
	}

	/** A complete guarded context-growth certificate. */
	private record GrowthWitness(
			Term initialCore,
			Shell shell,
			List<CoreEdge> edges) {}

	/** Proof argument for a guarded context-growth certificate. */
	private record GuardedGrowthArgument(GrowthWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			StringBuilder details = new StringBuilder();
			appendShell(details, spaces, this.witness.shell());
			int phase = 1;
			for (CoreEdge edge : this.witness.edges()) {
				details.append('\n').append(spaces).append("Core phase ")
						.append(phase++).append(": ")
						.append(edge.sourceCore()).append(" -> ")
						.append(edge.targetCore()).append('\n');
				appendPath(details, spaces + "  ", edge.activeToMarked());
				details.append('\n');
				appendPath(details, spaces + "  ", edge.properToOk());
			}
			if (!details.isEmpty() && details.charAt(details.length() - 1) == '\n')
				details.setLength(details.length() - 1);
			return details.toString();
		}

		/** Appends the six syntactic shell rules. */
		private static void appendShell(
				StringBuilder details, String spaces, Shell shell) {
			details.append(spaces).append("Guarded transport shell:\n");
			appendRule(details, spaces, shell.markedOut());
			appendRule(details, spaces, shell.properIn());
			appendRule(details, spaces, shell.okOut());
			appendRule(details, spaces, shell.activeIn());
			appendRule(details, spaces, shell.markedToProper());
			appendRule(details, spaces, shell.okToActive());
		}

		/** Appends one numbered shell rule. */
		private static void appendRule(
				StringBuilder details, String spaces, NumberedRule rule) {
			details.append(spaces).append("  rule ").append(rule.number())
					.append(": ").append(rule.rule()).append('\n');
		}

		/** Appends all checked steps of one local path. */
		private static void appendPath(
				StringBuilder details, String spaces, RewritePath path) {
			for (RewriteStep step : path.steps())
				details.append(spaces).append(step.source()).append(" -> ")
						.append(step.target()).append(" (rule ")
						.append(step.rule().number()).append(", position ")
						.append(step.position()).append(")\n");
		}

		@Override
		public String getWitnessKind() {
			return "guarded context growth";
		}

		@Override
		public String toString() {
			Shell shell = this.witness.shell();
			Term core = this.witness.initialCore();
			Term initial = wrap(shell.guard(), wrap(shell.active(), core));
			Term successor = wrap(
					shell.guard(), wrap(shell.pump(), wrap(shell.active(), core)));
			return "* Technique: bounded guarded context-growth search\n" +
					"* Certificate: " + initial + " is non-terminating\n" +
					"* Description:\nFor every n >= 0, " + shell.guard() + "(" +
					shell.pump() + "^n(" + shell.active() + "(" + core + ")))" +
					" rewrites to the instance for n + 1.\n" +
					"In particular, " + initial + " starts the infinite sequence whose " +
					"next family member is " + successor + ".\n" + getDetails(0);
		}
	}
}
