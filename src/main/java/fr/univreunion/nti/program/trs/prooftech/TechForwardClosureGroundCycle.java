/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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
import java.util.HashMap;
import java.util.List;
import java.util.Map;

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
 * Searches bounded forward closures of a linear symbol-preserving rule for a
 * replayable ground cycle.
 *
 * @author <A HREF="mailto:etiennepayet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechForwardClosureGroundCycle implements ProofTechnique {

	/** Maximum size of the source of a retained forward closure. */
	private static final int MAX_SOURCE_SIZE = 40;

	/** Maximum number of rewrite steps in a retained forward closure. */
	private static final int MAX_STEP_COUNT = 20;

	/** Maximum number of closure states inspected. */
	private static final int MAX_STATE_COUNT = 50_000;

	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose(
				"## Searching for a bounded forward-closure ground cycle...");
		NumberedRule rule = eligibleRule(trs);
		GroundCycleWitness witness = rule == null ? null : search(rule);
		if (witness == null) {
			proof.printlnIfVerbose("No forward-closure ground cycle found!");
			return proof;
		}

		proof.printlnIfVerbose("Found a forward-closure ground cycle!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(new ForwardClosureGroundCycleArgument(witness));
		return proof;
	}

	/** Selects the supported natural class of single-rule systems. */
	private static NumberedRule eligibleRule(Trs trs) {
		RuleTrs onlyRule = null;
		for (RuleTrs rule : trs) {
			if (onlyRule != null)
				return null;
			onlyRule = rule;
		}
		if (onlyRule == null || isNonLinear(onlyRule.getLeft()) ||
				isNonLinear(onlyRule.getRight()) ||
				!onlyRule.getLeft().getVariables().equals(
						onlyRule.getRight().getVariables()) ||
				!symbolOccurrences(onlyRule.getLeft()).equals(
						symbolOccurrences(onlyRule.getRight())) ||
				termSize(onlyRule.getLeft()) > MAX_SOURCE_SIZE)
			return null;
		return new NumberedRule(1, onlyRule);
	}

	/** Returns whether some variable does not occur exactly once. */
	private static boolean isNonLinear(Term term) {
		Map<Variable, Integer> occurrences = new HashMap<>();
		term.getVariableOccurrences(occurrences);
		return occurrences.values().stream().anyMatch(count -> count != 1);
	}

	/** Counts each function-symbol occurrence, including constants. */
	private static Map<FunctionSymbol, Integer> symbolOccurrences(Term term) {
		Map<FunctionSymbol, Integer> occurrences = new HashMap<>();
		term.forEachSubterm(subterm -> {
			if (!subterm.isVariable())
				occurrences.merge(subterm.getRootSymbol(), 1, Integer::sum);
		});
		return occurrences;
	}

	/** Starts the bounded depth-first forward-closure search. */
	private static GroundCycleWitness search(NumberedRule rule) {
		RuleTrs initialRule = rule.rule().deepCopy();
		ClosureState initial = new ClosureState(
				initialRule.getLeft(), initialRule.getRight(), new Position(),
				List.of(new ClosureAction(rule, new Position())));
		SearchBudget budget = new SearchBudget();
		return search(rule, initial, budget);
	}

	/** Searches below one closure state in deterministic position order. */
	private static GroundCycleWitness search(
			NumberedRule rule,
			ClosureState state,
			SearchBudget budget) {

		if (Thread.currentThread().isInterrupted() ||
				++budget.stateCount > MAX_STATE_COUNT)
			return null;
		GroundCycleWitness witness = certify(state);
		if (witness != null)
			return witness;
		if (state.actions().size() >= MAX_STEP_COUNT)
			return null;

		for (Position position : state.target()) {
			if (Thread.currentThread().isInterrupted() ||
					budget.stateCount >= MAX_STATE_COUNT)
				return null;
			ClosureState successor = successor(rule, state, position);
			if (successor != null) {
				witness = search(rule, successor, budget);
				if (witness != null)
					return witness;
			}
		}
		return null;
	}

	/** Builds one most-general forward-closure extension. */
	private static ClosureState successor(
			NumberedRule rule,
			ClosureState state,
			Position position) {

		Term selected = state.target().get(position);
		if (selected.isVariable())
			return null;
		RuleTrs freshRule = rule.rule().deepCopy();
		if (!isCanonicalExtension(
				position, state.lastPosition(), freshRule.getLeft()))
			return null;
		Substitution unifier = new Substitution();
		if (!selected.isUnifiableWith(freshRule.getLeft(), unifier))
			return null;

		Term source = state.source().apply(unifier);
		if (termSize(source) > MAX_SOURCE_SIZE)
			return null;
		Term target = state.target().apply(unifier).replace(
				position, freshRule.getRight().apply(unifier));
		List<ClosureAction> actions = new ArrayList<>(state.actions());
		actions.add(new ClosureAction(rule, position));
		return new ClosureState(
				source, target, position, List.copyOf(actions));
	}

	/**
	 * Applies the standard forward-closure pruning: extensions to the left of
	 * the preceding redex and extensions below its linear variables are skipped.
	 */
	private static boolean isCanonicalExtension(
			Position position,
			Position lastPosition,
			Term left) {

		if (isIndependentAndSmaller(position, lastPosition))
			return false;
		Position suffix = suffixWhenPrefix(position, lastPosition);
		return suffix == null || !hasLinearVariableAbove(left, suffix);
	}

	/** Returns whether the first position is independently left of the second. */
	private static boolean isIndependentAndSmaller(
			Position first,
			Position second) {

		List<Integer> firstElements = elements(first);
		List<Integer> secondElements = elements(second);
		int commonLength = Math.min(firstElements.size(), secondElements.size());
		for (int index = 0; index < commonLength; index++) {
			int firstElement = firstElements.get(index);
			int secondElement = secondElements.get(index);
			if (firstElement != secondElement)
				return firstElement < secondElement;
		}
		return false;
	}

	/** Returns the second position's suffix when the first is its prefix. */
	private static Position suffixWhenPrefix(
			Position prefix,
			Position position) {

		List<Integer> prefixElements = elements(prefix);
		List<Integer> positionElements = elements(position);
		if (prefixElements.size() > positionElements.size())
			return null;
		for (int index = 0; index < prefixElements.size(); index++)
			if (!prefixElements.get(index).equals(positionElements.get(index)))
				return null;
		Position suffix = new Position();
		for (int index = prefixElements.size();
				index < positionElements.size(); index++)
			suffix = suffix.addLast(positionElements.get(index));
		return suffix;
	}

	/** Tests whether a linear variable of the term lies strictly above a path. */
	private static boolean hasLinearVariableAbove(Term term, Position position) {
		Term current = term;
		Map<Variable, Integer> occurrences = new HashMap<>();
		term.getVariableOccurrences(occurrences);
		for (int child : position) {
			if (current instanceof Variable variable)
				return occurrences.getOrDefault(variable, 0) == 1;
			current = current.get(child);
			if (current == null)
				return false;
		}
		return false;
	}

	/** Converts a position to an index list. */
	private static List<Integer> elements(Position position) {
		List<Integer> elements = new ArrayList<>();
		position.forEach(elements::add);
		return elements;
	}

	/** Counts all positions of a term. */
	private static int termSize(Term term) {
		int[] size = {0};
		term.forEachSubterm(ignored -> size[0]++);
		return size[0];
	}

	/** Closes a forward derivation with a ground unifier and replays it. */
	private static GroundCycleWitness certify(ClosureState state) {
		Substitution unifier = new Substitution();
		if (!state.source().isUnifiableWith(state.target(), unifier))
			return null;
		Term seed = state.source().apply(unifier);
		Term expected = state.target().apply(unifier);
		if (!seed.isGround() || !seed.deepEquals(expected))
			return null;
		List<RewriteStep> steps = replay(seed, state.actions());
		if (steps == null || steps.isEmpty())
			return null;
		Term result = steps.getLast().target();
		return result.deepEquals(seed) && result.deepEquals(expected) ?
				new GroundCycleWitness(
						state.source(), state.target(), seed,
						unifier, List.copyOf(steps)) : null;
	}

	/** Replays every closure action as an original-TRS rewrite step. */
	private static List<RewriteStep> replay(
			Term seed,
			List<ClosureAction> actions) {

		List<RewriteStep> steps = new ArrayList<>();
		Term current = seed;
		for (ClosureAction action : actions) {
			Term redex = current.get(action.position());
			Substitution matcher = new Substitution();
			RuleTrs rule = action.rule().rule();
			if (!rule.getLeft().isMoreGeneralThan(redex, matcher))
				return null;
			Term target = current.replace(
					action.position(), rule.getRight().apply(matcher));
			steps.add(new RewriteStep(
					current, target, action.rule().number(), action.position()));
			current = target;
		}
		return steps;
	}

	/** One analyzed input rule and its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** One original-rule application retained by the closure. */
	private record ClosureAction(NumberedRule rule, Position position) {}

	/** One symbolic forward-closure state. */
	private record ClosureState(
			Term source,
			Term target,
			Position lastPosition,
			List<ClosureAction> actions) {}

	/** Mutable state budget shared by the depth-first search. */
	private static final class SearchBudget {
		private int stateCount;
	}

	/** One certified original-TRS rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** A complete ground-cycle certificate. */
	private record GroundCycleWitness(
			Term closureSource,
			Term closureTarget,
			Term seed,
			Substitution unifier,
			List<RewriteStep> steps) {}

	/** Proof argument built from a replayed forward-closure ground cycle. */
	private record ForwardClosureGroundCycleArgument(GroundCycleWitness witness)
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
			return "forward-closure ground cycle";
		}

		@Override
		public String toString() {
			Map<Variable, String> variables = new HashMap<>();
			return "* Technique: bounded forward-closure ground-cycle search\n" +
					"* Certificate: " +
					this.witness.seed().toString(variables, false) +
					" is non-terminating\n* Description:\n" +
					"The forward closure\n" +
					this.witness.closureSource().toString(variables, false) +
					" ->\n" +
					this.witness.closureTarget().toString(variables, false) +
					"\ncloses under the unifier " +
					this.witness.unifier().toString(variables) + ".\n" +
					"Its ground instance rewrites in " +
					this.witness.steps().size() + " steps back to itself. " +
					"Repeating this replay yields an infinite rewrite sequence.\n" +
					getDetails(0);
		}
	}
}
