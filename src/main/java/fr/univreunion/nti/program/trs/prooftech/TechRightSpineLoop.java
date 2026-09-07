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
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Searches a bounded context loop in rules that encode string rewriting along
 * the right spine of one binary function symbol.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechRightSpineLoop implements ProofTechnique {

	/** Maximum number of distinct constants in a searched string system. */
	private static final int MAX_ALPHABET_SIZE = 4;

	/** Maximum length of an enumerated starting word. */
	private static final int MAX_SEED_LENGTH = 8;

	/** Maximum depth of the breadth-first search from one starting word. */
	private static final int MAX_SEARCH_DEPTH = 16;

	/** Maximum length of a word retained by the search. */
	private static final int MAX_WORD_LENGTH = 64;

	/** Maximum number of starting words considered for one spine symbol. */
	private static final int MAX_SEED_COUNT = 20_000;

	/** Maximum number of descendants considered for one spine symbol. */
	private static final int MAX_STATE_COUNT = 100_000;

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
				"## Searching for a bounded right-spine context loop...");
		for (List<SpineRule> rules : extractRuleGroups(trs).values()) {
			LoopWitness witness = search(rules);
			if (witness != null) {
				proof.printlnIfVerbose("Found a right-spine context loop!");
				proof.setResult(Proof.ProofResult.NO);
				proof.setArgument(new RightSpineLoopArgument(witness));
				return proof;
			}
		}
		proof.printlnIfVerbose("No right-spine context loop found!");
		return proof;
	}

	/** Extracts eligible rules and groups them by right-spine symbol. */
	private static Map<FunctionSymbol, List<SpineRule>> extractRuleGroups(Trs trs) {
		Map<FunctionSymbol, List<SpineRule>> groups = new LinkedHashMap<>();
		int ruleNumber = 1;
		for (RuleTrs rule : trs) {
			SpineRule spineRule = extractRule(rule, ruleNumber++);
			if (spineRule != null)
				groups.computeIfAbsent(spineRule.spine(), ignored -> new ArrayList<>())
						.add(spineRule);
		}
		return groups;
	}

	/** Extracts the string rule represented by the specified TRS rule. */
	private static SpineRule extractRule(RuleTrs rule, int ruleNumber) {
		FunctionSymbol spine = rule.getLeft().getRootSymbol();
		if (spine.getArity() != 2)
			return null;

		SpineSide left = extractSide(rule.getLeft(), spine);
		SpineSide right = extractSide(rule.getRight(), spine);
		if (left == null || right == null ||
				!sameResidual(left.residual(), right.residual()))
			return null;

		return new SpineRule(spine, ruleNumber, left.word(), right.word());
	}

	/** Extracts a nonempty constant word followed by a variable residual. */
	private static SpineSide extractSide(Term term, FunctionSymbol spine) {
		List<FunctionSymbol> word = new ArrayList<>();
		Term current = term;
		while (current instanceof Function function &&
				function.getRootSymbol() == spine) {
			Term head = function.getChild(0);
			Term tail = function.getChild(1);
			if (head instanceof Function constant &&
					constant.getRootSymbol().getArity() == 0) {
				word.add(constant.getRootSymbol());
				current = tail;
				continue;
			}
			if (!word.isEmpty() && head instanceof Variable && tail instanceof Variable)
				return new SpineSide(List.copyOf(word), function);
			return null;
		}
		return null;
	}

	/** Returns whether two residuals are the same {@code f(X,Y)} term. */
	private static boolean sameResidual(Function left, Function right) {
		return left.getRootSymbol() == right.getRootSymbol() &&
				left.getChild(0) == right.getChild(0) &&
				left.getChild(1) == right.getChild(1);
	}

	/** Searches all bounded starting words for the specified string rules. */
	private static LoopWitness search(List<SpineRule> rules) {
		EncodedSystem system = encode(rules);
		if (system == null)
			return null;

		SearchBudget budget = new SearchBudget();
		int minimumLength = system.rules().stream()
				.mapToInt(rule -> rule.left().length())
				.min().orElse(0) + 1;
		for (int length = minimumLength; length <= MAX_SEED_LENGTH; length++) {
			int wordCount = power(system.alphabet().size(), length);
			for (int number = 0; number < wordCount; number++) {
				if (++budget.seedCount > MAX_SEED_COUNT)
					return null;
				String seed = word(number, length, system.alphabet().size());
				LoopWitness witness = searchFrom(seed, system, budget);
				if (witness != null)
					return witness;
				if (budget.stateCount >= MAX_STATE_COUNT)
					return null;
			}
		}
		return null;
	}

	/** Encodes function symbols as compact characters. */
	private static EncodedSystem encode(List<SpineRule> rules) {
		Map<FunctionSymbol, Character> codes = new LinkedHashMap<>();
		for (SpineRule rule : rules) {
			addSymbols(rule.left(), codes);
			addSymbols(rule.right(), codes);
		}
		if (codes.isEmpty() || codes.size() > MAX_ALPHABET_SIZE)
			return null;

		List<EncodedRule> encodedRules = new ArrayList<>();
		for (SpineRule rule : rules)
			encodedRules.add(new EncodedRule(
					rule.ruleNumber(), encode(rule.left(), codes), encode(rule.right(), codes)));
		return new EncodedSystem(
				rules.getFirst().spine(), List.copyOf(codes.keySet()), encodedRules);
	}

	/** Adds symbols to the insertion-ordered character dictionary. */
	private static void addSymbols(
			List<FunctionSymbol> symbols,
			Map<FunctionSymbol, Character> codes) {

		for (FunctionSymbol symbol : symbols)
			codes.computeIfAbsent(symbol, ignored -> (char) codes.size());
	}

	/** Encodes a symbol word using the provided dictionary. */
	private static String encode(
			List<FunctionSymbol> symbols,
			Map<FunctionSymbol, Character> codes) {

		StringBuilder word = new StringBuilder(symbols.size());
		for (FunctionSymbol symbol : symbols)
			word.append(codes.get(symbol).charValue());
		return word.toString();
	}

	/** Returns the word at the specified odometer position. */
	private static String word(int number, int length, int radix) {
		char[] symbols = new char[length];
		for (int i = length - 1; 0 <= i; i--) {
			symbols[i] = (char) (number % radix);
			number /= radix;
		}
		return new String(symbols);
	}

	/** Computes a small positive integer power. */
	private static int power(int base, int exponent) {
		int result = 1;
		for (int i = 0; i < exponent; i++)
			result *= base;
		return result;
	}

	/** Performs a breadth-first search from one starting word. */
	private static LoopWitness searchFrom(
			String seed,
			EncodedSystem system,
			SearchBudget budget) {

		ArrayDeque<SearchNode> pending = new ArrayDeque<>();
		Set<String> visited = new HashSet<>();
		SearchNode root = new SearchNode(seed, null, null, -1, 0);
		pending.add(root);
		visited.add(seed);

		while (!pending.isEmpty()) {
			SearchNode current = pending.remove();
			if (current.depth() >= MAX_SEARCH_DEPTH)
				continue;
			for (EncodedRule rule : system.rules()) {
				LoopWitness witness = expand(seed, system, budget,
						current, rule, pending, visited);
				if (witness != null || budget.stateCount >= MAX_STATE_COUNT)
					return witness;
			}
		}
		return null;
	}

	/** Expands one node with all left-to-right occurrences of one rule. */
	private static LoopWitness expand(
			String seed,
			EncodedSystem system,
			SearchBudget budget,
			SearchNode current,
			EncodedRule rule,
			ArrayDeque<SearchNode> pending,
			Set<String> visited) {

		String word = current.word();
		int lastPosition = word.length() - rule.left().length();
		for (int position = 0;
				position < lastPosition && budget.stateCount < MAX_STATE_COUNT;
				position++) {

			if (word.startsWith(rule.left(), position)) {
				String nextWord = replace(word, rule, position);
				if (nextWord.length() <= MAX_WORD_LENGTH && visited.add(nextWord)) {
					budget.stateCount++;
					SearchNode next = new SearchNode(
							nextWord, current, rule, position, current.depth() + 1);
					int occurrence = nextWord.indexOf(seed);
					if (0 <= occurrence)
						return buildWitness(system, seed, occurrence, next);
					pending.add(next);
				}
			}
		}
		return null;
	}

	/** Replaces one word occurrence with a rule's right-hand side. */
	private static String replace(String word, EncodedRule rule, int position) {
		return word.substring(0, position) + rule.right() +
				word.substring(position + rule.left().length());
	}

	/** Reconstructs a context-loop witness from a successful search node. */
	private static LoopWitness buildWitness(
			EncodedSystem system,
			String seed,
			int occurrence,
			SearchNode last) {

		List<LoopStep> steps = new ArrayList<>();
		for (SearchNode node = last; node.parent() != null; node = node.parent())
			steps.add(new LoopStep(
					node.parent().word(), node.word(), node.rule(), node.position()));
		Collections.reverse(steps);
		return new LoopWitness(system, seed, last.word(), occurrence, List.copyOf(steps));
	}

	/** One extracted side of a right-spine rule. */
	private record SpineSide(List<FunctionSymbol> word, Function residual) {}

	/** One extracted right-spine string rule. */
	private record SpineRule(
			FunctionSymbol spine,
			int ruleNumber,
			List<FunctionSymbol> left,
			List<FunctionSymbol> right) {}

	/** One compactly encoded string rule. */
	private record EncodedRule(int ruleNumber, String left, String right) {}

	/** An encoded string rewrite system. */
	private record EncodedSystem(
			FunctionSymbol spine,
			List<FunctionSymbol> alphabet,
			List<EncodedRule> rules) {}

	/** One node of the bounded breadth-first search. */
	private record SearchNode(
			String word,
			SearchNode parent,
			EncodedRule rule,
			int position,
			int depth) {}

	/** Mutable counters shared by the searches for one spine symbol. */
	private static final class SearchBudget {
		private int seedCount;
		private int stateCount;
	}

	/** One step of a context-loop certificate. */
	private record LoopStep(
			String source,
			String target,
			EncodedRule rule,
			int position) {}

	/** A complete context-loop certificate. */
	private record LoopWitness(
			EncodedSystem system,
			String seed,
			String result,
			int occurrence,
			List<LoopStep> steps) {}

	/** Proof argument built from a right-spine context loop. */
	private record RightSpineLoopArgument(LoopWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			StringBuilder details = new StringBuilder();
			int stepNumber = 1;
			for (LoopStep step : this.witness.steps()) {
				details.append(spaces).append(stepNumber++).append(". ")
						.append(renderWord(step.source())).append(" -> ")
						.append(renderWord(step.target())).append(" (rule ")
						.append(step.rule().ruleNumber()).append(", offset ")
						.append(step.position()).append(")\n");
			}
			if (!details.isEmpty())
				details.setLength(details.length() - 1);
			return details.toString();
		}

		@Override
		public String getWitnessKind() {
			return "right-spine context loop";
		}

		@Override
		public String toString() {
			String seed = renderWord(this.witness.seed());
			String result = renderWord(this.witness.result());
			String prefix = renderWord(this.witness.result().substring(
					0, this.witness.occurrence()));
			String suffix = renderWord(this.witness.result().substring(
					this.witness.occurrence() + this.witness.seed().length()));
			return "* Technique: bounded right-spine context-loop search\n" +
					"* Certificate: " + certificate() + " is non-terminating\n" +
					"* Description:\n" +
					"The right-spine word " + seed + " rewrites in " +
					this.witness.steps().size() + " steps to\n" + result + ".\n" +
					"The latter is " + context(prefix, seed, suffix) + ".\n" +
					"Every displayed word step is an application of an analyzed TRS rule\n" +
					"with the same residual " + this.witness.system().spine() + "(X,Y).\n" +
					"Repeating the derivation in the embedded copy of " + seed +
					" yields an infinite rewrite sequence.\n" +
					getDetails(0);
		}

		/** Renders an encoded word as a whitespace-separated symbol list. */
		private String renderWord(String word) {
			if (word.isEmpty())
				return "ε";
			StringBuilder result = new StringBuilder();
			for (int i = 0; i < word.length(); i++) {
				if (0 < i)
					result.append(' ');
				result.append(this.witness.system().alphabet().get(word.charAt(i)));
			}
			return result.toString();
		}

		/** Renders the ground right-spine term represented by the seed. */
		private String certificate() {
			FunctionSymbol spine = this.witness.system().spine();
			String constant = this.witness.system().alphabet().getFirst().toString();
			StringBuilder term = new StringBuilder();
			String seed = this.witness.seed();
			for (int i = 0; i < seed.length(); i++)
				term.append(spine).append('(')
						.append(this.witness.system().alphabet().get(seed.charAt(i)))
						.append(',');
			term.append(spine).append('(').append(constant).append(',')
					.append(constant).append(')');
			term.repeat(")", seed.length());
			return term.toString();
		}

		/** Renders the decomposition of the reached word around the seed. */
		private static String context(String prefix, String seed, String suffix) {
			StringBuilder result = new StringBuilder();
			if (!"ε".equals(prefix))
				result.append(prefix).append(" · ");
			result.append('(').append(seed).append(')');
			if (!"ε".equals(suffix))
				result.append(" · ").append(suffix);
			return result.toString();
		}
	}
}
