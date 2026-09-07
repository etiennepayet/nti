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
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
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
 * Searches for a regular tree language that is nonempty, closed under
 * rewriting and disjoint from the normal forms.
 *
 * <p>This is Technique 27 of J. Endrullis and H. Zantema,
 * <a href="https://doi.org/10.4230/LIPIcs.RTA.2015.160">Proving
 * non-termination by finite automata</a>, RTA 2015, LIPIcs 36, pp. 160--176.
 * The SAT model is decoded to an automaton and every proof obligation is
 * checked again independently before a nontermination result is returned.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class TechRegularLanguageNonTermination implements ProofTechnique {

	/** Maximum number of rewrite rules accepted by the structural gate. */
	private static final int MAX_RULE_COUNT = 8;
	/** Maximum number of distinct function symbols accepted by the gate. */
	private static final int MAX_SYMBOL_COUNT = 12;
	/** Maximum function-symbol arity accepted by the gate. */
	private static final int MAX_ARITY = 2;
	/** Maximum number of left-hand-side variables in one rule. */
	private static final int MAX_VARIABLES_PER_RULE = 3;
	/** Maximum rewrite-rule term depth accepted by the gate. */
	private static final int MAX_TERM_DEPTH = 8;
	/** Maximum reachable state count of the normal-form automaton. */
	private static final int MAX_NORMAL_FORM_STATE_COUNT = 64;
	/** Maximum explicit transition count of the normal-form automaton. */
	private static final int MAX_NORMAL_FORM_TRANSITION_COUNT = 4_096;
	/** Maximum synthesized candidate-automaton state count. */
	private static final int MAX_AUTOMATON_STATE_COUNT = 5;
	/** Maximum variable count of one SAT encoding. */
	private static final int MAX_SAT_VARIABLE_COUNT = 50_000;
	/** Maximum clause count of one SAT encoding. */
	private static final int MAX_SAT_CLAUSE_COUNT = 200_000;
	/** Total SAT-search time bound in milliseconds. */
	private static final int MAX_SAT_TIME_MILLISECONDS = 1_000;
	/** Verbose message emitted when no bounded certificate is found. */
	private static final String NOT_FOUND_MESSAGE =
			"No regular-language nontermination certificate found!";

	/** Solver used to synthesize candidate finite tree automata. */
	private final SatSolver satSolver;

	/** Builds the default bounded SAT-backed technique. */
	public TechRegularLanguageNonTermination() {
		this(new Sat4jSolver());
	}

	/**
	 * Builds the technique with an injected SAT solver.
	 *
	 * @param satSolver solver used for bounded automaton synthesis
	 */
	TechRegularLanguageNonTermination(SatSolver satSolver) {
		this.satSolver = satSolver;
	}

	/**
	 * Searches for and independently verifies a regular-language certificate.
	 *
	 * @param trs rewrite system to analyze
	 * @param context analysis context used to create and report the proof
	 * @return a {@code NO} proof on success, otherwise an inconclusive proof
	 */
	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose(
				"## Searching for a bounded regular-language " +
						"nontermination certificate " +
						"[Endrullis and Zantema, RTA'15]...");

		List<FunctionSymbol> alphabet = eligibleAlphabet(trs);
		if (alphabet == null || Thread.currentThread().isInterrupted()) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		NormalFormAutomaton normalForms = NormalFormAutomaton.build(
				trs, alphabet, MAX_NORMAL_FORM_STATE_COUNT,
				MAX_NORMAL_FORM_TRANSITION_COUNT);
		if (normalForms == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		RegularLanguageAutomatonSearch.SearchResult search =
				new RegularLanguageAutomatonSearch(
						this.satSolver, MAX_AUTOMATON_STATE_COUNT,
						MAX_SAT_VARIABLE_COUNT, MAX_SAT_CLAUSE_COUNT,
						MAX_SAT_TIME_MILLISECONDS)
						.search(trs, alphabet, normalForms);
		FiniteTreeAutomaton automaton = search.automaton();
		if (automaton == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		RegularLanguageCertificateVerifier.Verification verification =
				new RegularLanguageCertificateVerifier().verify(
						trs, automaton, normalForms);
		if (!verification.valid()) {
			proof.printlnIfVerbose(
					"Rejected an invalid SAT model: " +
							verification.failure() + ".");
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		proof.printlnIfVerbose(
				"Found and independently verified a regular-language " +
						"nontermination certificate!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(new RegularLanguageArgument(
				automaton, verification.witness(), search.variableCount(),
				search.clauseCount()));
		return proof;
	}

	/**
	 * Returns the deterministic alphabet, or {@code null} if the gate fails.
	 *
	 * @param trs rewrite system to check against the structural bounds
	 * @return the sorted alphabet, or {@code null} when the system is ineligible
	 */
	private static List<FunctionSymbol> eligibleAlphabet(Trs trs) {
		if (trs.size() == 0 || trs.size() > MAX_RULE_COUNT ||
				RegularLanguageCertificateVerifier.hasNonLeftLinearRule(trs))
			return null;

		Set<FunctionSymbol> symbols = new LinkedHashSet<>();
		boolean hasConstant = false;
		boolean hasDuplicatingRule = false;
		for (RuleTrs rule : trs) {
			if (rule.isGeneralized() || rule.depth() > MAX_TERM_DEPTH ||
					rule.getLeft().getVariables().size() >
							MAX_VARIABLES_PER_RULE)
				return null;
			collectSymbols(rule.getLeft(), symbols);
			collectSymbols(rule.getRight(), symbols);
			hasDuplicatingRule |= isDuplicating(rule);
		}
		if (!hasDuplicatingRule || symbols.size() > MAX_SYMBOL_COUNT)
			return null;
		for (FunctionSymbol symbol : symbols) {
			if (symbol.getArity() > MAX_ARITY)
				return null;
			hasConstant |= symbol.getArity() == 0;
		}
		if (!hasConstant)
			return null;

		List<FunctionSymbol> result = new ArrayList<>(symbols);
		result.sort(Comparator.comparing(FunctionSymbol::getName)
				.thenComparingInt(FunctionSymbol::getArity));
		return result;
	}

	/**
	 * Recursively collects function symbols from a term.
	 *
	 * @param term term whose symbols are collected
	 * @param symbols destination set
	 */
	private static void collectSymbols(
			Term term, Set<FunctionSymbol> symbols) {

		if (!(term instanceof Function function))
			return;
		symbols.add(function.getRootSymbol());
		for (int child = 0;
				child < function.getRootSymbol().getArity(); child++)
			collectSymbols(function.getChild(child), symbols);
	}

	/**
	 * Reports whether a rule duplicates at least one variable.
	 *
	 * @param rule rewrite rule to inspect
	 * @return {@code true} if a right-side variable has more occurrences
	 */
	private static boolean isDuplicating(RuleTrs rule) {
		Map<Variable, Integer> left = new IdentityHashMap<>();
		Map<Variable, Integer> right = new IdentityHashMap<>();
		rule.getLeft().getVariableOccurrences(left);
		rule.getRight().getVariableOccurrences(right);
		for (Map.Entry<Variable, Integer> occurrence : right.entrySet())
			if (occurrence.getValue() > left.getOrDefault(
					occurrence.getKey(), 0))
				return true;
		return false;
	}

	/**
	 * Printable independently verified regular-language certificate.
	 *
	 * @param automaton certified finite tree automaton
	 * @param witness accepted ground witness
	 * @param satVariableCount variable count of the successful SAT encoding
	 * @param satClauseCount clause count of the successful SAT encoding
	 */
	private record RegularLanguageArgument(
			FiniteTreeAutomaton automaton,
			Term witness,
			int satVariableCount,
			int satClauseCount) implements Argument {

		/**
		 * Renders the automaton with the requested indentation.
		 *
		 * @param indentation number of leading spaces
		 * @return the indented automaton description
		 */
		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			return spaces + this.automaton.toString()
					.replace("\n", "\n" + spaces);
		}

		/**
		 * Returns the kind of witness carried by this argument.
		 *
		 * @return {@code "regular tree language"}
		 */
		@Override
		public String getWitnessKind() {
			return "regular tree language";
		}

		/**
		 * Renders the complete proof argument.
		 *
		 * @return the human-readable certificate
		 */
		@Override
		public String toString() {
			return "* Technique: finite-tree-automaton regular language " +
					"[Endrullis and Zantema, RTA'15]\n" +
					"* Certificate: " + this.witness +
					" is non-terminating\n" +
					"* Description:\n" +
					"The following bottom-up tree automaton accepts a nonempty " +
					"language that is closed under rewriting and contains no " +
					"normal form:\n" + getDetails(0) + "\n" +
					"All three obligations were checked independently after SAT " +
					"synthesis (" + this.satVariableCount + " variables, " +
					this.satClauseCount + " clauses). Hence every accepted term " +
					"starts an infinite rewrite sequence.";
		}
	}
}
