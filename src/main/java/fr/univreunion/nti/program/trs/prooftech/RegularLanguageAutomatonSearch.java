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
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Performs the bounded SAT search for a regular-language certificate.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class RegularLanguageAutomatonSearch {

	/** SAT solver used for each fixed-state-count encoding. */
	private final SatSolver solver;
	/** Maximum number of candidate automaton states. */
	private final int maximumStateCount;
	/** Maximum number of variables in one CNF formula. */
	private final int maximumVariableCount;
	/** Maximum number of clauses in one CNF formula. */
	private final int maximumClauseCount;
	/** Total SAT-search deadline in milliseconds. */
	private final int timeoutMilliseconds;

	/**
	 * Creates a bounded automaton search.
	 *
	 * @param solver propositional solver used for each state count
	 * @param maximumStateCount maximum candidate-automaton state count
	 * @param maximumVariableCount maximum variables in one CNF encoding
	 * @param maximumClauseCount maximum clauses in one CNF encoding
	 * @param timeoutMilliseconds total SAT-search time bound in milliseconds
	 */
	RegularLanguageAutomatonSearch(
			SatSolver solver,
			int maximumStateCount,
			int maximumVariableCount,
			int maximumClauseCount,
			int timeoutMilliseconds) {

		this.solver = solver;
		this.maximumStateCount = maximumStateCount;
		this.maximumVariableCount = maximumVariableCount;
		this.maximumClauseCount = maximumClauseCount;
		this.timeoutMilliseconds = timeoutMilliseconds;
	}

	/**
	 * Searches increasing state counts for a satisfying automaton.
	 *
	 * @param trs rewrite system whose language must be closed
	 * @param alphabet function symbols used by the rewrite system
	 * @param normalForms automaton recognizing ground normal forms
	 * @return the synthesized automaton and encoding statistics, or a result
	 *         without an automaton when the search fails or is aborted
	 */
	SearchResult search(
			Trs trs,
			List<FunctionSymbol> alphabet,
			NormalFormAutomaton normalForms) {

		long deadline = System.nanoTime() +
				this.timeoutMilliseconds * 1_000_000L;
		int largestVariableCount = 0;
		int largestClauseCount = 0;
		for (int stateCount = 1;
				stateCount <= this.maximumStateCount; stateCount++) {
			if (Thread.currentThread().isInterrupted())
				return SearchResult.aborted(
						largestVariableCount, largestClauseCount);

			Encoding encoding = new Encoder(
					trs, alphabet, normalForms.automaton(), stateCount,
					this.maximumVariableCount, this.maximumClauseCount).encode();
			largestVariableCount = Math.max(
					largestVariableCount, encoding.formula().variableCount());
			largestClauseCount = Math.max(
					largestClauseCount, encoding.formula().clauses().size());
			if (encoding.formula().tooLarge())
				return SearchResult.aborted(
						largestVariableCount, largestClauseCount);

			long remainingNanos = deadline - System.nanoTime();
			if (remainingNanos <= 0)
				return SearchResult.aborted(
						largestVariableCount, largestClauseCount);
			int remainingMilliseconds = Math.max(1,
					(int) Math.min(Integer.MAX_VALUE,
							remainingNanos / 1_000_000L));
			SatSolver.SatResult satResult = this.solver.solve(
					encoding.formula(), remainingMilliseconds);
			if (satResult.status() ==
					SatSolver.SatResult.Status.ABORTED)
				return SearchResult.aborted(
						largestVariableCount, largestClauseCount);
			if (satResult.status() ==
					SatSolver.SatResult.Status.SATISFIABLE)
				return new SearchResult(
						encoding.decode(satResult.model()), false,
						largestVariableCount, largestClauseCount);
		}
		return new SearchResult(
				null, false, largestVariableCount, largestClauseCount);
	}

	/**
	 * Result of the bounded automaton search.
	 *
	 * @param automaton synthesized automaton, or {@code null}
	 * @param aborted whether a size, time or interruption bound stopped search
	 * @param variableCount largest encoded variable count
	 * @param clauseCount largest encoded clause count
	 */
	record SearchResult(
			FiniteTreeAutomaton automaton,
			boolean aborted,
			int variableCount,
			int clauseCount) {

		/**
		 * Creates a result for a bounded or interrupted search.
		 *
		 * @param variableCount largest encoded variable count
		 * @param clauseCount largest encoded clause count
		 * @return an aborted search result
		 */
		private static SearchResult aborted(
				int variableCount, int clauseCount) {
			return new SearchResult(
					null, true, variableCount, clauseCount);
		}
	}

	/** Builds the CNF encoding for one fixed candidate state count. */
	private static final class Encoder {
		/** Rewrite system whose closure obligations are encoded. */
		private final Trs trs;
		/** Deterministically ordered rewrite-system alphabet. */
		private final List<FunctionSymbol> alphabet;
		/** Deterministic automaton recognizing ground normal forms. */
		private final FiniteTreeAutomaton normalForms;
		/** Number of states in the candidate automaton. */
		private final int stateCount;
		/** Bounded CNF formula under construction. */
		private final CnfFormula formula;
		/** SAT variable assigned to each possible candidate transition. */
		private final Map<TransitionKey, Integer> transitionVariables =
				new LinkedHashMap<>();
		/** Memoized SAT variables for term evaluations. */
		private final Map<EvaluationKey, Integer> evaluationVariables =
				new HashMap<>();
		/** SAT variable assigned to each candidate final state. */
		private final int[] finalVariables;
		/** Next globally unique index for a function syntax node. */
		private int nextNodeIndex;

		/**
		 * Creates an encoder for one fixed candidate state count.
		 *
		 * @param trs rewrite system to encode
		 * @param alphabet function symbols to encode
		 * @param normalForms automaton recognizing normal forms
		 * @param stateCount candidate-automaton state count
		 * @param maximumVariableCount CNF variable bound
		 * @param maximumClauseCount CNF clause bound
		 */
		private Encoder(
				Trs trs,
				List<FunctionSymbol> alphabet,
				FiniteTreeAutomaton normalForms,
				int stateCount,
				int maximumVariableCount,
				int maximumClauseCount) {

			this.trs = trs;
			this.alphabet = alphabet;
			this.normalForms = normalForms;
			this.stateCount = stateCount;
			this.formula = new CnfFormula(
					maximumVariableCount, maximumClauseCount);
			this.finalVariables = new int[stateCount];
		}

		/**
		 * Encodes all certificate obligations while respecting CNF bounds.
		 *
		 * @return the completed or size-bounded encoding
		 */
		private Encoding encode() {
			declareAutomatonVariables();
			if (!this.formula.tooLarge())
				encodeReachabilityAndNonemptiness();
			if (!this.formula.tooLarge())
				encodeRewriteClosure();
			if (!this.formula.tooLarge())
				encodeNormalFormExclusion();
			return new Encoding(
					this.formula, this.stateCount,
					this.transitionVariables, this.finalVariables);
		}

		/** Declares transition and final-state variables. */
		private void declareAutomatonVariables() {
			for (FunctionSymbol symbol : this.alphabet)
				for (List<Integer> arguments : stateTuples(
						this.stateCount, symbol.getArity()))
					for (int result = 0;
							result < this.stateCount; result++)
						this.transitionVariables.put(
								new TransitionKey(symbol, arguments, result),
								this.formula.newVariable());
			for (int state = 0; state < this.stateCount; state++)
				this.finalVariables[state] = this.formula.newVariable();
		}

		/** Encodes accessible state numbering and a nonempty language. */
		private void encodeReachabilityAndNonemptiness() {
			for (int result = 0; result < this.stateCount; result++) {
				List<Integer> constructors = new ArrayList<>();
				for (FunctionSymbol symbol : this.alphabet)
					for (List<Integer> arguments : stateTuples(
							result, symbol.getArity()))
						constructors.add(transitionVariable(
								symbol, arguments, result));
				this.formula.addClause(constructors);
			}
			List<Integer> finalStates = new ArrayList<>(this.stateCount);
			for (int variable : this.finalVariables)
				finalStates.add(variable);
			this.formula.addClause(finalStates);
		}

		/** Encodes state-wise closure under every rewrite rule. */
		private void encodeRewriteClosure() {
			for (RuleTrs rule : this.trs) {
				RuleNodes nodes = new RuleNodes(rule, this.nextNodeIndex);
				this.nextNodeIndex = nodes.nextNodeIndex();
				int[] assignment = new int[nodes.variableCount()];
				encodeAssignments(nodes, assignment, 0);
			}
		}

		/**
		 * Enumerates variable-to-state assignments for one rewrite rule.
		 *
		 * @param nodes indexed nodes of the rule sides
		 * @param assignment state assigned to each rule variable
		 * @param index next variable position to assign
		 */
		private void encodeAssignments(
				RuleNodes nodes, int[] assignment, int index) {

			if (this.formula.tooLarge())
				return;
			if (index < assignment.length) {
				for (int state = 0; state < this.stateCount; state++) {
					assignment[index] = state;
					encodeAssignments(nodes, assignment, index + 1);
				}
				return;
			}
			for (int state = 0; state < this.stateCount; state++)
				this.formula.addClause(
						-evaluationLiteral(nodes.left(), assignment, state),
						evaluationLiteral(nodes.right(), assignment, state));
		}

		/**
		 * Returns the literal stating that a term node evaluates to a state.
		 *
		 * @param node indexed term node
		 * @param assignment state assigned to each rule variable
		 * @param resultState requested root state
		 * @return the corresponding evaluation literal
		 */
		private int evaluationLiteral(
				Node node, int[] assignment, int resultState) {

			if (this.formula.tooLarge())
				return this.formula.trueLiteral();
			if (node.variableIndex() >= 0)
				return assignment[node.variableIndex()] == resultState ?
						this.formula.trueLiteral() :
						-this.formula.trueLiteral();

			int projection = 0;
			for (int variable : node.relevantVariables())
				projection = projection * this.stateCount + assignment[variable];
			EvaluationKey key = new EvaluationKey(
					node.index(), projection, resultState);
			Integer existing = this.evaluationVariables.get(key);
			if (existing != null)
				return existing;

			int evaluation = this.formula.newVariable();
			this.evaluationVariables.put(key, evaluation);
			List<Integer> alternatives = new ArrayList<>();
			for (List<Integer> arguments : stateTuples(
					this.stateCount, node.symbol().getArity())) {
				List<Integer> conjunction = new ArrayList<>(
						arguments.size() + 1);
				conjunction.add(transitionVariable(
						node.symbol(), arguments, resultState));
				for (int child = 0; child < arguments.size(); child++)
					conjunction.add(evaluationLiteral(
							node.children().get(child), assignment,
							arguments.get(child)));

				int alternative = this.formula.newVariable();
				alternatives.add(alternative);
				for (int literal : conjunction)
					this.formula.addClause(-alternative, literal);
				List<Integer> reverse = new ArrayList<>(
						conjunction.size() + 1);
				for (int literal : conjunction)
					reverse.add(-literal);
				reverse.add(alternative);
				this.formula.addClause(reverse);
				this.formula.addClause(-alternative, evaluation);
			}
			List<Integer> reverse = new ArrayList<>(alternatives.size() + 1);
			reverse.add(-evaluation);
			reverse.addAll(alternatives);
			this.formula.addClause(reverse);
			return evaluation;
		}

		/** Encodes emptiness of the product with the normal-form automaton. */
		private void encodeNormalFormExclusion() {
			int[][] productVariables = new int[this.stateCount]
					[this.normalForms.stateCount()];
			for (int candidateState = 0;
					candidateState < this.stateCount; candidateState++)
				for (int normalState = 0;
						normalState < this.normalForms.stateCount(); normalState++)
					productVariables[candidateState][normalState] =
							this.formula.newVariable();

			for (Map.Entry<TransitionKey, Integer> candidate :
					this.transitionVariables.entrySet())
				for (FiniteTreeAutomaton.Transition normal :
						this.normalForms.transitions()) {
					TransitionKey transition = candidate.getKey();
					if (transition.symbol() != normal.symbol())
						continue;
					List<Integer> clause = new ArrayList<>(
							transition.arguments().size() + 2);
					clause.add(-candidate.getValue());
					for (int child = 0;
							child < transition.arguments().size(); child++)
						clause.add(-productVariables
								[transition.arguments().get(child)]
								[normal.arguments().get(child)]);
					clause.add(productVariables
							[transition.result()][normal.result()]);
					this.formula.addClause(clause);
				}

			for (int candidateState = 0;
					candidateState < this.stateCount; candidateState++)
				for (int normalState : this.normalForms.finalStates())
					this.formula.addClause(
							-productVariables[candidateState][normalState],
								-this.finalVariables[candidateState]);
		}

		/**
		 * Enumerates state tuples of a fixed arity.
		 *
		 * @param stateCount number of states available at each position
		 * @param arity tuple length
		 * @return all tuples in lexicographic enumeration order
		 */
		private static List<List<Integer>> stateTuples(
				int stateCount, int arity) {

			List<List<Integer>> result = new ArrayList<>();
			if (arity == 0) {
				result.add(List.of());
				return result;
			}
			if (stateCount == 0)
				return result;
			enumerateStateTuples(
					stateCount, arity, new ArrayList<>(), result);
			return result;
		}

		/**
		 * Recursively enumerates state-tuple suffixes.
		 *
		 * @param stateCount number of states available at each position
		 * @param remaining number of positions left to fill
		 * @param current tuple prefix under construction
		 * @param result destination list for complete tuples
		 */
		private static void enumerateStateTuples(
				int stateCount,
				int remaining,
				List<Integer> current,
				List<List<Integer>> result) {

			if (remaining == 0) {
				result.add(List.copyOf(current));
				return;
			}
			for (int state = 0; state < stateCount; state++) {
				current.add(state);
				enumerateStateTuples(
						stateCount, remaining - 1, current, result);
				current.removeLast();
			}
		}

		/**
		 * Looks up the variable representing one candidate transition.
		 *
		 * @param symbol transition symbol
		 * @param arguments source states
		 * @param result target state
		 * @return the transition variable
		 * @throws IllegalArgumentException if the transition was not declared
		 */
		private int transitionVariable(
				FunctionSymbol symbol, List<Integer> arguments, int result) {

			Integer variable = this.transitionVariables.get(
					new TransitionKey(symbol, arguments, result));
			if (variable == null)
				throw new IllegalArgumentException("unknown transition variable");
			return variable;
		}
	}

	/** An identity-bearing encoding whose array is not a value component. */
	@SuppressWarnings("ClassCanBeRecord")
	private static final class Encoding {
		/** Encoded bounded CNF formula. */
		private final CnfFormula formula;
		/** Candidate-automaton state count. */
		private final int stateCount;
		/** Transition-to-SAT-variable index in deterministic order. */
		private final Map<TransitionKey, Integer> transitionVariables;
		/** SAT variables representing final states. */
		private final int[] finalVariables;

		/**
		 * Stores a completed fixed-state-count encoding.
		 *
		 * @param formula encoded CNF formula
		 * @param stateCount candidate-automaton state count
		 * @param transitionVariables transition-to-variable index
		 * @param finalVariables final-state variables by state
		 */
		private Encoding(
				CnfFormula formula,
				int stateCount,
				Map<TransitionKey, Integer> transitionVariables,
				int[] finalVariables) {

			this.formula = formula;
			this.stateCount = stateCount;
			this.transitionVariables = transitionVariables;
			this.finalVariables = finalVariables.clone();
		}

		/**
		 * Returns the encoded formula.
		 *
		 * @return the CNF formula
		 */
		private CnfFormula formula() {
			return this.formula;
		}

		/**
		 * Decodes transition and final-state variables from a SAT model.
		 *
		 * @param model one-based Boolean SAT model
		 * @return the candidate finite tree automaton
		 */
		private FiniteTreeAutomaton decode(boolean[] model) {
			Set<Integer> finalStates = new LinkedHashSet<>();
			for (int state = 0; state < this.finalVariables.length; state++)
				if (model[this.finalVariables[state]])
					finalStates.add(state);

			List<FiniteTreeAutomaton.Transition> transitions =
					new ArrayList<>();
			for (Map.Entry<TransitionKey, Integer> entry :
					this.transitionVariables.entrySet())
				if (model[entry.getValue()]) {
					TransitionKey transition = entry.getKey();
					transitions.add(new FiniteTreeAutomaton.Transition(
							transition.symbol(), transition.arguments(),
							transition.result()));
				}
			return new FiniteTreeAutomaton(
					this.stateCount, finalStates, transitions);
		}
	}

	/** Indexed syntax trees and variable metadata for one rewrite rule. */
	private static final class RuleNodes {
		/** Root node of the left-hand side. */
		private final Node left;
		/** Root node of the right-hand side. */
		private final Node right;
		/** Number of distinct variables in the left-hand side. */
		private final int variableCount;
		/** First function-node index unused after indexing this rule. */
		private final int nextNodeIndex;

		/**
		 * Indexes both sides of a rewrite rule.
		 *
		 * @param rule rewrite rule to index
		 * @param firstNodeIndex first index available for function nodes
		 */
		private RuleNodes(RuleTrs rule, int firstNodeIndex) {
			List<Variable> variables =
					RegularLanguageCertificateVerifier
							.variablesInTraversalOrder(rule.getLeft());
			IdentityHashMap<Variable, Integer> variableIndexes =
					new IdentityHashMap<>();
			for (int index = 0; index < variables.size(); index++)
				variableIndexes.put(variables.get(index), index);
			NodeBuilder builder = new NodeBuilder(
					variableIndexes, firstNodeIndex);
			this.left = builder.build(rule.getLeft());
			this.right = builder.build(rule.getRight());
			this.variableCount = variables.size();
			this.nextNodeIndex = builder.nextNodeIndex;
		}

		/**
		 * Returns the indexed left-hand side.
		 *
		 * @return the left root node
		 */
		private Node left() {
			return this.left;
		}

		/**
		 * Returns the indexed right-hand side.
		 *
		 * @return the right root node
		 */
		private Node right() {
			return this.right;
		}

		/**
		 * Returns the number of left-hand-side variables.
		 *
		 * @return the variable count
		 */
		private int variableCount() {
			return this.variableCount;
		}

		/**
		 * Returns the next unused function-node index.
		 *
		 * @return the next node index
		 */
		private int nextNodeIndex() {
			return this.nextNodeIndex;
		}
	}

	/** Builds identity-shared syntax nodes for both sides of one rule. */
	private static final class NodeBuilder {
		/** Identity-based index of left-hand-side variables. */
		private final IdentityHashMap<Variable, Integer> variableIndexes;
		/** Identity-based memo table from terms to syntax nodes. */
		private final IdentityHashMap<Term, Node> nodes =
				new IdentityHashMap<>();
		/** Next globally unique index for a function syntax node. */
		private int nextNodeIndex;

		/**
		 * Creates a node builder for one rewrite rule.
		 *
		 * @param variableIndexes identity-based variable indexes
		 * @param nextNodeIndex first available function-node index
		 */
		private NodeBuilder(
				IdentityHashMap<Variable, Integer> variableIndexes,
				int nextNodeIndex) {

			this.variableIndexes = variableIndexes;
			this.nextNodeIndex = nextNodeIndex;
		}

		/**
		 * Builds or reuses the indexed node for a term.
		 *
		 * @param term rule subterm to index
		 * @return the corresponding syntax node
		 * @throws IllegalArgumentException if a right-hand-side variable does not
		 *         occur in the left-hand side
		 */
		private Node build(Term term) {
			Node existing = this.nodes.get(term);
			if (existing != null)
				return existing;
			if (term instanceof Variable variable) {
				Integer variableIndex = this.variableIndexes.get(variable);
				if (variableIndex == null)
					throw new IllegalArgumentException(
							"extra right-hand-side variable");
				Node result = new Node(
						-1, null, variableIndex, List.of(),
						new int[] {variableIndex});
				this.nodes.put(term, result);
				return result;
			}

			Function function = (Function) term;
			List<Node> children = new ArrayList<>(
					function.getRootSymbol().getArity());
			Set<Integer> relevant = new java.util.TreeSet<>();
			for (int child = 0;
					child < function.getRootSymbol().getArity(); child++) {
				Node childNode = build(function.getChild(child));
				children.add(childNode);
				for (int variableIndex : childNode.relevantVariables())
					relevant.add(variableIndex);
			}
			int[] relevantVariables = relevant.stream()
					.mapToInt(Integer::intValue).toArray();
			Node result = new Node(
					this.nextNodeIndex++, function.getRootSymbol(), -1,
					children, relevantVariables);
			this.nodes.put(term, result);
			return result;
		}
	}

	/** An identity-bearing syntax node whose array is not a value component. */
	@SuppressWarnings("ClassCanBeRecord")
	private static final class Node {
		/** Unique function-node index, or {@code -1} for a variable. */
		private final int index;
		/** Root function symbol, or {@code null} for a variable. */
		private final FunctionSymbol symbol;
		/** Variable index, or {@code -1} for a function node. */
		private final int variableIndex;
		/** Immutable child-node list in argument order. */
		private final List<Node> children;
		/** Indexes of variables occurring at or below this node. */
		private final int[] relevantVariables;

		/**
		 * Creates an indexed syntax node.
		 *
		 * @param index unique index for a function node, or {@code -1} for a variable
		 * @param symbol root symbol, or {@code null} for a variable
		 * @param variableIndex variable index, or {@code -1} for a function node
		 * @param children child nodes in argument order
		 * @param relevantVariables variables occurring below this node
		 */
		private Node(
				int index,
				FunctionSymbol symbol,
				int variableIndex,
				List<Node> children,
				int[] relevantVariables) {

			this.index = index;
			this.symbol = symbol;
			this.variableIndex = variableIndex;
			this.children = List.copyOf(children);
			this.relevantVariables = relevantVariables.clone();
		}

		/**
		 * Returns the function-node index.
		 *
		 * @return the node index, or {@code -1} for a variable
		 */
		private int index() {
			return this.index;
		}

		/**
		 * Returns the root function symbol.
		 *
		 * @return the symbol, or {@code null} for a variable
		 */
		private FunctionSymbol symbol() {
			return this.symbol;
		}

		/**
		 * Returns the variable index.
		 *
		 * @return the variable index, or {@code -1} for a function node
		 */
		private int variableIndex() {
			return this.variableIndex;
		}

		/**
		 * Returns the child nodes.
		 *
		 * @return an immutable child list
		 */
		private List<Node> children() {
			return this.children;
		}

		/**
		 * Returns the indexes of variables occurring below this node.
		 *
		 * @return the internally owned relevant-variable array
		 */
		private int[] relevantVariables() {
			return this.relevantVariables;
		}
	}

	/**
	 * Key identifying one candidate-automaton transition.
	 *
	 * @param symbol transition symbol
	 * @param arguments source states
	 * @param result target state
	 */
	private record TransitionKey(
			FunctionSymbol symbol, List<Integer> arguments, int result) {

		TransitionKey {
			arguments = List.copyOf(arguments);
		}
	}

	/**
	 * Key identifying one memoized term-evaluation literal.
	 *
	 * @param node function-node index
	 * @param assignment projected variable assignment
	 * @param result requested root state
	 */
	private record EvaluationKey(int node, int assignment, int result) {}

}
