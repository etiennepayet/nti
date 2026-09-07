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

package fr.univreunion.nti.program.trs.prooftech.dependencypair.processor;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.CancellationException;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.dependencypair.DependencyGraph;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblemCollection;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Applies a bounded forward-instantiation transformation to a dependency pair
 * problem. A transformation is retained only when it strictly decreases the
 * number of dependency pairs that belong to cyclic SCCs.
 *
 * <p>The forward-instantiation transformation is based on Definition 28(d),
 * with soundness established by Theorem 31, in J. Giesl, R. Thiemann,
 * P. Schneider-Kamp, and S. Falke,
 * <a href="https://doi.org/10.1007/s10817-006-9057-7">Mechanizing and
 * Improving Dependency Pairs</a>, Journal of Automated Reasoning 37(3),
 * 155--203, 2006. The acceptance policy implements a conservative bounded
 * fragment of the safe-transformation heuristic from Definition 33,
 * especially clauses (1) and (5); termination of repeated safe
 * transformations is Theorem 34 of the same article.
 *
 * <p>The explicit size and depth bounds, and the requirement that the one
 * permitted non-decreasing step be followed immediately by a strict decrease,
 * are implementation choices specific to this processor.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class ForwardInstantiationDependencyPairProcessor
		extends DependencyPairProcessor {

	/** Maximum number of rewrite rules inspected by this processor. */
	private static final int MAX_TRS_RULE_COUNT = 2048;

	/** Maximum number of dependency pairs transformed by this processor. */
	private static final int MAX_DEPENDENCY_PAIR_COUNT = 64;

	/** Maximum accepted depth for an input dependency pair. */
	private static final int MAX_INPUT_PAIR_DEPTH = 32;

	/** Maximum accepted depth for a generated dependency pair. */
	private static final int MAX_GENERATED_PAIR_DEPTH = 64;

	/** Builds a forward-instantiation processor without argument filtering. */
	public ForwardInstantiationDependencyPairProcessor() {
		super(false);
	}

	/**
	 * Searches first for a directly decreasing forward instantiation, then for
	 * one permitted non-decreasing step followed by a decreasing one.
	 * {@inheritDoc}
	 */
	@Override
	public DependencyPairProcessorResult run(
			DependencyPairProblem problem,
			ArgFiltering filtering,
			int indentation,
			AnalysisContext context) {

		Proof proof = context.createProof();
		this.printFiltering(null, proof, indentation);
		if (Thread.currentThread().isInterrupted())
			return DependencyPairProcessorResult.failed(proof);

		Trs trs = problem.getTRS();
		List<RuleTrs> pairs = problem.getDependencyPairs().toDeque()
				.stream().toList();
		if (!isWithinBounds(trs, pairs, proof, indentation) ||
				containsGeneralizedRule(trs, proof, indentation))
			return DependencyPairProcessorResult.failed(proof);

		InverseCapSymbols inverseCapSymbols = inverseCapSymbols(trs);
		List<Term> inverseCaps = inverseCaps(pairs, inverseCapSymbols);

		try {
			int oldCyclicPairCount = cyclicPairCount(
					trs, new DependencyPairs(pairs));
			List<Instantiation> initialInstantiations =
					new ArrayList<>(pairs.size());
			for (int sourceIndex = 0;
					sourceIndex < pairs.size(); sourceIndex++) {
				if (Thread.currentThread().isInterrupted())
					return DependencyPairProcessorResult.failed(proof);

				RuleTrs source = pairs.get(sourceIndex);
				Instantiation instantiation = instantiate(
						source, inverseCaps);
				initialInstantiations.add(instantiation);
				if (instantiation == null)
					continue;

				List<RuleTrs> transformed = replace(
						pairs, sourceIndex, instantiation.instances());
				Deque<DependencyPairs> transformedSccs =
						new DependencyGraph(
								trs, new DependencyPairs(transformed)).getSCCs();
				int newCyclicPairCount = cyclicPairCount(transformedSccs);
				if (newCyclicPairCount < oldCyclicPairCount)
					return successfulResult(
							problem,
							List.of(new Transformation(
									source, instantiation.instances())),
							transformedSccs,
							oldCyclicPairCount, newCyclicPairCount,
							proof, indentation);
			}

			DependencyPairProcessorResult lookaheadResult = safeLookahead(
					problem, pairs, initialInstantiations, inverseCapSymbols,
					oldCyclicPairCount, proof, indentation);
			if (lookaheadResult != null)
				return lookaheadResult;
		}
		catch (CancellationException exception) {
			return DependencyPairProcessorResult.failed(proof);
		}

		return DependencyPairProcessorResult.failed(proof);
	}

	/**
	 * Tries the one non-decreasing forward-instantiation step permitted by the
	 * safe-transformation criterion, followed by a strictly decreasing step.
	 * Only a first step having exactly one matching successor pair is eligible.
	 *
	 * @param problem the original dependency-pair problem
	 * @param pairs the dependency pairs in their deterministic search order
	 * @param initialInstantiations the previously computed instantiations,
	 *        indexed like {@code pairs}
	 * @param inverseCapSymbols the TRS symbols used to construct inverse caps
	 * @param oldCyclicPairCount the number of cyclic pairs before either step
	 * @param proof the proof receiving diagnostic and certificate messages
	 * @param indentation the indentation used for proof messages
	 * @return a processor result when a safe sequence is found or the search is
	 *         interrupted; {@code null} if no eligible sequence exists
	 */
	private static DependencyPairProcessorResult safeLookahead(
			DependencyPairProblem problem,
			List<RuleTrs> pairs,
			List<Instantiation> initialInstantiations,
			InverseCapSymbols inverseCapSymbols,
			int oldCyclicPairCount,
			Proof proof,
			int indentation) {

		for (int firstIndex = 0; firstIndex < pairs.size(); firstIndex++) {
			if (Thread.currentThread().isInterrupted())
				return DependencyPairProcessorResult.failed(proof);

			Instantiation firstInstantiation =
					initialInstantiations.get(firstIndex);
			if (firstInstantiation == null ||
					firstInstantiation.unifiablePairCount() != 1)
				continue;

			List<RuleTrs> intermediate = replace(
					pairs, firstIndex, firstInstantiation.instances());
			List<Term> intermediateInverseCaps = inverseCaps(
					intermediate, inverseCapSymbols);
			DependencyPairProcessorResult result =
					tryStrictlyDecreasingSecondStep(
							problem,
							new Transformation(
									pairs.get(firstIndex),
									firstInstantiation.instances()),
							intermediate, intermediateInverseCaps,
							oldCyclicPairCount, proof, indentation);
			if (result != null)
				return result;
		}
		return null;
	}

	/**
	 * Tries every possible second step after one safe lookahead step. The pair
	 * order of the intermediate problem determines the search order.
	 *
	 * @param problem the original dependency-pair problem
	 * @param firstTransformation the accepted first source replacement
	 * @param intermediate the dependency pairs produced by the first step
	 * @param intermediateInverseCaps the inverse caps of the intermediate
	 *        left-hand sides, indexed like {@code intermediate}
	 * @param oldCyclicPairCount the cyclic-pair count before the first step
	 * @param proof the proof receiving diagnostic and certificate messages
	 * @param indentation the indentation used for proof messages
	 * @return a processor result when a decreasing second step is found or the
	 *         search is interrupted; {@code null} otherwise
	 */
	private static DependencyPairProcessorResult tryStrictlyDecreasingSecondStep(
			DependencyPairProblem problem,
			Transformation firstTransformation,
			List<RuleTrs> intermediate,
			List<Term> intermediateInverseCaps,
			int oldCyclicPairCount,
			Proof proof,
			int indentation) {

		Trs trs = problem.getTRS();
		for (int secondIndex = 0;
				secondIndex < intermediate.size(); secondIndex++) {
			if (Thread.currentThread().isInterrupted())
				return DependencyPairProcessorResult.failed(proof);

			RuleTrs secondSource = intermediate.get(secondIndex);
			Instantiation secondInstantiation = instantiate(
					secondSource, intermediateInverseCaps);
			if (secondInstantiation == null)
				continue;

			List<RuleTrs> transformed = replace(
					intermediate, secondIndex,
					secondInstantiation.instances());
			Deque<DependencyPairs> transformedSccs =
					new DependencyGraph(
							trs, new DependencyPairs(transformed)).getSCCs();
			int newCyclicPairCount = cyclicPairCount(transformedSccs);
			if (newCyclicPairCount < oldCyclicPairCount)
				return successfulResult(
						problem,
						List.of(
								firstTransformation,
								new Transformation(secondSource,
										secondInstantiation.instances())),
						transformedSccs,
						oldCyclicPairCount, newCyclicPairCount,
						proof, indentation);
		}
		return null;
	}

	/**
	 * Checks the explicit size and depth bounds before constructing inverse caps
	 * or dependency graphs.
	 *
	 * @param trs the rewrite system to inspect
	 * @param pairs the input dependency pairs
	 * @param proof the proof receiving the reason for a rejected input
	 * @param indentation the indentation used for proof messages
	 * @return {@code true} if all configured bounds are respected
	 */
	private static boolean isWithinBounds(
			Trs trs, List<RuleTrs> pairs, Proof proof, int indentation) {

		if (trs.size() > MAX_TRS_RULE_COUNT ||
				pairs.size() > MAX_DEPENDENCY_PAIR_COUNT) {
			proof.printlnIfVerbose(
					"Forward instantiation exceeds its size bounds! Aborting!",
					indentation);
			return false;
		}
		for (RuleTrs pair : pairs)
			if (pair.depth() > MAX_INPUT_PAIR_DEPTH) {
				proof.printlnIfVerbose(
						"Forward instantiation exceeds its depth bound! Aborting!",
						indentation);
				return false;
			}
		return true;
	}

	/**
	 * Detects generalized rules, which are outside this conservative fragment.
	 *
	 * @param trs the rewrite system to inspect
	 * @param proof the proof receiving the reason for rejection
	 * @param indentation the indentation used for proof messages
	 * @return {@code true} if the TRS contains a generalized rule
	 */
	private static boolean containsGeneralizedRule(
			Trs trs, Proof proof, int indentation) {

		for (RuleTrs rule : trs)
			if (rule.isGeneralized()) {
				proof.printlnIfVerbose(
						"Forward instantiation is disabled for a generalized TRS.",
						indentation);
				return true;
			}
		return false;
	}

	/**
	 * Collects the right-hand-side root symbols that may be rewritten at an
	 * inverse-cap position. A collapsing rule makes the whole inverse cap a
	 * fresh variable.
	 *
	 * @param trs the rewrite system whose right-hand sides are inspected
	 * @return the symbol set and the presence of a collapsing rule
	 */
	private static InverseCapSymbols inverseCapSymbols(Trs trs) {
		Set<FunctionSymbol> rightRoots = new HashSet<>();
		for (RuleTrs rule : trs) {
			Term right = rule.getRight();
			if (right instanceof Variable)
				return new InverseCapSymbols(Set.of(), true);
			rightRoots.add(right.getRootSymbol());
		}
		return new InverseCapSymbols(rightRoots, false);
	}

	/**
	 * Builds {@code REN(CAP_R^-1(term))}. Repeated occurrences of an original
	 * variable share the same fresh variable, whereas every capped position is
	 * replaced independently.
	 *
	 * @param term the term from which to construct the inverse cap
	 * @param symbols the symbols identifying capped positions
	 * @param renamedVariables the identity-based renaming accumulated for the
	 *        variables of {@code term}
	 * @return the renamed inverse cap
	 */
	private static Term inverseCap(
			Term term,
			InverseCapSymbols symbols,
			Map<Variable, Variable> renamedVariables) {

		if (symbols.collapsing())
			return new Variable();
		if (term instanceof Variable variable)
			return renamedVariables.computeIfAbsent(
					variable, ignored -> new Variable());

		Function function = (Function) term;
		FunctionSymbol root = function.getRootSymbol();
		if (symbols.rightRoots().contains(root))
			return new Variable();

		List<Term> arguments = new ArrayList<>(root.getArity());
		for (int index = 0; index < root.getArity(); index++)
			arguments.add(inverseCap(
					function.getChild(index), symbols, renamedVariables));
		return new Function(root, arguments);
	}

	/**
	 * Builds the inverse caps of all dependency-pair left-hand sides. Each pair
	 * receives an independent variable renaming.
	 *
	 * @param pairs the dependency pairs in source order
	 * @param symbols the symbols identifying capped positions
	 * @return inverse caps indexed like {@code pairs}
	 */
	private static List<Term> inverseCaps(
			List<RuleTrs> pairs, InverseCapSymbols symbols) {

		List<Term> result = new ArrayList<>(pairs.size());
		for (RuleTrs pair : pairs)
			result.add(inverseCap(
					pair.getLeft(), symbols, new IdentityHashMap<>()));
		return result;
	}

	/**
	 * Generates every forward instance of one dependency pair by unifying its
	 * right-hand side with each inverse cap. Alpha-equivalent instances are
	 * retained only once, in successor order.
	 *
	 * @param source the dependency pair to instantiate
	 * @param inverseCaps the inverse caps of possible successor left-hand sides
	 * @return the generated instances and the number of matching successors, or
	 *         {@code null} if interrupted or if an instance exceeds the depth
	 *         bound
	 */
	private static Instantiation instantiate(
			RuleTrs source, List<Term> inverseCaps) {

		List<RuleTrs> instances = new ArrayList<>();
		int unifiablePairCount = 0;
		for (Term inverseCap : inverseCaps) {
			if (Thread.currentThread().isInterrupted())
				return null;

			Map<Term, Term> copies = new HashMap<>();
			Function left = (Function) source.getLeft().deepCopy(copies);
			Term right = source.getRight().deepCopy(copies);
			Substitution unifier = new Substitution();
			if (!right.isUnifiableWith(inverseCap, unifier))
				continue;
			unifiablePairCount++;

			RuleTrs instance = new RuleTrs(
					(Function) left.apply(unifier), right.apply(unifier));
			if (instance.depth() > MAX_GENERATED_PAIR_DEPTH)
				return null;
			if (!containsVariant(instances, instance))
				instances.add(instance);
		}
		return new Instantiation(instances, unifiablePairCount);
	}

	/**
	 * Tests whether the list already contains an alpha-equivalent rule.
	 *
	 * @param rules the rules already retained
	 * @param candidate the rule considered for insertion
	 * @return {@code true} if a retained rule is a variable-renamed variant of
	 *         {@code candidate}
	 */
	private static boolean containsVariant(
			List<RuleTrs> rules, RuleTrs candidate) {

		for (RuleTrs rule : rules) {
			Substitution renaming = new Substitution();
			if (rule.getLeft().isMoreGeneralThan(
					candidate.getLeft(), renaming) &&
					rule.getRight().isMoreGeneralThan(
							candidate.getRight(), renaming) &&
					isVariableBijection(renaming))
				return true;
		}
		return false;
	}

	/**
	 * Checks whether a matching substitution is a variable renaming.
	 *
	 * @param substitution the substitution to inspect
	 * @return {@code true} if every image is a distinct variable
	 */
	private static boolean isVariableBijection(Substitution substitution) {
		Set<Variable> images = Collections.newSetFromMap(new IdentityHashMap<>());
		for (Map.Entry<Variable, Term> entry : substitution) {
			if (!(entry.getValue() instanceof Variable variable) ||
					!images.add(variable))
				return false;
		}
		return true;
	}

	/**
	 * Returns a copy of a pair list in which one source pair is replaced by its
	 * instances, retaining the order of all pairs and instances.
	 *
	 * @param pairs the original dependency pairs
	 * @param sourceIndex the index of the pair to replace
	 * @param instances the replacement instances
	 * @return the transformed dependency-pair list
	 */
	private static List<RuleTrs> replace(
			List<RuleTrs> pairs, int sourceIndex, List<RuleTrs> instances) {

		List<RuleTrs> transformed = new ArrayList<>(
				pairs.size() - 1 + instances.size());
		for (int index = 0; index < pairs.size(); index++) {
			if (index == sourceIndex)
				transformed.addAll(instances);
			else
				transformed.add(pairs.get(index));
		}
		return transformed;
	}

	/**
	 * Builds a dependency graph and counts its nodes in cyclic SCCs.
	 *
	 * @param trs the rewrite system defining graph transitions
	 * @param pairs the dependency pairs forming the graph nodes
	 * @return the number of dependency pairs retained by the SCC computation
	 */
	private static int cyclicPairCount(Trs trs, DependencyPairs pairs) {
		return cyclicPairCount(new DependencyGraph(trs, pairs).getSCCs());
	}

	/**
	 * Counts the nodes in an already computed collection of cyclic SCCs.
	 *
	 * @param sccs the cyclic strongly connected components
	 * @return the sum of their numbers of dependency pairs
	 */
	private static int cyclicPairCount(Deque<DependencyPairs> sccs) {
		int count = 0;
		for (DependencyPairs scc : sccs)
			count += scc.size();
		return count;
	}

	/**
	 * Records an accepted transformation and converts its cyclic SCCs into the
	 * finite or decomposed processor result.
	 *
	 * @param problem the original dependency-pair problem
	 * @param transformations the one or two accepted source replacements
	 * @param transformedSccs the cyclic SCCs after all replacements
	 * @param oldCyclicPairCount the cyclic-pair count before the replacements
	 * @param newCyclicPairCount the cyclic-pair count after the replacements
	 * @param proof the proof receiving the transformation certificate
	 * @param indentation the indentation used for proof messages
	 * @return a finite result if no cyclic SCC remains, otherwise the SCC
	 *         decomposition
	 */
	private static DependencyPairProcessorResult successfulResult(
			DependencyPairProblem problem,
			List<Transformation> transformations,
			Deque<DependencyPairs> transformedSccs,
			int oldCyclicPairCount,
			int newCyclicPairCount,
			Proof proof,
			int indentation) {

		for (Transformation transformation : transformations)
			proof.printlnIfVerbose(
					"Forward-instantiated dependency pair " +
							transformation.source() + " into " +
							transformation.instances() + ".", indentation);
		if (transformations.size() == 2)
			proof.printlnIfVerbose(
					"The first step has exactly one matching successor pair; " +
							"the second step is strictly decreasing.", indentation);
		proof.printlnIfVerbose(
				"This decreases the number of cyclic dependency pairs from " +
						oldCyclicPairCount + " to " + newCyclicPairCount + ".",
				indentation);
		if (transformedSccs.isEmpty())
			return DependencyPairProcessorResult.finite(proof);

		DependencyPairProblemCollection subproblems =
				new DependencyPairProblemCollection();
		for (DependencyPairs scc : transformedSccs)
			subproblems.add(new DependencyPairProblem(problem.getTRS(), scc));
		return DependencyPairProcessorResult.decomposed(proof, subproblems);
	}

	/** The information needed to construct an inverse cap. */
	private record InverseCapSymbols(
			Set<FunctionSymbol> rightRoots, boolean collapsing) {}

	/** The generated instances and the number of matching successor pairs. */
	private record Instantiation(
			List<RuleTrs> instances, int unifiablePairCount) {}

	/** One accepted source replacement, retained for the proof certificate. */
	private record Transformation(RuleTrs source, List<RuleTrs> instances) {}

	/** {@inheritDoc} */
	@Override
	public String toString() {
		return "## DP Processor: forward instantiation. ";
	}
}
