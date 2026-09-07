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
import java.util.Collection;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.dependencypair.DependencyPairs;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Term;

/**
 * Applies the simple-projection subterm criterion to a dependency pair
 * problem.
 *
 * <p>This is the subterm criterion of N. Hirokawa and A. Middeldorp,
 * <a href="https://doi.org/10.1007/978-3-540-25979-4_18"><i>Dependency Pairs
 * Revisited</i></a>, RTA 2004, LNCS 3091, pp. 249--268, especially Sect. 3
 * and Theorem 11.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class SubtermCriterionDependencyPairProcessor
		extends FinitenessDependencyPairProcessor {

	/** Maximum number of complete simple projections inspected. */
	private static final int MAX_PROJECTION_COUNT = 50_000;

	/** Builds a processor that does not use argument filtering. */
	public SubtermCriterionDependencyPairProcessor() {
		super(false);
	}

	@Override
	protected DependencyPairProcessorResult run(
			DependencyPairProblem problem,
			ArgFiltering filtering,
			Collection<PairOfTerms> trsPairs,
			Collection<PairOfTerms> dependencyPairs,
			int indentation,
			AnalysisContext context) {

		Proof proof = context.createProof();
		this.printFiltering(filtering, proof, indentation);
		ProjectionSearch search = search(dependencyPairs);
		if (search.tooLarge()) {
			proof.printlnIfVerbose(
					"Too many simple projections (more than " +
							MAX_PROJECTION_COUNT + ")! Aborting!", indentation);
			return DependencyPairProcessorResult.failed(proof);
		}
		Projection projection = search.best();
		if (projection == null)
			return DependencyPairProcessorResult.failed(proof);

		List<RuleTrs> nonStrictRules = new ArrayList<>();
		for (PairOfTerms pair : dependencyPairs)
			if (project(pair.left(), projection.positions()).deepEquals(
					project(pair.right(), projection.positions())))
				nonStrictRules.add(pair.rule());

		return buildResult(
				problem, projection, nonStrictRules, proof, indentation);
	}

	/** Removes strict pairs and applies the SCC processor to the remainder. */
	private static DependencyPairProcessorResult buildResult(
			DependencyPairProblem problem,
			Projection projection,
			Collection<RuleTrs> nonStrictRules,
			Proof proof,
			int indentation) {

		proof.printlnIfVerbose(projection.toString(indentation));
		if (nonStrictRules.isEmpty())
			return DependencyPairProcessorResult.finite(proof);

		Trs trs = problem.getTRS();
		Deque<DependencyPairs> sccs =
				trs.getDependencyGraph().getSCCs(nonStrictRules);
		if (sccs.isEmpty())
			return DependencyPairProcessorResult.finite(proof);

		DependencyPairProcessorResult result =
				DependencyPairProcessorResult.decomposed(proof);
		for (DependencyPairs scc : sccs)
			result.add(new DependencyPairProblem(trs, scc));
		return result;
	}

	/** Searches all bounded simple projections and retains the strongest one. */
	private static ProjectionSearch search(Collection<PairOfTerms> pairs) {
		if (pairs.isEmpty())
			return new ProjectionSearch(null, false);

		LinkedHashMap<FunctionSymbol, Integer> arities = new LinkedHashMap<>();
		for (PairOfTerms pair : pairs) {
			FunctionSymbol left = pair.left().getRootSymbol();
			FunctionSymbol right = pair.right().getRootSymbol();
			if (left == null || right == null ||
					left.getArity() == 0 || right.getArity() == 0)
				return new ProjectionSearch(null, false);
			arities.putIfAbsent(left, left.getArity());
			arities.putIfAbsent(right, right.getArity());
		}

		long projectionCount = 1;
		for (int arity : arities.values()) {
			projectionCount *= arity;
			if (projectionCount > MAX_PROJECTION_COUNT)
				return new ProjectionSearch(null, true);
		}

		ProjectionEnumerator enumerator = new ProjectionEnumerator(
				List.copyOf(arities.keySet()), arities, List.copyOf(pairs));
		enumerator.search(0);
		return new ProjectionSearch(enumerator.best, false);
	}

	/** Returns the argument selected at the root by a projection. */
	private static Term project(
			Term term, Map<FunctionSymbol, Integer> positions) {

		return term.get(positions.get(term.getRootSymbol()));
	}

	/** One bounded enumeration of simple projections. */
	private static final class ProjectionEnumerator {
		private final List<FunctionSymbol> symbols;
		private final Map<FunctionSymbol, Integer> arities;
		private final List<PairOfTerms> pairs;
		private final Map<FunctionSymbol, Integer> current = new LinkedHashMap<>();
		private Projection best;

		private ProjectionEnumerator(
				List<FunctionSymbol> symbols,
				Map<FunctionSymbol, Integer> arities,
				List<PairOfTerms> pairs) {

			this.symbols = symbols;
			this.arities = arities;
			this.pairs = pairs;
		}

		/** Enumerates assignments in symbol and argument order. */
		private boolean search(int symbolIndex) {
			if (Thread.currentThread().isInterrupted())
				return true;
			if (symbolIndex == this.symbols.size())
				return this.retainCompleteProjection();

			FunctionSymbol symbol = this.symbols.get(symbolIndex);
			for (int position = 0;
					position < this.arities.get(symbol); position++) {
				this.current.put(symbol, position);
				if (this.isCompatibleSoFar() && this.search(symbolIndex + 1))
					return true;
			}
			this.current.remove(symbol);
			return false;
		}

		/** Rejects an assignment as soon as one fully projected pair grows. */
		private boolean isCompatibleSoFar() {
			for (PairOfTerms pair : this.pairs) {
				FunctionSymbol left = pair.left().getRootSymbol();
				FunctionSymbol right = pair.right().getRootSymbol();
				if (this.current.containsKey(left) &&
						this.current.containsKey(right) &&
						!isSupertermOrEqual(
								project(pair.left(), this.current),
								project(pair.right(), this.current)))
					return false;
			}
			return true;
		}

		/** Retains a projection if it removes more dependency pairs. */
		private boolean retainCompleteProjection() {
			int nonStrictCount = 0;
			for (PairOfTerms pair : this.pairs)
				if (project(pair.left(), this.current).deepEquals(
						project(pair.right(), this.current)))
					nonStrictCount++;
			if (nonStrictCount == this.pairs.size())
				return false;
			if (this.best == null || nonStrictCount < this.best.nonStrictCount())
				this.best = new Projection(
						new LinkedHashMap<>(this.current), nonStrictCount);
			return nonStrictCount == 0;
		}

		/** Tests the reflexive syntactic superterm relation. */
		private static boolean isSupertermOrEqual(Term source, Term target) {
			if (source.deepEquals(target))
				return true;
			for (Position position : source)
				if (source.get(position).deepEquals(target))
					return true;
			return false;
		}
	}

	/** The result of a bounded projection search. */
	private record ProjectionSearch(Projection best, boolean tooLarge) {}

	/** One simple projection and its number of retained dependency pairs. */
	private record Projection(
			Map<FunctionSymbol, Integer> positions,
			int nonStrictCount) {

		public String toString(int indentation) {
			StringBuilder result = new StringBuilder(
					" ".repeat(Math.max(0, indentation)))
					.append("Simple projection: {");
			boolean first = true;
			for (Map.Entry<FunctionSymbol, Integer> entry :
					this.positions.entrySet()) {
				if (first)
					first = false;
				else
					result.append(", ");
				result.append(entry.getKey()).append(" -> ")
						.append(entry.getValue() + 1);
			}
			return result.append('}').toString();
		}
	}

	@Override
	public String toString() {
		return "## DP Processor: subterm criterion. ";
	}
}
