/*
 * Copyright 2025 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech.dependencypair.processor;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblemCollection;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairProblem;

/**
 * A result provided by a dependency pair processor.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class DependencyPairProcessorResult {

	/**
	 * A value indicating whether a dependency pair
	 * problem could be proved finite or infinite, or
	 * be decomposed into a set of subproblems.
	 * 
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	private enum ResultType {
		FINITE,
		INFINITE,
		DECOMPOSED,
		FAILED
	}

	/**
	 * Returns a result indicating that a dependency pair
	 * problem could be proved finite.
	 * 
	 * @param proof the proof of the returned result
	 */
	public static DependencyPairProcessorResult finite(Proof proof) {
		return new DependencyPairProcessorResult(ResultType.FINITE, null, proof);
	}

	/**
	 * Returns a result indicating that a dependency pair
	 * problem could be proved infinite.
	 * 
	 * @param proof the proof of the returned result
	 */
	public static DependencyPairProcessorResult infinite(Proof proof) {
		return new DependencyPairProcessorResult(ResultType.INFINITE, null, proof);
	}

	/**
	 * Returns a result indicating that a dependency pair
	 * problem could be decomposed into subproblems.
	 * 
	 * @param proof the proof of the returned result
	 */
	public static DependencyPairProcessorResult decomposed(Proof proof) {
		return new DependencyPairProcessorResult(ResultType.DECOMPOSED, new DependencyPairProblemCollection(), proof);
	}

	/**
	 * Returns a result indicating that a dependency pair
	 * problem could be decomposed into the specified
	 * subproblems.
	 * 
	 * @param proof the proof of the returned result
	 * @param subproblems the subproblems of the
	 * returned result
	 */
	public static DependencyPairProcessorResult decomposed(Proof proof,
			DependencyPairProblemCollection subproblems) {

		return new DependencyPairProcessorResult(
				ResultType.DECOMPOSED,
				subproblems,
				proof);
	}

	/**
	 * Returns a result indicating that a dependency pair
	 * problem could not be proved finite nor infinite,
	 * nor be decomposed into subproblems.
	 * 
	 * @param proof the proof of the returned result
	 */
	public static DependencyPairProcessorResult failed(Proof proof) {
		return new DependencyPairProcessorResult(ResultType.FAILED, null, proof);
	}

	/**
	 * A value indicating whether the dependency pair processor
	 * could prove finiteness or infiniteness of a dependency
	 * pair problem, or decompose it into a set of subproblems.
	 */
	private final ResultType type;

	/**
	 * A collection of new dependency pair problems to solve,
	 * computed by the dependency pair processor. These problems
	 * are subproblems of the dependency pair problem that has
	 * been processed.
	 */
	private final DependencyPairProblemCollection subproblems;

	/**
	 * The proof computed by the dependency pair processor.
	 */
	private final Proof proof;

	/**
	 * Builds a result provided by a dependency pair processor.
	 * 
	 * @param type the type of this result, indicating
	 * whether the dependency pair processor could prove
	 * finiteness or infiniteness of a dependency pair problem,
	 * or decompose it into a set of subproblems
	 * @param subproblems the subproblems of this result
	 * @param proof the proof of this result
	 */
	private DependencyPairProcessorResult(ResultType type, DependencyPairProblemCollection subproblems, Proof proof) {
		this.type = type;
		this.subproblems = subproblems;
		this.proof = proof;
	}

	/**
	 * Returns the subproblems of this result.
	 * 
	 * @return the subproblems of this result
	 */
	public DependencyPairProblemCollection getSubproblems() {
		return this.subproblems;
	}

	/**
	 * Returns the proof of this result.
	 * 
	 * @return the proof of this result
	 */
	public Proof getProof() {
		return this.proof;
	}

	/**
	 * Adds the specified subproblem to this result.
	 * 
	 * @param sp a dependency pair subproblem to add to this result
	 * @return <code>true</code> iff this result changed
	 * as a result of the call
	 */
	public boolean add(DependencyPairProblem sp) {
		return (this.subproblems != null && this.subproblems.add(sp));
	}

	/**
	 * Checks whether this result indicates that a
	 * dependency pair problem could be proved finite.
	 * 
	 * @return <code>true</code> iff this result
	 * indicates that a dependency pair problem could be proved
	 * finite
	 */
	public boolean isFinite() {
		return this.type == ResultType.FINITE;
	}

	/**
	 * Checks whether this result indicates that a
	 * dependency pair problem could be proved infinite.
	 * 
	 * @return <code>true</code> iff this result
	 * indicates that a dependency pair problem could be proved
	 * infinite
	 */
	public boolean isInfinite() {
		return this.type == ResultType.INFINITE;
	}

	/**
	 * Checks whether this result indicates that a dependency
	 * pair problem could be decomposed into subproblems.
	 * 
	 * @return <code>true</code> iff this result
	 * indicates that a dependency pair problem could be decomposed
	 * into subproblems
	 */
	public boolean isDecomposed() {
		return this.type == ResultType.DECOMPOSED;
	}

	/**
	 * Checks whether this result indicates that a dependency
	 * pair problem could not be proved finite nor infinite,
	 * nor be decomposed.
	 * 
	 * @return <code>true</code> iff this result
	 * indicates that a dependency pair problem could not be proved
	 * finite nor infinite, nor be decomposed
	 */
	public boolean isFailed() {
		return this.type == ResultType.FAILED;
	}

	/**
	 * Returns a String representation of this result.
	 */
	@Override
	public String toString() {
		return this.type.toString();
	}
}
