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
import java.util.Arrays;
import java.util.List;

/**
 * A bounded in-memory CNF formula using signed integer literals.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class CnfFormula {

	/** Distinguished variable constrained to logical truth. */
	private static final int TRUE_LITERAL = 1;

	/** Maximum number of variables that may be allocated. */
	private final int maximumVariableCount;
	/** Maximum number of clauses that may be stored. */
	private final int maximumClauseCount;
	/** Clauses stored as arrays of signed integer literals. */
	private final List<int[]> clauses = new ArrayList<>();
	/** Number of variables allocated so far. */
	private int variableCount = TRUE_LITERAL;
	/** Whether a configured size bound has been exceeded. */
	private boolean tooLarge;

	/**
	 * Creates an initially true bounded formula.
	 *
	 * @param maximumVariableCount maximum number of allocated variables
	 * @param maximumClauseCount maximum number of stored clauses
	 */
	CnfFormula(int maximumVariableCount, int maximumClauseCount) {
		this.maximumVariableCount = maximumVariableCount;
		this.maximumClauseCount = maximumClauseCount;
		this.clauses.add(new int[] {TRUE_LITERAL});
	}

	/**
	 * Allocates a propositional variable.
	 *
	 * @return the positive literal of the new variable, or the distinguished
	 *         true literal after the variable bound has been reached
	 */
	int newVariable() {
		if (this.variableCount >= this.maximumVariableCount) {
			this.tooLarge = true;
			return TRUE_LITERAL;
		}
		return ++this.variableCount;
	}

	/**
	 * Returns the distinguished literal constrained to true.
	 *
	 * @return the true literal
	 */
	int trueLiteral() {
		return TRUE_LITERAL;
	}

	/**
	 * Adds one disjunctive clause after simplifying true and false constants.
	 *
	 * @param literals signed integer literals forming the clause
	 */
	void addClause(int... literals) {
		if (this.tooLarge)
			return;
		int[] simplified = new int[literals.length];
		int size = 0;
		for (int literal : literals) {
			if (literal == TRUE_LITERAL)
				return;
			if (literal != -TRUE_LITERAL)
				simplified[size++] = literal;
		}
		if (this.clauses.size() >= this.maximumClauseCount) {
			this.tooLarge = true;
			return;
		}
		this.clauses.add(Arrays.copyOf(simplified, size));
	}

	/**
	 * Adds one clause represented as boxed signed literals.
	 *
	 * @param literals signed integer literals forming the clause
	 */
	void addClause(List<Integer> literals) {
		int[] values = new int[literals.size()];
		for (int index = 0; index < literals.size(); index++)
			values[index] = literals.get(index);
		addClause(values);
	}

	/**
	 * Returns the number of variables allocated so far.
	 *
	 * @return the variable count, including the distinguished true variable
	 */
	int variableCount() {
		return this.variableCount;
	}

	/**
	 * Returns the stored clauses in insertion order.
	 *
	 * @return the internal list of clauses
	 */
	List<int[]> clauses() {
		return this.clauses;
	}

	/**
	 * Reports whether a configured formula bound has been exceeded.
	 *
	 * @return {@code true} if no further clauses or variables may be added
	 */
	boolean tooLarge() {
		return this.tooLarge;
	}
}
