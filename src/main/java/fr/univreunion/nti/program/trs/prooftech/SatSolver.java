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

/**
 * Solves one bounded propositional CNF formula.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

interface SatSolver {

	/**
	 * Solves a bounded CNF formula.
	 *
	 * @param formula formula to solve
	 * @param timeoutMilliseconds maximum solving time in milliseconds
	 * @return the satisfiability status and, when available, a model
	 */
	SatResult solve(CnfFormula formula, int timeoutMilliseconds);

	/**
	 * Result of a bounded SAT call.
	 *
	 * @param status solving status
	 * @param model one-based Boolean model, or {@code null} without a model
	 */
	record SatResult(Status status, boolean[] model) {
		/** Possible outcomes of a bounded SAT call. */
		enum Status {
			/** A satisfying assignment was found. */
			SATISFIABLE,
			/** The formula was proved unsatisfiable. */
			UNSATISFIABLE,
			/** The call stopped because of a bound or interruption. */
			ABORTED
		}

		/**
		 * Creates a satisfiable result.
		 *
		 * @param model one-based Boolean model
		 * @return a satisfiable result carrying the model
		 */
		static SatResult satisfiable(boolean[] model) {
			return new SatResult(Status.SATISFIABLE, model);
		}

		/**
		 * Creates an unsatisfiable result.
		 *
		 * @return an unsatisfiable result
		 */
		static SatResult unsatisfiable() {
			return new SatResult(Status.UNSATISFIABLE, null);
		}

		/**
		 * Creates an aborted result.
		 *
		 * @return a result denoting interruption, timeout or a size bound
		 */
		static SatResult aborted() {
			return new SatResult(Status.ABORTED, null);
		}
	}
}
