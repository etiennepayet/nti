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

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;

/**
 * SAT4J-backed implementation of the bounded SAT interface.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class Sat4jSolver implements SatSolver {

	/**
	 * Solves a CNF formula with SAT4J within the supplied time bound.
	 *
	 * @param formula formula to solve
	 * @param timeoutMilliseconds maximum solving time in milliseconds
	 * @return the SAT result, or an aborted result on timeout or interruption
	 */
	@Override
	public SatResult solve(CnfFormula formula, int timeoutMilliseconds) {
		if (formula.tooLarge() || Thread.currentThread().isInterrupted())
			return SatResult.aborted();

		ISolver solver = SolverFactory.newDefault();
		solver.newVar(formula.variableCount());
		solver.setExpectedNumberOfClauses(formula.clauses().size());
		solver.setTimeoutMs(timeoutMilliseconds);
		try {
			for (int[] clause : formula.clauses()) {
				if (Thread.currentThread().isInterrupted())
					return SatResult.aborted();
				solver.addClause(new VecInt(clause));
			}
			if (!solver.isSatisfiable())
				return SatResult.unsatisfiable();

			boolean[] model = new boolean[formula.variableCount() + 1];
			for (int literal : solver.model())
				if (0 < literal && literal < model.length)
					model[literal] = true;
			return SatResult.satisfiable(model);
		}
		catch (ContradictionException exception) {
			return SatResult.unsatisfiable();
		}
		catch (TimeoutException exception) {
			return SatResult.aborted();
		}
	}
}
