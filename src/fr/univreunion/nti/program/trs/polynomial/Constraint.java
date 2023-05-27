/*
 * Copyright 2022 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.polynomial;

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.term.Variable;

/**
 * A constraint of the form <code>P &gt; 0</code> or
 * <code>P &ge; 0</code> where <code>P</code> is a
 * polynomial.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Constraint {

	/**
	 * The polynomial part of this constraint.
	 */
	private final Polynomial P;

	/**
	 * A boolean indicating whether this constraint
	 * is strict, i.e., has the form <code>P &gt; 0</code>
	 * or <code>P &ge; 0</code>. 
	 */
	private final boolean isStrict;

	/**
	 * The rule from which this constraint was generated
	 * (<code>null</code> if this constraint comes from
	 * no rule).
	 */
	private final RuleTrs R;

	/**
	 * Builds a constraint which is not generated from
	 * any rule.
	 * 
	 * @param P the polynomial part of this constraint
	 * @param isStrict a boolean indicating whether this
	 * constraint is strict
	 */
	public Constraint(Polynomial P, boolean isStrict) {
		this.P = P;
		this.isStrict = isStrict;
		this.R = null;
	}

	/**
	 * Builds a constraint.
	 * 
	 * @param P the polynomial part of this constraint
	 * @param isStrict a boolean indicating whether this
	 * constraint is strict
	 * @param R the rule from which this constraint was
	 * generated (<code>null</code> if this constraint
	 * comes from no rule)
	 */
	public Constraint(Polynomial P, boolean isStrict, RuleTrs R) {
		this.P = P;
		this.isStrict = isStrict;
		this.R = R;
	}

	/**
	 * Returns <code>true</code> iff this constraint is
	 * strict, i.e., has the form <code>P &gt; 0</code>.
	 * 
	 * @return <code>true</code> iff this constraint is
	 * strict
	 */
	public boolean isStrict() {
		return this.isStrict;
	}

	/**
	 * Returns the rule from which this constraint was generated.
	 * 
	 * @return the rule from which this constraint was generated
	 */
	public RuleTrs getRule() {
		return this.R;
	}

	/**
	 * Returns the polynomial part of this constraint.
	 * 
	 * @return the polynomial part of this constraint
	 */
	public Polynomial getPolynomial() {
		return this.P;
	}

	/**
	 * Applies Diff1 or Diff2 of [Giesl, RTA'95]
	 * to this constraint (if this constraint is
	 * strict, then Diff1 is applied, otherwise
	 * Diff2 is applied).
	 * 
	 * @param mu the variable used in [Giesl, RTA'95] for
	 * solving polynomial constraints
	 * @return the constraints resulting from applying
	 * Diff1 or Diff2 of [Giesl, RTA'95] to this constraint
	 */
	public List<Constraint> diff(PolynomialConst mu) {
		// The list to return at the end.
		List<Constraint> result = new LinkedList<Constraint>();

		// First, we replace a variable of this constraint with mu.
		Deque<Variable> l = new LinkedList<Variable>();
		Polynomial P_mu = this.P.replaceWithMu(l, mu);

		// Here, l is supposed to contain at most one variable.
		// Moreover, if l is empty, then this constraint does
		// not contain any variable: if such a situation occurs,
		// we return an empty list of constraints.
		if (!l.isEmpty()) {
			result.add(new Constraint(P_mu, this.isStrict, this.R));
			result.add(new Constraint(this.P.partialDerivative(l.getFirst()), false, this.R));
		}

		return result;
	}

	/**
	 * Returns the list of constraints resulting
	 * from repeated applications of Diff1 and Diff2
	 * [Giesl, RTA'95] to this constraint, until all
	 * rule variables have been removed.
	 * 
	 * If a generated constraint is unsatisfiable,
	 * then <code>null</code> is returned.
	 * 
	 * If some generated constraints yield minimal or
	 * maximal values for some constant polynomials,
	 * then the specified intervals are completed accordingly.
	 * 
	 * @param mu the variable used in [Giesl, RTA'95]
	 * for solving polynomial constraints
	 * @param intervals intervals of values that have to be
	 * used for instantiating some constant polynomials
	 * @return the list of constraints resulting from
	 * repeated applications of Diff1 and Diff2 to this
	 * constraint, or <code>null</code> if a generated
	 * constraint is unsatisfiable
	 */
	public List<Constraint> diffRepeated(PolynomialConst mu, Intervals intervals) {

		// The list to return at the end.
		List<Constraint> result = new LinkedList<Constraint>();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// Some data structures used for computing the
		// repeated applications of Diff1 and Diff2.
		List<Constraint> x = new LinkedList<Constraint>();
		List<Constraint> diffed = new LinkedList<Constraint>();

		diffed.add(this);
		while (!diffed.isEmpty()) {
			x.clear();
			x.addAll(diffed);
			diffed.clear();
			for (Constraint c : x) {
				List<Constraint> cDiff = c.diff(mu);
				// If cDiff is empty, then c does not contain
				// any rule variable. We try to update the
				// previously generated collection of constraints
				// and the intervals using c. If unsatisfiability
				// is detected, then we stop everything and return
				// null.
				if (currentThread.isInterrupted() ||
						(cDiff.isEmpty() && !c.update(result, intervals)))
					return null;
				else
					diffed.addAll(cDiff);
			}
		}

		return result;
	}

	/**
	 * Returns <code>true</code> iff the provided
	 * interpretation satisfies this constraint.
	 * 
	 * @param interpretation an interpretation of
	 * the variables of this constraint
	 * @return <code>true</code> iff the provided
	 * interpretation satisfies this constraint
	 */
	public boolean isTrue(Map<Variable, Integer> interpretation) {
		Integer value = this.P.integerValue(interpretation);

		if (value == null) return false;

		if (this.isStrict) return (0 < value);

		return (0 <= value);
	}

	/**
	 * Returns <code>true</code> iff the provided
	 * interpretation satisfies the non-strict form
	 * of this constraint.
	 * 
	 * @param interpretation an interpretation of
	 * the variables of this constraint
	 * @return <code>true</code> iff the provided
	 * interpretation satisfies the non-strict form
	 * of this constraint
	 */
	public boolean isTrueIfNotStrict(Map<Variable,Integer> interpretation) {
		Integer value = this.P.integerValue(interpretation);

		if (value == null) return false;

		return (0 <= value);
	}

	/**
	 * Tries to check whether this constraint is always
	 * true.
	 * 
	 * If <code>true</code> is returned, then it is sure
	 * that this constraint is always true. Otherwise,
	 * i.e., if <code>false</code> is returned, then we
	 * do not know.
	 * 
	 * @return <code>true</code> if it is sure that
	 * this constraint is always true, or <code>false</code>
	 * if we do not know
	 */
	public boolean isAlwaysTrue() {
		if (this.isStrict) return this.P.gtz();

		return this.P.gez();
	}

	/**
	 * Tries to check whether this constraint is always
	 * false.
	 * 
	 * If <code>true</code> is returned, then it is sure
	 * that this constraint is always false. Otherwise,
	 * i.e., if <code>false</code> is returned, then we
	 * do not know.
	 * 
	 * @return <code>true</code> if it is sure that
	 * this constraint is always false, or <code>false</code>
	 * if we do not know
	 */
	public boolean isAlwaysFalse() {
		if (this.isStrict) return this.P.lez();

		return this.P.ltz();
	}

	/**
	 * Updates the specified intervals using this constraint.
	 * 
	 * If there is a conflict between this constraint and some
	 * limit in <code>intervals</code>, then <code>null</code>
	 * is returned. Otherwise, <code>true</code> is returned iff
	 * <code>intervals</code> is updated (i.e., modified).
	 * 
	 * @param intervals intervals of values that have to be
	 * used for instantiating some constant polynomials
	 * @return <code>null</code>, <code>true</code> or
	 * <code>false</code>
	 */
	private Boolean update(Intervals intervals) {

		// We try to decompose this.P.
		PolynomialConst[] operands = this.P.subOperands();

		if (operands != null) {
			// Here, this.P has the form c0 - c1 where
			// c0 and c1 are constant polynomials.

			PolynomialConst c0 = operands[0];
			Integer v0 = c0.getValue();
			PolynomialConst c1 = operands[1];
			Integer v1 = c1.getValue();

			if (v0 == null && v1 != null) {
				// Here, this.P has the form c0 - v1 >= 0
				// or c0 - v1 > 0, i.e., c0 >= v1 or c0 > v1.
				// Therefore, v1 provides a lower limit for c0.
				if (intervals.putMin(c0, (this.isStrict ? v1 + 1 : v1)))
					return true;
				// Here, there is a conflict between v1 and the upper
				// limit for c0 in 'intervals'.
				return null;
			}

			if (v0 != null && v1 == null) {
				// Here, this.P has the form v0 - c1 >= 0
				// or v0 - c1 > 0, i.e., v0 >= c1 or v0 > c1.
				// Therefore, v0 provides an upper limit for c1.
				if (intervals.putMax(c1, (this.isStrict ? v0 - 1 : v0)))
					return true;
				// Here, there is a conflict between v0 and the lower
				// limit for c1 in 'intervals'.
				return null;
			}
		}

		// Here, 'intervals' has not been modified.
		return false;
	}

	/**
	 * Updates the specified collection of constraints and
	 * the specified intervals using this constraint.
	 * 
	 * If the context defined by the specified elements and
	 * this constraint is unsatisfiable, then <code>false</code>
	 * is returned. Otherwise, <code>true</code> is returned.
	 * 
	 * @param constraints a collection of constraints to be
	 * updated using this constraint
	 * @param intervals some intervals to be updated using
	 * this constraint
	 * @return <code>false</code> if unsatisfiability is
	 * detected
	 */
	public boolean update(Collection<Constraint> constraints,
			Intervals intervals) {

		// First, we check whether the context defined
		// by the specified collection of constraints,
		// the specified intervals and this constraint
		// is unsatisfiable.
		if (this.isAlwaysFalse()) return false;
		Boolean update = this.update(intervals);
		if (update == null) return false;

		// Here, we did not detect unsatisfiability. We
		// update the specified collection of constraints
		// only if this constraint is useful.
		if (!update && !this.isAlwaysTrue())
			constraints.add(this);

		return true;
	}

	/**
	 * Returns a string representation of this constraint
	 * relatively to the given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @return a string representation of this constraint
	 */
	public String toString(Map<Variable,String> variables) {
		return this.P.toString(variables) +
				(this.isStrict ? " > 0" : " >= 0");
	}

	/**
	 * Returns a string representation of this constraint.
	 * 
	 * @return a string representation of this constraint
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<Variable,String>());
	}
}
