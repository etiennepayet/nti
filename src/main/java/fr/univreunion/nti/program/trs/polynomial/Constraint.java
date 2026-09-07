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
 * <p>The Diff1 and Diff2 transformations are from J. Giesl,
 * <a href="https://doi.org/10.1007/3-540-59200-8_77">Generating Polynomial
 * Orderings for Termination Proofs</a>, RTA 1995, LNCS 914, 426--431.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Constraint {

	/**
	 * The polynomial part of this constraint.
	 */
	private final Polynomial polynomial;

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
	private final RuleTrs rule;

	/**
	 * Builds a constraint which is not generated from
	 * any rule.
	 * 
	 * @param polynomial the polynomial part of this constraint
	 * @param isStrict a boolean indicating whether this
	 * constraint is strict
	 */
	public Constraint(Polynomial polynomial, boolean isStrict) {
		this.polynomial = polynomial;
		this.isStrict = isStrict;
		this.rule = null;
	}

	/**
	 * Builds a constraint.
	 * 
	 * @param polynomial the polynomial part of this constraint
	 * @param isStrict a boolean indicating whether this
	 * constraint is strict
	 * @param rule the rule from which this constraint was
	 * generated (<code>null</code> if this constraint
	 * comes from no rule)
	 */
	public Constraint(Polynomial polynomial, boolean isStrict, RuleTrs rule) {
		this.polynomial = polynomial;
		this.isStrict = isStrict;
		this.rule = rule;
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
		return this.rule;
	}

	/**
	 * Returns the polynomial part of this constraint.
	 * 
	 * @return the polynomial part of this constraint
	 */
	public Polynomial getPolynomial() {
		return this.polynomial;
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
		List<Constraint> result = new LinkedList<>();

		// First, we replace a variable of this constraint with mu.
		Deque<Variable> l = new LinkedList<>();
		Polynomial polynomialWithMu = this.polynomial.replaceWithMu(l, mu);

		// Here, l is supposed to contain at most one variable.
		// Moreover, if l is empty, then this constraint does
		// not contain any variable: if such a situation occurs,
		// we return an empty list of constraints.
		if (!l.isEmpty()) {
			result.add(new Constraint(polynomialWithMu, this.isStrict, this.rule));
			result.add(new Constraint(this.polynomial.partialDerivative(l.getFirst()), false, this.rule));
		}

		return result;
	}

	/**
	 * Returns the list of constraints resulting
	 * from repeated applications of Diff1 and Diff2
	 * [Giesl, RTA'95] to this constraint, until all
	 * rule variables have been removed.
	 * <p>
	 * If a generated constraint is unsatisfiable,
	 * then <code>null</code> is returned.
	 * <p>
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
		List<Constraint> result = new LinkedList<>();

		// The thread running this method.
		Thread currentThread = Thread.currentThread();

		// Some data structures used for computing the
		// repeated applications of Diff1 and Diff2.
		List<Constraint> x = new LinkedList<>();
		List<Constraint> diffed = new LinkedList<>();

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
	 * Returns <code>true</code> iff the provided interpretation
	 * does not satisfy this constraint.
	 * 
	 * @param interpretation an interpretation of
	 * the variables of this constraint
	 * @return <code>true</code> iff the provided interpretation
	 * does not satisfy this constraint
	 */
	public boolean isUnsatisfied(Map<Variable, Integer> interpretation) {
		Integer value = this.polynomial.integerValue(interpretation);

		if (value == null) return true;

		if (this.isStrict) return (value <= 0);

		return (value < 0);
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
		Integer value = this.polynomial.integerValue(interpretation);

		if (value == null) return false;

		return (0 <= value);
	}

	/**
	 * Tries to check whether this constraint is always
	 * true.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that this constraint is always true. Otherwise,
	 * i.e., if <code>false</code> is returned, then we
	 * do not know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * this constraint is always true, or <code>false</code>
	 * if we do not know
	 */
	public boolean isAlwaysTrue() {
		if (this.isStrict) return this.polynomial.gtz();

		return this.polynomial.gez();
	}

	/**
	 * Tries to check whether this constraint is always
	 * false.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that this constraint is always false. Otherwise,
	 * i.e., if <code>false</code> is returned, then we
	 * do not know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * this constraint is always false, or <code>false</code>
	 * if we do not know
	 */
	public boolean isAlwaysFalse() {
		if (this.isStrict) return this.polynomial.lez();

		return this.polynomial.ltz();
	}

	/**
	 * Updates the specified intervals using this constraint.
	 * <p>
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

		// We try to decompose the polynomial part.
		PolynomialConst[] operands = this.polynomial.subOperands();
		if (operands == null)
			return false;

		// Here, the polynomial part has the form c0 - c1 where
		// c0 and c1 are constant polynomials.
		PolynomialConst c0 = operands[0];
		Integer v0 = c0.getValue();
		PolynomialConst c1 = operands[1];
		Integer v1 = c1.getValue();

		if (v0 == null && v1 != null)
			return this.updateMin(intervals, c0, v1);

		if (v0 != null && v1 == null)
			return this.updateMax(intervals, c1, v0);

		// Here, 'intervals' has not been modified.
		return false;
	}

	/**
	 * Updates the lower limit of a constant polynomial.
	 *
	 * @param intervals the intervals to update
	 * @param constant the constant polynomial whose lower limit is updated
	 * @param value the value providing the lower limit
	 * @return <code>true</code> on success, or <code>null</code> on conflict
	 */
	private Boolean updateMin(
			Intervals intervals, PolynomialConst constant, int value) {
		int min = this.isStrict ? value + 1 : value;
		return intervals.putMin(constant, min) ? true : null;
	}

	/**
	 * Updates the upper limit of a constant polynomial.
	 *
	 * @param intervals the intervals to update
	 * @param constant the constant polynomial whose upper limit is updated
	 * @param value the value providing the upper limit
	 * @return <code>true</code> on success, or <code>null</code> on conflict
	 */
	private Boolean updateMax(
			Intervals intervals, PolynomialConst constant, int value) {
		int max = this.isStrict ? value - 1 : value;
		return intervals.putMax(constant, max) ? true : null;
	}

	/**
	 * Updates the specified collection of constraints and
	 * the specified intervals using this constraint.
	 * <p>
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
		return this.polynomial.toString(variables) +
				(this.isStrict ? " > 0" : " >= 0");
	}

	/**
	 * Returns a string representation of this constraint.
	 * 
	 * @return a string representation of this constraint
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
