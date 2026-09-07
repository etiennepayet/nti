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

package fr.univreunion.nti.program.recurrentpair;

import java.util.ArrayList;
import java.util.List;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Hole;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Utilities for recognizing and decomposing towers of contexts.
 * <p>
 * This class is stateless: all methods operate only on their parameters
 * and local variables.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

final class ContextTower {

	/**
	 * A ground context together with its power.
	 *
	 * @param power the power of the context
	 * @param context the ground context
	 */
	record GroundContext(int power, Term context) {}

	/**
	 * One context layer and the corresponding children that contain the
	 * distinguished variable.
	 *
	 * @param context the context built from the layer
	 * @param variableChildren the children replaced by holes in the context
	 */
	private record ContextLayer(Term context, List<Term> variableChildren) {}

	/**
	 * This class cannot be instantiated.
	 */
	private ContextTower() {}

	/**
	 * Checks whether <code>c_y = c^n[y]</code> for a
	 * <em>ground</em> context <code>c</code> (that
	 * possibly contains several occurrences of the
	 * provided hole). If so, then returns
	 * <code>c</code> and the largest possible
	 * <code>n</code>, otherwise returns
	 * <code>null</code>.
	 * <p>
	 * <code>c_y</code> is supposed to be a term
	 * whose only variable is <code>y</code>.
	 * Moreover, the context <code>c</code> is
	 * supposed to be <code>square</code> or to
	 * have the following form: f(t_1,...,t_n)
	 * where, for each i, t_i is square or it
	 * does not contain square.
	 *
	 * @param outerTerm the outer term <code>c_y</code>
	 * from which a context is built
	 * @param y the inner term from which a
	 * context is built
	 * @param square the hole to be used while
	 * building the context
	 * @return a ground context together with a
	 * non-negative integer, or <code>null</code>
	 * if no context could be built from the provided
	 * terms
	 */
	static synchronized GroundContext groundContextFrom(
			Term outerTerm, Variable y, Hole square) {

		if (outerTerm == y) return new GroundContext(0, square);
		if (!(outerTerm instanceof Function outerFunction)) return null;

		ContextLayer contextLayer = buildContextLayer(outerFunction, square);
		Integer contextPower = commonPowerOf(
				contextLayer.variableChildren(), contextLayer.context(), y);
		if (contextPower == null) return null;

		// We return contextPower + 1 because contextPower is
		// the power of c relative to a direct subterm of c_y,
		// i.e., c_y = c[c^contextPower[y]].
		return new GroundContext(contextPower + 1, contextLayer.context());
	}

	/**
	 * Builds the outer context layer and collects the children replaced by its
	 * holes.
	 *
	 * @param outerFunction the function forming the outer layer
	 * @param square the hole used in the context
	 * @return the context layer
	 */
	private static ContextLayer buildContextLayer(
			Function outerFunction, Hole square) {
		FunctionSymbol rootSymbol = outerFunction.getRootSymbol();
		int arity = rootSymbol.getArity();
		List<Term> contextArguments = new ArrayList<>(arity);
		List<Term> variableChildren = new ArrayList<>();
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++) {
			Term child = outerFunction.get(argumentIndex);
			if (child.isGround())
				// Since it is ground, child does not contain y.
				contextArguments.add(child);
			else {
				contextArguments.add(square);
				variableChildren.add(child);
			}
		}

		return new ContextLayer(
				new Function(rootSymbol, contextArguments), variableChildren);
	}

	/**
	 * Computes the common context power of the specified direct children.
	 *
	 * @param variableChildren the children containing the distinguished variable
	 * @param context the context whose power is computed
	 * @param variable the distinguished variable
	 * @return the common power, {@code -1} for no child, or {@code null} if the
	 * children do not have a common power
	 */
	private static Integer commonPowerOf(
			List<Term> variableChildren, Term context, Variable variable) {
		int contextPower = -1;
		for (Term child : variableChildren) {
			// child is a direct subterm of c_y.
			int childPower = powerOf(child, context, variable);
			if (childPower < 0) return null;
			if (contextPower == -1) contextPower = childPower;
			else if (childPower != contextPower) return null;
		}

		return contextPower;
	}

	/**
	 * Checks whether <code>term</code> has the form
	 * <code>c^n[base]</code>, where <code>c</code>
	 * denotes <code>context</code>, for some <code>n</code>.
	 * If so, then returns <code>n</code>. Otherwise,
	 * returns a negative integer.
	 * <p>
	 * In particular, a negative integer is returned if
	 * <code>context</code> does not contain any hole.
	 *
	 * @param term a term to be checked
	 * @param context a context <code>c</code> (possibly
	 * with several holes)
	 * @param base a base term
	 * @return <code>n</code> if it exists, otherwise a
	 * negative integer
	 */
	static synchronized int powerOf(Term term, Term context, Term base) {
		// If term is equal to base, then term = c^0[base].
		if (term.deepEquals(base)) return 0;

		FunctionSymbol rootSymbol = term.getRootSymbol();
		if (rootSymbol != context.getRootSymbol()) return -1;

		return powerOfMatchingLayer(term, context, base, rootSymbol.getArity());
	}

	/**
	 * Computes the power below a term layer whose root matches the context root.
	 *
	 * @param term the term whose current layer matches the context root
	 * @param context the context whose power is computed
	 * @param base the expected base term
	 * @param arity the arity of the common root symbol
	 * @return the power below this layer, or a negative integer on failure
	 */
	private static int powerOfMatchingLayer(
			Term term, Term context, Term base, int arity) {
		int towerPower = -2;
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++) {
			Term contextChild = context.get(argumentIndex);
			Term termChild = term.get(argumentIndex);
			if (contextChild instanceof Hole) {
				int childTowerPower = powerOf(termChild, context, base);
				if (childTowerPower < 0) return -1;
				// The first hole establishes the power; all other holes must
				// produce the same value.
				if (towerPower < 0) towerPower = childTowerPower;
				else if (towerPower != childTowerPower) return -1;
			}
			else if (!contextChild.deepEquals(termChild))
				return -1;
		}

		return towerPower + 1;
	}

	/**
	 * Checks whether <code>term</code> has the form
	 * <code>c^n[base]</code>, where <code>c</code>
	 * denotes <code>context</code>, for some term
	 * <code>base</code>. If so, then returns
	 * <code>base</code>. Otherwise, returns
	 * <code>null</code>.
	 * <p>
	 * In particular, <code>null</code> is returned
	 * if <code>context</code> does not contain any hole.
	 *
	 * @param term a term to be checked
	 * @param context a context <code>c</code> (possibly
	 * with several holes)
	 * @param power a non-negative integer
	 * @return <code>base</code> if it exists, or
	 * <code>null</code> otherwise
	 */
	static synchronized Term baseOf(Term term, Term context, int power) {
		// We have term = context^0[term].
		if (power <= 0) return term;

		FunctionSymbol rootSymbol = term.getRootSymbol();
		if (rootSymbol != context.getRootSymbol()) return null;

		return baseOfMatchingLayer(
				term, context, power, rootSymbol.getArity());
	}

	/**
	 * Extracts the common base below a term layer whose root matches the context
	 * root.
	 *
	 * @param term the term whose current layer matches the context root
	 * @param context the context from which the base is extracted
	 * @param power the remaining context power
	 * @param arity the arity of the common root symbol
	 * @return the common base, or {@code null} on failure
	 */
	private static Term baseOfMatchingLayer(
			Term term, Term context, int power, int arity) {
		Term base = null;
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++) {
			Term contextChild = context.get(argumentIndex);
			Term termChild = term.get(argumentIndex);
			if (contextChild instanceof Hole) {
				Term childBase = baseOf(termChild, context, power - 1);
				if (childBase == null) return null;
				if (base == null) base = childBase;
				else if (!childBase.deepEquals(base)) return null;
			}
			else if (!contextChild.deepEquals(termChild))
				return null;
		}

		return base;
	}
}
