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

package fr.univreunion.nti.term.pattern;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A set of methods for manipulating pattern terms.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class PatternUtils {

	/**
	 * Prevents instantiation of this utility class.
	 */
	private PatternUtils() {
	}

	/**
	 * Returns the term <code>c^n(t)</code>, which
	 * results from embedding <code>c</code>
	 * <code>n</code> times into itself.
	 *
	 * @param context a 1-context whose hole is
	 * <code>contextVariable</code>
	 * @param contextVariable the unique variable of the context
	 * @param embeddingCount the number of embeddings of the context
	 * @param baseTerm the base term
	 * @return the term <code>c^n(t)</code>
	 */
	public static synchronized Term embed(
			Term context,
			Variable contextVariable,
			int embeddingCount,
			Term baseTerm) {
		Term result;

		if (0 < embeddingCount) {
			Substitution embeddingSubstitution = new Substitution();
			embeddingSubstitution.add(contextVariable, context);

			result = context.shallowCopy(); // result = c^1(x)
			for (int embeddingIndex = 1;
					embeddingIndex < embeddingCount; embeddingIndex++)
				// Here, result = c^i(x).
				result.applyInPlace(embeddingSubstitution);
				// Here, result = c^{i+1}(x).

			// Here, result = c^n(x).

			embeddingSubstitution.addReplace(contextVariable, baseTerm);
			result.applyInPlace(embeddingSubstitution); // this makes a shallow copy of t
			// Here, result = c^n(t).
		}
		else result = baseTerm.shallowCopy();

		return result;
	}

	/**
	 * Tries to compute the smallest ground 1-context
	 * <code>c</code> such that <code>s = c^a(x)</code>
	 * for some natural <code>a</code>.
	 * <p>
	 * Only contexts of the following form are considered:
	 * <code>f(t_1,...,t_n)</code> where each <code>t_i</code>
	 * is <code>x</code> or does not contain <code>x</code>.
	 * <p>
	 * Upon success, this method stores the computed exponent
	 * <code>a</code> in the first cell of the provided array.
	 *
	 * @param term a term
	 * @param variable a variable occurring in <code>term</code>
	 * @param exponent an array for storing the computed exponent
	 * <code>a</code>
	 * @return the computed context, or <code>null</code>
	 * if no context could be computed
	 * @throws ArithmeticException if the computed exponent cannot be represented
	 * as an <code>int</code>
	 */
	public static synchronized Term getContext(
			Term term, Variable variable, int[] exponent) {

		exponent[0] = 0;

		if (term == variable) return term;

		if (term.isVariable() || !term.getVariables().contains(variable))
			return null;

		// From here, term is not a variable and contains variable.

		FunctionSymbol rootSymbol = term.getRootSymbol();

		// The arguments of the context we build.
		List<Term> contextArguments = new ArrayList<>();

		// First, we complete the argument list of the context.
		Term holeContent = null; // the term occurring in every hole
		for (int argumentIndex = 0;
				argumentIndex < rootSymbol.getArity(); argumentIndex++) {
			Term child = term.get(argumentIndex);
			if (child.isGround()) {
				// child is ground: it does not correspond to a hole.
				contextArguments.add(child);
				continue;
			}

			// child is not ground: it corresponds to a hole.
			contextArguments.add(variable);
			if (holeContent == null)
				holeContent = child;
			else if (!child.deepEquals(holeContent))
				return null;
		}

		// Then, we build the context. It has the form
		// f(t_1,...,t_n) where each t_i is x or is a
		// ground term.
		Function context = new Function(rootSymbol, contextArguments);

		// Finally, we compute the number of times
		// the context is embedded into itself.
		exponent[0] = Math.incrementExact(towerOfContexts(
				holeContent, context, variable, variable));
		if (exponent[0] <= 0) return null;

		return context;
	}

	/**
	 * Computes a simplified version of the specified term
	 * relatively to the specified substitution.
	 * <p>
	 * It is supposed that the domain of <code>theta</code>
	 * is included in the set of variables of <code>s</code>.
	 * <p>
	 * The mappings of <code>theta</code> of the form
	 * <code>x -> c^{a_1,...,a_l,b}(t)</code> are considered.
	 * Suppose that there are naturals <code>k</code>
	 * such that each occurrence of <code>x</code> in
	 * <code>s</code> appears in <code>c^k(x)</code>.
	 * Then, we consider the maximum <code>k'</code> of
	 * these <code>k</code>'s: all occurrences of
	 * <code>c^k(x)</code> in <code>s</code> are
	 * replaced, in a copy of <code>s</code>, by
	 * <code>x</code> and
	 * <code>x -> c^{a_1,...,a_l,b}(t)</code>
	 * in <code>theta</code> is replaced by
	 * <code>x -> c^{a_1,...,a_l,b+k'}(t)</code>.
	 * <p>
	 * The term <code>s</code> is not modified by
	 * this method. On the contrary, the mappings
	 * of <code>theta</code> may be modified as
	 * explained above.
	 *
	 * @param term the term to simplify
	 * @param substitution the substitution to use for the
	 * simplification
	 * @return the simplified term
	 * @throws ArithmeticException if a shifted closing exponent cannot be
	 * represented as an <code>int</code>
	 */
	public static synchronized Term simplify(
			Term term, Substitution substitution) {
		Objects.requireNonNull(term, "term");
		Objects.requireNonNull(substitution, "substitution");

		Term simplifiedTerm = term;
		Map<Variable, Map<Position, Integer>> towersByVariable =
				collectTowers(term, substitution);

		for (Map.Entry<Variable, Term> mapping : substitution)
			simplifiedTerm = simplifyHatMapping(
					simplifiedTerm, mapping, towersByVariable);

		return simplifiedTerm;
	}

	/**
	 * Simplifies a term using one hat-function mapping. The minimum tower is
	 * moved from every occurrence in the term to the closing exponent of a
	 * shallow copy stored back in the mapping.
	 *
	 * @param term the term simplified so far
	 * @param mapping a substitution mapping
	 * @param towersByVariable tower heights indexed by variable and position
	 * @return the term simplified with the mapping
	 */
	private static Term simplifyHatMapping(
			Term term,
			Map.Entry<Variable, Term> mapping,
			Map<Variable, Map<Position, Integer>> towersByVariable) {
		if (!(mapping.getValue() instanceof HatFunction hatFunction))
			return term;

		Variable variable = mapping.getKey();
		Map<Position, Integer> towersByPosition =
				towersByVariable.get(variable);
		int minimumTower = minimumValue(towersByPosition);
		if (minimumTower < 0) return term;

		HatFunction shiftedHatFunction =
				(HatFunction) hatFunction.shallowCopy();
		shiftedHatFunction.setB(
				Math.addExact(shiftedHatFunction.getB(), minimumTower));
		mapping.setValue(shiftedHatFunction);

		Term simplifiedTerm = term;
		for (Map.Entry<Position, Integer> tower :
				towersByPosition.entrySet())
			simplifiedTerm = reduceTowerAt(
					simplifiedTerm,
					tower.getKey(),
					variable,
					tower.getValue(),
					minimumTower);

		return simplifiedTerm;
	}

	/**
	 * Checks whether <code>s = c^a(t)</code> for some
	 * natural <code>a</code>.
	 * <p>
	 * If <code>c</code> is the empty context (i.e.,
	 * <code>c == contextVariable</code>) then 0 is returned.
	 * <p>
	 * The terms <code>s</code>, <code>c</code> and
	 * <code>t</code> are not modified by this method.
	 *
	 * @param term a term to be checked
	 * @param context a 1-context
	 * @param contextVariable the hole of <code>c</code>
	 * @param baseTerm a base term
	 * @return <code>a</code> if it exists, otherwise a
	 * negative integer
	 * @throws ArithmeticException if the computed exponent cannot be represented
	 * as an <code>int</code>
	 */
	public static synchronized int towerOfContexts(
			Term term,
			Term context,
			Variable contextVariable,
			Term baseTerm) {

		if (term == null || context == null ||
				contextVariable == null || baseTerm == null)
			return -1;

		// If s is equal to t or c is empty
		// then a = 0.
		if (term.deepEquals(baseTerm) || context == contextVariable) return 0;

		ContextLayerMatch layerMatch =
				matchContextLayer(term, context, contextVariable);
		if (!layerMatch.matches()) return -1;

		int innerExponent = -1;
		if (layerMatch.holeContent() != null) {
			innerExponent = towerOfContexts(
					layerMatch.holeContent(), context, contextVariable, baseTerm);
			if (innerExponent < 0) return -1;
		}

		return Math.incrementExact(innerExponent);
	}

	/**
	 * Computes the integer <code>b</code> and the term
	 * <code>t</code> such that <code>s = c^b(t)</code>
	 * with <code>t \neq c(...)</code>. Then,
	 * <code>t</code> is returned and <code>n[0]</code>
	 * is set to <code>b</code>.
	 * <p>
	 * If <code>c</code> is the empty context
	 * (i.e., it is equal to <code>contextVariable</code>)
	 * then <code>s</code> is returned and
	 * <code>n[0]</code> is set to <code>0</code>.
	 * <p>
	 * The terms <code>s</code> and <code>c</code>
	 * are not modified by this method.
	 *
	 * @param term the term of interest
	 * @param context a 1-context
	 * @param contextVariable the unique variable of <code>c</code>
	 * @param exponent an array that is used to store the
	 * computed integer <code>b</code>
	 * @return the term <code>t</code>
	 * @throws ArithmeticException if the computed exponent cannot be represented
	 * as an <code>int</code>
	 */
	public static synchronized Term towerOfContexts(
			Term term,
			Term context,
			Variable contextVariable,
			int[] exponent) {

		exponent[0] = 0;

		// If c is the empty context then
		// we return s.
		if (context == contextVariable) return term;

		ContextLayerMatch layerMatch =
				matchContextLayer(term, context, contextVariable);
		if (!layerMatch.matches()) return term;

		Term extractedTerm = null;
		if (layerMatch.holeContent() != null)
			extractedTerm = towerOfContexts(
					layerMatch.holeContent(), context, contextVariable, exponent);

		// Here, we have recognized c.
		exponent[0] = Math.incrementExact(exponent[0]);
		// We add 1 because term = c(holeContent), where
		// holeContent = c^{exponent[0]}(t).
		return extractedTerm;
	}

	/**
	 * Checks whether the root layer of a term matches a context. All context
	 * holes must contain structurally equal terms, while every fixed context
	 * argument must match the corresponding term argument.
	 *
	 * @param term the term whose root layer is checked
	 * @param context a context
	 * @param contextVariable the variable denoting every context hole
	 * @return the layer match and the common hole content, when present
	 */
	private static ContextLayerMatch matchContextLayer(
			Term term, Term context, Variable contextVariable) {
		FunctionSymbol rootSymbol = term.getRootSymbol();
		if (rootSymbol != context.getRootSymbol())
			return new ContextLayerMatch(false, null);

		Term holeContent = null;
		for (int argumentIndex = 0;
				argumentIndex < rootSymbol.getArity(); argumentIndex++) {
			Term contextChild = context.get(argumentIndex);
			Term termChild = term.get(argumentIndex);
			if (contextChild == contextVariable) {
				if (holeContent == null)
					holeContent = termChild;
				else if (!termChild.deepEquals(holeContent))
					return new ContextLayerMatch(false, null);
			}
			else if (!contextChild.deepEquals(termChild))
				return new ContextLayerMatch(false, null);
		}

		return new ContextLayerMatch(true, holeContent);
	}

	/**
	 * The result of matching one term layer against a context.
	 */
	private record ContextLayerMatch(boolean matches, Term holeContent) {}

	/**
	 * Returns the minimum value in the specified map.
	 * <p>
	 * It is supposed that each mapping <code>(p -> i)</code>
	 * in the specified map is such that <code>i</code> is a
	 * natural.
	 * <p>
	 * A negative value is returned if the provided map
	 * is empty.
	 *
	 * @param valuesByPosition a map from positions to naturals
	 * @return the minimum value in the map, or a
	 * negative integer if the map is empty
	 */
	private static synchronized int minimumValue(
			Map<Position, Integer> valuesByPosition) {
		int minimum = -1;
		for (int value : valuesByPosition.values())
			minimum = minimum < 0 ? value : Math.min(minimum, value);

		return minimum;
	}

	/**
	 * Returns the term obtained from <code>s</code> by
	 * replacing the subterm at position <code>p</code>
	 * by <code>c^{a - min}(x)</code>, where
	 * <code>c</code> is the 1-context such that
	 * <code>s|p = c^a(x)</code>.
	 * <p>
	 * The term <code>s</code> is not modified by this
	 * method.
	 *
	 * @param term the term where the replacement takes place
	 * @param position the position of the replacement
	 * @param variable the unique variable of the context <code>c</code>
	 * @param towerHeight the exponent of <code>c</code> in <code>s|p</code>
	 * @param minimumTower the minimum value of the exponents of
	 * <code>c</code> in <code>s</code>
	 * @return the term resulting from the replacement
	 */
	private static synchronized Term reduceTowerAt(
			Term term,
			Position position,
			Variable variable,
			int towerHeight,
			int minimumTower) {
		if (towerHeight == minimumTower)
			// Here, s|p = c^{min}(x), so we replace
			// s|p by x.
			return term.replace(position, variable);

		// Here, s|p = c^a(x) with a > min.
		Term tower = term.get(position);
		Term replacementChild = null;
		Term result = term;
		for (int argumentIndex = 0;
				argumentIndex < tower.getRootSymbol().getArity(); argumentIndex++) {
			Term child = tower.get(argumentIndex);
			if (!child.contains(variable)) continue;

			// Necessarily, child = c^{a-1}(x). The same computed child is
			// shared by every hole of this context layer.
			if (replacementChild == null)
				replacementChild = reduceTowerAt(
						child,
						new Position(),
						variable,
						towerHeight - 1,
						minimumTower);
			result = result.replace(
					position.addLast(argumentIndex), replacementChild);
		}

		return result;
	}

	/**
	 * If <code>theta(x) = c^{a_1,...,a_l,b}(t)</code> then,
	 * for all occurrences of <code>x</code> in <code>s</code>,
	 * computes the maximum natural <code>k</code> such that
	 * <code>c^k</code> embeds the occurrence.
	 * <p>
	 * It is supposed that the domain of <code>theta</code>
	 * is included in the set of variables of <code>s</code>.
	 * <p>
	 * The returned data structure maps each <code>x</code>
	 * such that <code>theta(x) = c^{a_1,...,a_l,b}(t)</code>
	 * to a set of mappings of the form <code>p -> k</code>
	 * where <code>p</code> is the position of an occurrence
	 * of <code>x</code> in <code>s</code> and <code>k</code>
	 * is the maximum natural as described above.
	 * <p>
	 * The term <code>s</code> and the substitution
	 * <code>theta</code> are not modified by this method.
	 *
	 * @param term the term to examine
	 * @param substitution a substitution whose domain is
	 * the set of variables of <code>s</code>
	 * @return a map as described above
	 */
	private static synchronized Map<Variable, Map<Position, Integer>>
			collectTowers(Term term, Substitution substitution) {
		Map<Variable, Map<Position, Integer>> towersByVariable = new HashMap<>();

		// We consider every mapping of the form
		// x -> c^{a_1,...,a_l,b}(t) in theta.
		for (Map.Entry<Variable, Term> mapping : substitution) {
			if (!(mapping.getValue() instanceof HatFunction hatFunction))
				continue;

			HatFunctionSymbol hatFunctionSymbol = hatFunction.getRootSymbol();
			Variable variable = mapping.getKey();
			towersByVariable.put(variable, collectTowersForVariable(
					term,
					variable,
					hatFunctionSymbol.getSimpleContext(),
					hatFunctionSymbol.getVariable()));
		}

		return towersByVariable;
	}

	/**
	 * Computes a set of mappings of the form <code>p -> k</code>
	 * where <code>p</code> is the position of an occurrence
	 * of <code>x</code> in <code>s</code> and <code>k</code>
	 * is the maximum natural such that <code>c^k</code> embeds
	 * the occurrence.
	 * <p>
	 * The terms <code>s</code> and <code>c</code> are not
	 * modified by this method.
	 *
	 * @param term the term to examine
	 * @param variable the variable to consider in <code>s</code>
	 * @param context a 1-context
	 * @param contextVariable the hole of <code>c</code>
	 * @return a set of mappings as described above
	 */
	private static synchronized Map<Position, Integer>
			collectTowersForVariable(
					Term term,
					Variable variable,
					Term context,
					Variable contextVariable) {
		Map<Position, Integer> towersByPosition = new HashMap<>();

		// We check whether s has the form c^a(x).
		int towerHeight = towerOfContexts(
				term, context, contextVariable, variable);
		if (0 <= towerHeight) {
			// Here, s = c^a(x). We add (epsilon -> a) to the map.
			towersByPosition.put(new Position(), towerHeight);
			return towersByPosition;
		}

		// Otherwise, we run this method recursively on every direct subterm.
		for (int argumentIndex = 0;
				argumentIndex < term.getRootSymbol().getArity(); argumentIndex++) {
			Map<Position, Integer> childTowers = collectTowersForVariable(
					term.get(argumentIndex), variable, context, contextVariable);
			for (Map.Entry<Position, Integer> childTower :
					childTowers.entrySet()) {
				Position position =
						childTower.getKey().addFirst(argumentIndex);
				towersByPosition.put(position, childTower.getValue());
			}
		}

		return towersByPosition;
	}
}
