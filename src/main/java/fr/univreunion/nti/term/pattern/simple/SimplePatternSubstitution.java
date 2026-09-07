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

package fr.univreunion.nti.term.pattern.simple;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.PatternUtils;

/**
 * A simple pattern substitution, i.e., a function
 * from variables to terms containing no hat symbol
 * or a hat symbol only at the root position.
 * <p>
 * Such a substitution is stored in two equivalent forms.
 * The inherited pattern-substitution representation is a
 * list <code>[sigma_1,...,sigma_l,mu]</code> of pumping
 * substitutions <code>sigma_i</code> and a closing substitution
 * <code>mu</code>. The field <code>hatFunctionSubstitution</code>
 * stores the corresponding substitution <code>theta</code>,
 * which maps variables to terms with hat symbols. These two
 * representations are connected by the transformations
 * <code>upsilon</code> and <code>upsilon^-1</code> used in
 * the mathematical definitions.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class SimplePatternSubstitution extends PatternSubstitution {

	/**
	 * The mappings of this simple pattern substitution.
	 */
	private final Substitution hatFunctionSubstitution;

	/**
	 * Builds an empty simple pattern substitution.
	 */
	private SimplePatternSubstitution() {
		super();
		this.hatFunctionSubstitution = new Substitution();
	}

	/**
	 * Builds a simple pattern substitution from
	 * the provided list of pumping and closing
	 * substitutions, which are supposed to have
	 * the correct form (i.e., mappings of the
	 * form x -> c^a(x) for the pumping substitutions).
	 * <p>
	 * The length of the provided list must be at
	 * least 2 (i.e., the list must contain at least
	 * a pumping substitution and a closing substitution).
	 *
	 * @param pumpingAndClosingSubstitutions the pumping and closing
	 * substitutions of this simple pattern substitution
	 * @param hatFunctionSubstitution the mappings of this simple pattern
	 * substitution
	 * @throws IllegalArgumentException if the provided
	 * list is <code>null</code> or is too short
	 */
	private SimplePatternSubstitution(
			List<Substitution> pumpingAndClosingSubstitutions,
			Substitution hatFunctionSubstitution) {

		super(pumpingAndClosingSubstitutions);
		this.hatFunctionSubstitution = hatFunctionSubstitution;
	}

	/**
	 * Builds an empty simple pattern substitution.
	 *
	 * @return an empty simple pattern substitution
	 */
	public static SimplePatternSubstitution empty() {
		return new SimplePatternSubstitution();
	}

	/**
	 * Tries to build a simple pattern substitution
	 * from the specified substitution <code>theta</code>,
	 * which is the representation with hat symbols.
	 * <p>
	 * This method attempts to compute the image of
	 * <code>theta</code> by <code>upsilon^-1</code>,
	 * i.e., to recover the corresponding list of pumping
	 * and closing substitutions.
	 *
	 * @param theta the substitution to convert
	 * @return a simple pattern substitution,
	 * or <code>null</code> if no pattern
	 * substitution could be reconstructed from
	 * <code>theta</code> by <code>upsilon^-1</code>
	 */
	public static SimplePatternSubstitution tryBuild(Substitution theta) {
		return tryBuild(theta, false);
	}

	/**
	 * Tries to build a simple pattern substitution by taking ownership of the
	 * provided hat-function substitution upon success.
	 * <p>
	 * This entry point is reserved for freshly computed substitutions which are
	 * not accessed again by their caller. When this method succeeds, the returned
	 * pattern substitution directly retains {@code theta}; the caller must
	 * therefore relinquish all subsequent access to it.
	 *
	 * @param theta the substitution whose ownership may be transferred
	 * @return a simple pattern substitution, or {@code null} upon failure
	 */
	public static SimplePatternSubstitution tryBuildTakingOwnership(
			Substitution theta) {
		return tryBuild(theta, true);
	}

	/** Builds from a hat-function representation with optional ownership. */
	private static SimplePatternSubstitution tryBuild(
			Substitution theta, boolean takeOwnership) {
		List<Substitution> pumpingAndClosingSubstitutions =
				tryRecoverPumpingAndClosingSubstitutions(theta);
		if (pumpingAndClosingSubstitutions == null || pumpingAndClosingSubstitutions.size() < 2)
			return null;

		return new SimplePatternSubstitution(
				pumpingAndClosingSubstitutions,
				takeOwnership ? theta : new Substitution(theta));
	}

	/**
	 * Tries to build a simple pattern substitution
	 * from the specified list of pumping and
	 * closing substitutions
	 * <code>[sigma_1,...,sigma_l,mu]</code>.
	 * <p>
	 * This method attempts to compute the image of
	 * <code>[sigma_1,...,sigma_l,mu]</code> by
	 * <code>upsilon</code>, i.e., to build the
	 * corresponding substitution <code>theta</code>
	 * with hat symbols.
	 *
	 * @param pumpingAndClosingSubstitutions the substitutions to convert
	 * @return a simple pattern substitution,
	 * or <code>null</code> if no pattern
	 * substitution could be constructed from
	 * <code>pumpingAndClosingSubstitutions</code>
	 * by <code>upsilon</code>
	 */
	public static SimplePatternSubstitution tryBuild(
			List<Substitution> pumpingAndClosingSubstitutions) {
		Substitution hatFunctionSubstitution = tryBuildHatFunctionSubstitution(
				pumpingAndClosingSubstitutions);

		if (hatFunctionSubstitution == null)
			return null;

		return new SimplePatternSubstitution(
				pumpingAndClosingSubstitutions, hatFunctionSubstitution);
	}

	/**
	 * Attempts to build the hat-function representation
	 * corresponding to the provided list of pumping and
	 * closing substitutions.
	 *
	 * @param pumpingAndClosingSubstitutions the substitutions
	 * to convert
	 * @return the corresponding hat-function substitution, or
	 * <code>null</code> in case of failure
	 */
	private static Substitution tryBuildHatFunctionSubstitution(
			List<Substitution> pumpingAndClosingSubstitutions) {

		Substitution hatFunctionSubstitution = new Substitution();
		for (Variable variable : domainOf(pumpingAndClosingSubstitutions)) {
			Term patternImage = tryBuildHatFunctionImage(
					variable,
					imagesOf(variable, pumpingAndClosingSubstitutions));
			if (patternImage == null)
				return null;
			hatFunctionSubstitution.add(variable, patternImage);
		}

		return hatFunctionSubstitution;
	}

	/**
	 * Returns the union of the domains of the provided substitutions.
	 *
	 * @param substitutions some substitutions
	 * @return the union of their domains
	 */
	private static Set<Variable> domainOf(List<Substitution> substitutions) {
		Set<Variable> domain = new HashSet<>();
		for (Substitution substitution : substitutions)
			domain.addAll(substitution.getDomain());

		return domain;
	}

	/**
	 * Returns the images of the specified variable in the provided
	 * substitutions, using the variable itself when it is not in a
	 * substitution domain.
	 *
	 * @param variable a variable
	 * @param substitutions some substitutions
	 * @return the variable images in substitution order
	 */
	private static List<Term> imagesOf(
			Variable variable, List<Substitution> substitutions) {
		List<Term> images = new ArrayList<>();
		for (Substitution substitution : substitutions)
			images.add(substitution.getOrDefault(variable, variable));

		return images;
	}

	/**
	 * Computes the composition of this pattern substitution
	 * with the provided one.
	 * <p>
	 * Neither this pattern substitution nor the provided
	 * one are modified by this method.
	 *
	 * @param otherPatternSubstitution the pattern substitution to compose with
	 * this one
	 * @return the result of the composition, or
	 * <code>null</code> in case of failure
	 */
	@Override
	public SimplePatternSubstitution composeWith(PatternSubstitution otherPatternSubstitution) {

		if (otherPatternSubstitution instanceof SimplePatternSubstitution otherSimplePatternSubstitution)
			return tryBuildTakingOwnership(
					this.hatFunctionSubstitution.composeWith(
					otherSimplePatternSubstitution.hatFunctionSubstitution));

		return null;
	}

	/**
	 * Returns a deep copy of this pattern substitution
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @return a deep copy of this pattern substitution
	 */
	@Override
	public SimplePatternSubstitution deepCopy() {
		return this.deepCopy(new HashMap<>());
	}

	/**
	 * Returns a deep copy of this pattern substitution
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * <p>
	 * The specified map is used to store subterm
	 * copies and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened", i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 *
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this pattern substitution
	 */
	@Override
	public SimplePatternSubstitution deepCopy(Map<Term, Term> copies) {
		return tryBuildTakingOwnership(
				this.hatFunctionSubstitution.deepCopy(copies));
	}

	/**
	 * Returns the mappings of this simple
	 * pattern substitution. This substitution
	 * is denoted by theta in the corresponding
	 * mathematical definitions.
	 *
	 * @return the mappings of this simple
	 * pattern substitution
	 */
	public Substitution getHatFunctionSubstitution() {
		return this.hatFunctionSubstitution;
	}

	/**
	 * Returns a string representation of this
	 * simple pattern substitution relatively
	 * to the given set of variable symbols.
	 *
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	@Override
	public String toString(Map<Variable, String> variables) {
		return this.hatFunctionSubstitution.toString(variables);
	}

	/**
	 * Returns a string representation of this
	 * simple pattern substitution.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}

	/**
	 * Attempts to compute the image of the provided
	 * substitution by upsilon^-1, i.e., a list of
	 * pumping and closing substitutions corresponding
	 * to the provided substitution.
	 *
	 * @param theta a substitution
	 * @return a list of pumping and closing substitutions,
	 * or <code>null</code> in case of failure
	 */
	private static List<Substitution> tryRecoverPumpingAndClosingSubstitutions(Substitution theta) {
		// The list of substitutions to return at the end.
		LinkedList<Substitution> pumpingAndClosingSubstitutions = new LinkedList<>();
		// There is always one closing substitution. Pumping substitutions are
		// prepended on demand when hat images expose a larger arity.
		pumpingAndClosingSubstitutions.add(new Substitution());

		for (Map.Entry<Variable, Term> entry : theta) {
			Term image = entry.getValue();
			if (image instanceof HatFunction hatFunction)
				ensureHatArity(
						pumpingAndClosingSubstitutions,
						hatFunction.getArity());
			if (!tryFillPumpingAndClosingSubstitutionsFromEntry(
					pumpingAndClosingSubstitutions, entry))
				return null;
		}

		ensurePumpingSubstitutionExists(pumpingAndClosingSubstitutions);

		return pumpingAndClosingSubstitutions;
	}

	/** Ensures that the recovered list can represent the specified hat arity. */
	private static void ensureHatArity(
			LinkedList<Substitution> pumpingAndClosingSubstitutions,
			int hatArity) {

		while (pumpingAndClosingSubstitutions.size() <= hatArity)
			pumpingAndClosingSubstitutions.addFirst(new Substitution());
	}

	/**
	 * Attempts to fill the pumping and closing substitutions from one
	 * mapping of the hat-function representation.
	 *
	 * @param pumpingAndClosingSubstitutions the pumping and closing
	 * substitutions to fill
	 * @param entry one mapping of a substitution with hat symbols
	 * @return <code>true</code> iff the substitutions could be filled
	 */
	private static boolean tryFillPumpingAndClosingSubstitutionsFromEntry(
			LinkedList<Substitution> pumpingAndClosingSubstitutions,
			Map.Entry<Variable, Term> entry) {

		Variable variable = entry.getKey();
		Term image = entry.getValue();

		if (image instanceof HatFunction hatFunction)
			return tryFillPumpingAndClosingSubstitutionsFromHatFunctionImage(
					pumpingAndClosingSubstitutions, variable, hatFunction);

		return tryFillClosingSubstitutionFromPlainImage(
				pumpingAndClosingSubstitutions, variable, image);
	}

	/**
	 * Ensures that the list contains at least one pumping substitution
	 * and one closing substitution.
	 *
	 * @param pumpingAndClosingSubstitutions the substitution list to update
	 */
	private static void ensurePumpingSubstitutionExists(
			LinkedList<Substitution> pumpingAndClosingSubstitutions) {

		if (pumpingAndClosingSubstitutions.size() < 2)
			// Here there is only a closing substitution because
			// we did not encounter hat functions. Then, we also
			// add an empty pumping substitution.
			pumpingAndClosingSubstitutions.addFirst(new Substitution());
	}

	/**
	 * Attempts to fill the pumping and closing substitutions from
	 * an image of the form
	 * <code>theta(x) = c^{a_1,...,a_l,b}(v)</code>.
	 *
	 * @param pumpingAndClosingSubstitutions the pumping and closing
	 * substitutions to fill
	 * @param variable the variable whose image is used
	 * @param hatFunction the image of <code>variable</code>
	 * @return <code>true</code> iff the substitutions
	 * could be filled
	 */
	private static boolean tryFillPumpingAndClosingSubstitutionsFromHatFunctionImage(
			LinkedList<Substitution> pumpingAndClosingSubstitutions,
			Variable variable,
			HatFunction hatFunction) {

		HatFunctionSymbol hatSymbol = hatFunction.getRootSymbol();
		Term context = hatSymbol.getSimpleContext();
		Variable contextHole = hatSymbol.getVariable();
		Term baseArgument = hatFunction.getArgument();

		// We check whether argument contains inner
		// subterms that are hat functions.
		if (baseArgument.containsHatSubterm())
			return false;

		Iterator<Integer> exponents = hatFunction.exponentsDescendingIterator();
		Iterator<Substitution> substitutionIterator =
				pumpingAndClosingSubstitutions.descendingIterator();

		// We add the closing image of variable to
		// the closing substitution.
		substitutionIterator.next().add(
				variable, PatternUtils.embed(
						context, contextHole, exponents.next(), baseArgument));

		// For each i, we add the pumping image of variable
		// to the pumping substitution sigma_i.
		while (exponents.hasNext())
			substitutionIterator.next().add(
					variable, PatternUtils.embed(
							context, contextHole, exponents.next(), variable));

		return true;
	}

	/**
	 * Attempts to fill the closing substitution from an
	 * image that is not a hat function.
	 *
	 * @param pumpingAndClosingSubstitutions the pumping and closing
	 * substitutions to fill
	 * @param variable the variable whose image is used
	 * @param image the image of <code>variable</code>
	 * @return <code>true</code> iff the closing
	 * substitution could be filled
	 */
	private static boolean tryFillClosingSubstitutionFromPlainImage(
			LinkedList<Substitution> pumpingAndClosingSubstitutions,
			Variable variable,
			Term image) {

		// We add the image of variable to the closing
		// substitution, but only if image
		// does not contain inner subterms that are
		// hat functions.
		if (image.containsHatSubterm())
			return false;
		pumpingAndClosingSubstitutions.getLast().add(variable, image);

		return true;
	}

	/**
	 * Attempts to build the image <code>theta(x)</code>
	 * obtained by applying <code>upsilon</code> to the
	 * images of <code>x</code> in the pumping and closing
	 * substitutions.
	 * <p>
	 * The provided list has the form
	 * <code>[sigma_1(x),...,sigma_l(x),mu(x)]</code>
	 * for pumping substitutions <code>sigma_i</code>
	 * and a closing substitution <code>mu</code>.
	 * If for all <code>1 <= i <= l</code> we have
	 * <code>sigma_i(x) == x</code> then this method
	 * returns <code>mu(x)</code>.
	 * Else, it computes the smallest ground 1-context
	 * <code>c</code> such that
	 * <code>sigma_i(x) = c^{a_i}(x)</code>
	 * and <code>mu(x) = c^b(t)</code> for some naturals
	 * <code>a_i</code> and <code>b</code> and some term
	 * <code>t</code>. Then, it returns the term
	 * <code>c^{a_1,...,a_l,b}(t)</code>, or
	 * <code>null</code> if no such <code>c</code> could
	 * be computed.
	 * <p>
	 * It is supposed that
	 * <code>sigma_1(x),...,sigma_l(x)</code> are terms
	 * whose only variable is <code>x</code>.
	 *
	 * @param variable the unique variable of
	 * <code>sigma_1(x),...,sigma_l(x)</code>
	 * @param images the list
	 * <code>[sigma_1(x),...,sigma_l(x),mu(x)]</code>
	 * @return the image <code>theta(x)</code>, or
	 * <code>null</code> if it could not be constructed
	 */
	private static Term tryBuildHatFunctionImage(Variable variable, List<Term> images) {

		HatFunctionImageComponents components =
				tryComputeHatFunctionImageComponents(variable, images);

		if (components == null)
			return null;
		if (components.simpleContext() == null)
			return components.closingBaseTerm();

		HatFunctionSymbol hatContextSymbol = HatFunctionSymbol.intern(
				components.simpleContext(), variable);
		return new HatFunction(
				hatContextSymbol,
				components.closingBaseTerm(),
				components.exponents());
	}

	/**
	 * The components used to build a hat-function image
	 * <code>theta(x) = c^{a_1,...,a_l,b}(t)</code>.
	 *
	 * @param simpleContext the ground 1-context <code>c</code>
	 * @param closingBaseTerm the term <code>t</code>
	 * @param exponents the exponents <code>a_1,...,a_l,b</code>
	 */
	private record HatFunctionImageComponents(
			Term simpleContext,
			Term closingBaseTerm,
			List<Integer> exponents) {}

	/**
	 * Attempts to compute the components of the image
	 * <code>theta(x) = c^{a_1,...,a_l,b}(t)</code>
	 * from the list
	 * <code>[sigma_1(x),...,sigma_l(x),mu(x)]</code>.
	 *
	 * @param variable the unique variable of
	 * <code>sigma_1(x),...,sigma_l(x)</code>
	 * @param images the list
	 * <code>[sigma_1(x),...,sigma_l(x),mu(x)]</code>
	 * @return the components of the image <code>theta(x)</code>, or
	 * <code>null</code> if they could not be computed
	 */
	private static HatFunctionImageComponents tryComputeHatFunctionImageComponents(
			Variable variable,
			List<Term> images) {

		List<Integer> exponents = new ArrayList<>();
		Term simpleContext = null;
		int[] computedExponent = new int[1];

		int closingImageIndex = images.size() - 1;
		for (int index = 0; index < closingImageIndex; index++) {
			PumpingImageComponents pumpingImageComponents = tryComputePumpingImageComponents(
					variable,
					images.get(index),
					computedExponent);
			if (pumpingImageComponents == null)
				return null;

			exponents.add(pumpingImageComponents.exponent());
			Term candidateContext = pumpingImageComponents.simpleContext();
			if (candidateContext == null)
				continue;
			if (simpleContext != null &&
					!candidateContext.deepEquals(simpleContext))
				return null;
			simpleContext = candidateContext;
		}

		// Here, the last image of variable comes from the
		// closing substitution mu.
		Term closingImage = images.get(closingImageIndex);

		// If simpleContext == null then variable is in the
		// domain of no pumping substitution. In this
		// case, we return mu(x).
		if (simpleContext == null)
			return new HatFunctionImageComponents(null, closingImage, exponents);

		// Here, simpleContext != null, i.e., variable is in
		// the domain of at least one pumping substitution.
		// We compute b and t such that mu(x) = c^b(t).
		// The exponent b is stored in computedExponent[0].
		Term closingBaseTerm = PatternUtils.towerOfContexts(
				closingImage, simpleContext, variable, computedExponent);
		exponents.add(computedExponent[0]);

		return new HatFunctionImageComponents(simpleContext, closingBaseTerm, exponents);
	}

	/**
	 * The components read from one pumping image
	 * <code>sigma_i(x) = c^{a_i}(x)</code>.
	 *
	 * @param simpleContext the context <code>c</code>, or <code>null</code>
	 * when the exponent is zero
	 * @param exponent the exponent <code>a_i</code>
	 */
	private record PumpingImageComponents(Term simpleContext, int exponent) {}

	/**
	 * Attempts to compute the context and exponent represented by one
	 * pumping image.
	 *
	 * @param variable the unique variable of the pumping image
	 * @param image the image to analyze
	 * @param computedExponent output array used by <code>PatternUtils</code>
	 * @return the pumping-image components, or <code>null</code> in case
	 * of failure
	 */
	private static PumpingImageComponents tryComputePumpingImageComponents(
			Variable variable,
			Term image,
			int[] computedExponent) {

		if (image == variable)
			return new PumpingImageComponents(null, 0);

		if (!(image instanceof Function))
			return null;

		// We compute c and a such that image = c^a(variable).
		// The exponent a is stored in computedExponent[0].
		Term simpleContext = PatternUtils.getContext(image, variable, computedExponent);
		if (simpleContext == null)
			return null;

		return new PumpingImageComponents(simpleContext, computedExponent[0]);
	}
}
