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

package fr.univreunion.nti.term;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

import fr.univreunion.nti.program.lp.Mode;
import fr.univreunion.nti.program.lp.SoP;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.argfiltering.Filter;
import fr.univreunion.nti.program.trs.polynomial.ArithOperator;
import fr.univreunion.nti.program.trs.polynomial.Polynomial;
import fr.univreunion.nti.program.trs.polynomial.PolynomialComp;
import fr.univreunion.nti.program.trs.polynomial.PolynomialConst;
import fr.univreunion.nti.program.trs.reducpair.LexOrder;
import fr.univreunion.nti.program.trs.reducpair.PolyInterpretation;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.leftunif.LuEquation;

/**
 * A term of the form f(...).
 * <p>
 * An object of this class is mutable.
 *
 * <p>The homeomorphic-embedding operations follow T. Arts and J. Giesl,
 * <a href="https://doi.org/10.1016/S0304-3975(99)00207-8">Termination of
 * Term Rewriting Using Dependency Pairs</a>, Theoretical Computer Science
 * 236(1--2), 133--178, 2000. The path-order operations follow F. Baader and
 * T. Nipkow, <a href="https://doi.org/10.1017/CBO9781139172752">Term
 * Rewriting and All That</a>, Cambridge University Press, 1998.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Function extends Term {

	/**
	 * The index of the first argument in this function's argument array.
	 */
	private static final int FIRST_ARGUMENT_INDEX = 0;

	/**
	 * The arity of unary function symbols.
	 */
	private static final int UNARY_ARITY = 1;

	/**
	 * The index of the constant coefficient in a polynomial interpretation.
	 */
	private static final int CONSTANT_COEFFICIENT_INDEX = 0;

	/**
	 * The symbol at root position (string representation).
	 */
	private final FunctionSymbol rootSymbol;

	/**
	 * The arguments of the root symbol.
	 */
	private final Term[] arguments;

	/**
	 * Builds a function.
	 *
	 * @param rootSymbol the symbol at root position
	 * @param arguments the arguments (direct sons) of the root symbol
	 * @throws IllegalArgumentException if the arity of the given root
	 * symbol is different from the size of the given argument list or
	 * if the given argument list contains <code>null</code>
	 */
	public Function(FunctionSymbol rootSymbol, List<? extends Term> arguments) {
		if (rootSymbol.getArity() != arguments.size())
			throw new IllegalArgumentException("size mismatch");

		this.rootSymbol = rootSymbol;
		this.arguments = new Term[rootSymbol.getArity()];
		int argumentIndex = 0;
		for (Term argument : arguments) {
			if (argument == null)
				throw new IllegalArgumentException(
						"construction of a term with a null subterm");
			this.arguments[argumentIndex++] = argument;
		}
	}

	/**
	 * Builds a function whose root symbol is the specified one.
	 *
	 * @param rootSymbol the root symbol of the function to build
	 */
	private Function(FunctionSymbol rootSymbol) {
		this.rootSymbol = rootSymbol;
		this.arguments = new Term[rootSymbol.getArity()];
	}

	/**
	 * Returns the root symbol of this function.
	 *
	 * @return the root symbol of this function
	 */
	@Override
	public FunctionSymbol getRootSymbol() {
		return this.rootSymbol;
	}

	/**
	 * Returns the child at the specified index in this function.
	 *
	 * @param childIndex the index of the child to be returned
	 * @return the child at the specified index, or <code>null</code> if
	 * <code>childIndex</code> is not a valid child index in this function
	 */
	public Term getChild(int childIndex) {
		// Check whether childIndex is out of bounds.
		if (this.isChildIndexOutOfBounds(childIndex))
			return null;

		return this.arguments[childIndex];
	}

	/**
	 * Checks whether the specified index is outside this function's direct
	 * children.
	 *
	 * @param childIndex the index to validate
	 * @return <code>true</code> iff the specified index does not denote a
	 * direct child of this function
	 */
	private boolean isChildIndexOutOfBounds(int childIndex) {
		return childIndex < 0 || this.arguments.length <= childIndex;
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether this term has the same structure as the specified
	 * term <code>t</code>. This term and <code>t</code> are
	 * not modified by this method.
	 * <p>
	 * This method implements a rough, but quickly computable,
	 * over-approximation of both the subsumption and the
	 * unification tests. It is essentially used for computing
	 * families (see method <code>getFamily</code> in class
	 * <code>FD_Graph</code>).
	 * <p>
	 * Both this term and the specified term are supposed to be
	 * the schemas of their respective class representatives.
	 * Moreover, it is supposed that <code>this != t</code>
	 * and that <code>t != null</code>.
	 *
	 * @param t the term whose structure has to be compared
	 * to that of this term
	 * @return <code>true</code> if this term has the same
	 * structure as that of the given term and <code>false</code>
	 * otherwise
	 */
	@Override
	protected boolean hasSameStructureAsAux(Term t) {
		if (t instanceof Variable)
			return true;

		if (!(t instanceof Function other) ||
				this.rootSymbol != other.rootSymbol)
			return false;

		for (int argumentIndex = 0;
				argumentIndex < this.arguments.length;
				argumentIndex++) {

			Term sourceArgument = this.arguments[argumentIndex];
			if (!sourceArgument.hasSameStructureAs(other.arguments[argumentIndex]))
				return false;
		}

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether some other term is equal to
	 * this one.
	 * <p>
	 * This a deep, structural, comparison.
	 * <p>
	 * Both this term and the provided term are
	 * supposed to be the representatives of their
	 * respective class. Moreover, it is supposed
	 * that <code>this != t</code>.
	 *
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term is the
	 * same as the term argument
	 */
	@Override
	protected boolean deepEqualsAux(Term t) {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return true;

		if (!(t instanceof Function targetFunction) || this.rootSymbol != targetFunction.rootSymbol)
			return false;

		return this.hasDeepEqualArguments(targetFunction);
	}

	/**
	 * Checks whether this function has already been visited during the current
	 * traversal, marking it as visited otherwise.
	 *
	 * @return <code>true</code> iff this function had already been visited
	 * during the current traversal
	 */
	private boolean hasAlreadyBeenVisitedInCurrentTraversal() {
		long time = Term.getCurrentTime();
		if (this.mark >= time)
			return true;

		this.mark = time;
		return false;
	}

	/**
	 * Checks whether this function's arguments are deeply equal to the
	 * corresponding arguments of the specified function.
	 *
	 * @param targetFunction the function whose arguments are compared
	 * with this function's arguments
	 * @return <code>true</code> iff every pair of corresponding arguments
	 * is deeply equal
	 */
	private boolean hasDeepEqualArguments(Function targetFunction) {
		for (int argumentIndex = 0;
				argumentIndex < this.arguments.length;
				argumentIndex++) {

			Term sourceArgument = this.arguments[argumentIndex];
			if (!sourceArgument.deepEqualsAux1(
					targetFunction.arguments[argumentIndex]))
				return false;
		}

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return a shallow copy of this term
	 */
	@Override
	protected Term shallowCopyAux() {
		return this.copyWithMappedArguments(Term::shallowCopy);
	}

	/**
	 * Builds a copy of this function with each argument replaced by the term
	 * returned by the specified mapper.
	 *
	 * @param mapper the argument mapper, applied from left to right
	 * @return the resulting function
	 */
	private Function copyWithMappedArguments(UnaryOperator<Term> mapper) {
		Function result = new Function(this.rootSymbol);

		int argumentIndex = 0;
		for (Term argument : this.arguments)
			result.arguments[argumentIndex++] = mapper.apply(argument);

		return result;
	}

	/**
	 * An auxiliary, internal, method which returns a
	 * deep copy of this term i.e., a copy where each
	 * subterm is also copied, except the variables
	 * not occurring in the specified collection.
	 * <p>
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied.
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param varsToBeCopied a collection of variables
	 * that must be copied
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return a deep copy of this term
	 */
	@Override
	protected Term deepCopyAux(
			Collection<Variable> varsToBeCopied,
			Map<Term, Term> copies) {

		return this.copyWithMappedArguments(
				argument -> argument.deepCopy(varsToBeCopied, copies));
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains the given
	 * term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative. Moreover, it is supposed
	 * that <code>this != t</code>.
	 *
	 * @param t a term whose presence in this term
	 * is to be tested
	 * @return <code>true</code> iff this term
	 * contains <code>t</code>
	 */
	@Override
	protected boolean containsAux(Term t) {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		for (Term argument : this.arguments)
			if (argument.containsAux1(t))
				return true;

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0.
	 * <p>
	 * Used in the implementation of step 3 of
	 * Alg. A-2.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	@Override
	protected boolean containsRhoAux() {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		for (Term argument : this.arguments)
			if (argument.findSchema().containsRhoAux())
				return true;

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * check whether this term is ground i.e., contains
	 * no variable.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return <code>true</code> iff this term contains
	 * no variable
	 */
	@Override
	protected boolean isGroundAux() {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return true;

		for (Term argument : this.arguments)
			if (!argument.findSchema().isGroundAux())
				return false;

		return true;
	}

	/**
	 * Returns the function resulting from replacing,
	 * in this function, the arguments at the positions
	 * given by <code>mode</code> with ground terms built
	 * from <code>tau</code>.
	 * <p>
	 * This function is not modified by this method.
	 * <p>
	 * The specified mode <code>mode</code> is supposed to
	 * be compatible with this function and with the
	 * specified set of positions <code>tau</code>. I.e.,
	 * if <code>p</code> denotes the root symbol of this
	 * function, then <code>p</code> is also the predicate
	 * symbol of <code>mode</code>. Moreover, the argument
	 * positions given by <code>mode</code> are included
	 * in the domain of <code>tau(p)</code>.
	 * <p>
	 * The returned function is built as follows.
	 * For each mapping <code>i -> t</code> in
	 * <code>tau(p)</code>, if <code>i</code> is
	 * in <code>mode</code> then the <code>i</code>-th argument
	 * of this function is replaced with a ground instance
	 * of <code>t</code> (variables are replaced with the
	 * constant symbol <code>a</code>). The other arguments
	 * are deep copies of the corresponding arguments in
	 * this function.
	 *
	 * @param mode a mode, compatible with <code>tau</code>
	 * @param tau a set of positions
	 * @return the function resulting from grounding
	 * this function at some specific positions
	 */
	public Function ground(Mode mode, SoP tau) {
		// The function that will be returned.
		Function result = new Function(this.rootSymbol);

		// The constant symbol that we use for grounding.
		Function groundingTerm =
				new Function(FunctionSymbol.intern("a", 0), List.of());

		// A data structure used for copying the arguments
		// that are not distinguished by tau.
		Map<Term, Term> copies = new HashMap<>();

		for (int argumentIndex = 0; argumentIndex < this.arguments.length; argumentIndex++) {
			result.arguments[argumentIndex] = this.groundOrCopyArgument(
					argumentIndex,
					mode,
					tau,
					groundingTerm,
					copies);
		}

		return result;
	}

	/**
	 * Grounds the argument at the specified index when it is selected by the
	 * provided mode and set of positions, or returns a deep copy otherwise.
	 *
	 * @param argumentIndex the index of the argument to ground or copy
	 * @param mode a mode, compatible with <code>tau</code>
	 * @param tau a set of positions
	 * @param groundingTerm the ground term used for replacing variables
	 * @param copies a set of subterm copies
	 * @return the grounded argument or a deep copy of the original argument
	 */
	private Term groundOrCopyArgument(
			int argumentIndex,
			Mode mode,
			SoP tau,
			Term groundingTerm,
			Map<Term, Term> copies) {

		Term mappedTerm = mode.contains(argumentIndex) ?
				tau.getMappedTerm(this.rootSymbol, argumentIndex) :
				null;
		Term sourceArgument = this.arguments[argumentIndex];

		return mappedTerm != null ?
				mappedTerm.replaceVariables(groundingTerm) :
				sourceArgument.deepCopy(copies);
	}

	/**
	 * Adds the variables of this term to the provided set.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param variables the variable set to complete
	 */
	@Override
	protected void addVariablesTo(Set<Variable> variables) {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return;

		for (Term argument : this.arguments)
			argument.findSchema().addVariablesTo(variables);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to compute the number of occurrences of each
	 * variable of this term.
	 * <p>
	 * The provided mapping is filled accordingly.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param occurrences a mapping which associates
	 * variables with their number of occurrences in
	 * this term
	 */
	@Override
	protected void getVariableOccurrencesAux(Map<Variable, Integer> occurrences) {
		for (Term argument : this.arguments)
			argument.getVariableOccurrences(occurrences);
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of function symbols of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return the set of function symbols of this term
	 */
	@Override
	protected Set<FunctionSymbol> getFunSymbolsAux() {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return new HashSet<>();

		HashSet<FunctionSymbol> symbols = new HashSet<>();
		symbols.add(this.getRootSymbol());
		for (Term argument : this.arguments)
			symbols.addAll(argument.findSchema().getFunSymbolsAux());
		return symbols;
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the subterm of this term at the given single
	 * position.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param childIndex a single position
	 * @return the subterm of this term at position
	 * <code>i</code>, or <code>null</code> if
	 * <code>i</code> is not a valid position in
	 * this term
	 */
	@Override
	protected Term getAux(int childIndex) {
		return this.getChild(childIndex);
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * return the subterm of this term at the position
	 * specified by the provided iterator.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * <p>
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 * Moreover, this term is supposed to be the schema of
	 * its class representative.
	 * <p>
	 * It is also supposed that <code>it</code> has a
	 * next element.
	 *
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at the given position
	 * or <code>null</code> if the provided iterator does not
	 * correspond to a valid position in this term
	 */
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		// 'it' is supposed to have a next element, hence we can
		// safely write this.
		Integer childIndex = it.next();

		// Check whether childIndex is out of bounds.
		if (this.isChildIndexOutOfBounds(childIndex))
			return null;

		return this.arguments[childIndex].get(it, shallow);
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the hat subterms of this
	 * term.
	 * <p>
	 * There are no duplicate in the returned collection,
	 * i.e., if s and t are in the returned collection
	 * then they are not equal (w.r.t. a deep, structural,
	 * comparison).
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return a collection consisting of the hat subterms
	 * of this term
	 */
	@Override
	protected Collection<Term> getHatSubtermsAux() {
		Collection<Term> result = new ArrayList<>();

		for (Term argument : this.arguments) {
			Collection<Term> argumentHatSubterms =
					argument.findSchema().getHatSubtermsAux();
			for (Term candidate : argumentHatSubterms)
				addIfDeeplyDistinct(result, candidate);
		}

		if (result.isEmpty() && this.rootSymbol.isHatSymbol())
			result.add(this);

		return result;
	}

	/** {@inheritDoc} */
	@Override
	protected boolean containsHatSubtermAux() {
		if (this.rootSymbol.isHatSymbol())
			return true;
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return false;

		for (Term argument : this.arguments)
			if (argument.findSchema().containsHatSubtermAux())
				return true;

		return false;
	}

	/**
	 * Adds the specified term to the provided collection if no already
	 * collected term is deeply equal to it.
	 *
	 * @param terms the collection to update
	 * @param candidate the term to add if it is deeply distinct
	 */
	private static void addIfDeeplyDistinct(
			Collection<Term> terms,
			Term candidate) {

		if (!containsDeepEqualTerm(terms, candidate))
			terms.add(candidate);
	}

	/**
	 * Checks whether the provided collection contains a term deeply equal to
	 * the specified candidate.
	 *
	 * @param terms the collection to inspect
	 * @param candidate the reference term
	 * @return <code>true</code> iff some collected term is deeply equal to
	 * <code>candidate</code>
	 */
	private static boolean containsDeepEqualTerm(
			Collection<Term> terms,
			Term candidate) {

		for (Term term : terms)
			if (candidate.deepEquals(term))
				return true;

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the disagreement positions
	 * of this term and the specified term.
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * <p>
	 * Moreover, it is supposed that <code>this != t</code>.
	 * <p>
	 * If the specified term is <code>null</code> then a
	 * collection consisting of the empty position (epsilon)
	 * is returned.
	 *
	 * @param t a term
	 * @param allowVariablePairs <code>true</code> iff disagreement pairs of the
	 * form {@code <variable, variable>} are allowed
	 * @return a collection consisting of the disagreement positions
	 * of this term and the given term
	 */
	@Override
	protected Collection<Position> dposAux(Term t, boolean allowVariablePairs) {
		// The collection to return at the end.
		Collection<Position> positions = new ArrayList<>();

		if (!(t instanceof Function targetFunction) ||
				this.rootSymbol != targetFunction.rootSymbol) {

			positions.add(new Position());
			return positions;
		}

		this.addArgumentDisagreementPositions(
				positions, targetFunction, allowVariablePairs);

		return positions;
	}

	/**
	 * Adds the disagreement positions found in the arguments of this function.
	 *
	 * @param positions the collection to complete
	 * @param targetFunction the function to compare with this function
	 * @param allowVariablePairs <code>true</code> iff disagreement pairs of the
	 * form {@code <variable, variable>} are allowed
	 */
	private void addArgumentDisagreementPositions(
			Collection<Position> positions,
			Function targetFunction,
			boolean allowVariablePairs) {

		for (int argumentIndex = 0;
				argumentIndex < this.arguments.length;
				argumentIndex++) {

			Term sourceArgument = this.arguments[argumentIndex];
			for (Position disagreementPosition :
					sourceArgument.dpos(
							targetFunction.arguments[argumentIndex], allowVariablePairs))
				positions.add(disagreementPosition.addFirst(argumentIndex));
		}
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, the subterm at the position specified by
	 * <code>it</code> with <code>t</code>.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * <p>
	 * Both this term and <code>t</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * <p>
	 * Moreover, it is supposed that <code>it</code> has a
	 * next element.
	 *
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 * @throws IndexOutOfBoundsException when the provided
	 * iterator does not correspond to a valid position in
	 * this term
	 */
	@Override
	protected Term replaceAux(Iterator<Integer> it, Term t) {
		int childIndex = this.nextValidChildIndex(it);
		return this.copyReplacingArgument(childIndex, it, t);
	}

	/**
	 * Returns the next child index from the specified position iterator.
	 *
	 * @param position an iterator over a position, expected to have a next element
	 * @return the next valid child index
	 * @throws IndexOutOfBoundsException if the next index is not a valid child
	 *         index in this function
	 */
	private int nextValidChildIndex(Iterator<Integer> position) {
		// 'position' is supposed to have a next element, hence we can safely write
		// this.
		int childIndex = position.next();

		// Check whether childIndex is out of bounds.
		if (this.isChildIndexOutOfBounds(childIndex))
			throw new IndexOutOfBoundsException(childIndex + " -- " + this);

		return childIndex;
	}

	/**
	 * Builds a copy of this function where the subterm below the specified
	 * child index is replaced.
	 *
	 * @param childIndex the index of the child below which replacement occurs
	 * @param it an iterator over the remaining replacement position
	 * @param t the replacing term
	 * @return the function resulting from the replacement
	 */
	private Function copyReplacingArgument(
			int childIndex,
			Iterator<Integer> it,
			Term t) {

		Function replacement = new Function(this.rootSymbol);
		int argumentIndex = 0;
		for (Term argument : this.arguments) {
			replacement.arguments[argumentIndex] =
					this.replaceOrCopyArgument(argument, argumentIndex, childIndex, it, t);
			argumentIndex++;
		}

		return replacement;
	}

	/**
	 * Returns the replacement of the provided argument if it is located at the
	 * child index to replace, or a shallow copy otherwise.
	 *
	 * @param argument the argument to replace or copy
	 * @param argumentIndex the index of the provided argument
	 * @param childIndex the index of the child to replace
	 * @param it an iterator over the remaining replacement position
	 * @param t the replacing term
	 * @return the replacement of the argument or its shallow copy
	 */
	private Term replaceOrCopyArgument(
			Term argument,
			int argumentIndex,
			int childIndex,
			Iterator<Integer> it,
			Term t) {

		return argumentIndex == childIndex ? argument.replace(it, t) : argument.shallowCopy();
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, each variable with the provided replacement
	 * term.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term and the replacement term are not modified
	 * by this method.
	 * <p>
	 * Both this term and the replacement term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 *
	 * @param replacement a replacing term
	 * @return the term resulting from the replacement
	 */
	@Override
	protected Term replaceVariablesAux(Term replacement) {
		return this.copyWithMappedArguments(
				argument -> argument.replaceVariables(replacement));
	}

	/**
	 * An auxiliary, internal, method which tries to complete
	 * <code>theta</code> into a matcher of this term onto
	 * <code>t</code>.
	 * <p>
	 * This term and <code>t</code> are not modified by this
	 * method. On the contrary, <code>theta</code> may be
	 * modified, even if this method fails.
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 *
	 * @param t a term
	 * @param theta a substitution
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a matcher of this term onto
	 * <code>t</code>
	 */
	@Override
	protected boolean isMoreGeneralThanAux(Term t, Substitution theta) {
		if (this == t)
			return true;

		if (!(t instanceof Function targetFunction) ||
				this.rootSymbol != targetFunction.rootSymbol)
			return false;

		return this.hasMoreGeneralArgumentsThan(targetFunction, theta);
	}

	/**
	 * Tries to complete <code>theta</code> by matching this function's
	 * arguments onto the corresponding arguments of the specified function.
	 *
	 * @param targetFunction the function this function is matched onto
	 * @param theta a substitution
	 * @return <code>true</code> iff every argument could be matched
	 */
	private boolean hasMoreGeneralArgumentsThan(
			Function targetFunction,
			Substitution theta) {

		for (int argumentIndex = 0; argumentIndex < this.arguments.length; argumentIndex++) {
			Term sourceArgument = this.arguments[argumentIndex];
			if (!sourceArgument.isMoreGeneralThan(
					targetFunction.arguments[argumentIndex], theta))
				return false;
		}

		return true;
	}

	/**
	 * Tries to complete <code>theta</code> into a
	 * <code>tau</code>-matcher of <code>s</code> onto
	 * <code>t</code> ie, tries to complete
	 * <code>theta</code> so that <code>s</code> is
	 * <code>tau</code>-more general than <code>t</code>
	 * for <code>theta</code>.
	 * <p>
	 * Both <code>s</code> and <code>t</code> are not
	 * modified by this method. On the contrary,
	 * <code>theta</code> may be modified, even if
	 * this method fails.
	 *
	 * @param s a function
	 * @param t a function
	 * @param tau a set of positions
	 * @param theta a substitution
	 * @return <code>true</code> iff <code>theta</code> could
	 * be completed into a <code>tau</code>-matcher of
	 * <code>s</code> onto <code>t</code>
	 */
	public static boolean tauMoreGeneral(Function s, Function t,
			SoP tau, Substitution theta) {

		// If s or t do not point to a function, then the following
		// code fails:
		s = (Function) s.findSchema();
		t = (Function) t.findSchema();

		if (s == t)
			return true;

		return s.isTauMoreGeneralThan(t, tau, theta);
	}

	/**
	 * An auxiliary, internal, method which tries to complete
	 * <code>theta</code> into a <code>tau</code>-matcher of
	 * this function onto <code>target</code>.
	 * <p>
	 * This function and <code>target</code> are not modified by this
	 * method. On the contrary, <code>theta</code> may be modified,
	 * even if this method fails.
	 * <p>
	 * Both this function and <code>target</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * <p>
	 * Moreover, it is supposed that <code>this != target</code>.
	 *
	 * @param target a function
	 * @param tau a set of positions
	 * @param theta a substitution
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a <code>tau</code>-matcher of this
	 * function onto <code>target</code>
	 */
	private boolean isTauMoreGeneralThan(Function target, SoP tau, Substitution theta) {
		if (this.rootSymbol != target.rootSymbol)
			return false;

		for (int argumentIndex = 0; argumentIndex < this.arguments.length; argumentIndex++) {
			if (!this.isTauArgumentMoreGeneralThan(
					target, tau, theta, argumentIndex))
				return false;
		}

		return true;
	}

	/**
	 * Checks the <code>tau</code>-more-general condition for one argument.
	 *
	 * @param target the function this function is matched onto
	 * @param tau a set of positions
	 * @param theta a substitution
	 * @param argumentIndex the argument index to check
	 * @return <code>true</code> iff the argument satisfies the
	 * <code>tau</code>-more-general condition
	 */
	private boolean isTauArgumentMoreGeneralThan(
			Function target,
			SoP tau,
			Substitution theta,
			int argumentIndex) {

		Term mappedTerm = tau.getMappedTerm(this.rootSymbol, argumentIndex);
		Term sourceArgument = this.arguments[argumentIndex];

		return mappedTerm != null ?
				mappedTerm.isMoreGeneralThan(sourceArgument) :
				sourceArgument.isMoreGeneralThan(
						target.arguments[argumentIndex], theta);
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether the terms <code>s</code> and <code>t</code>
	 * are unifiable. If they are unifiable, then the computed
	 * most general unifier is applied to them (hence, they are
	 * modified). If they are not unifiable, then they may also
	 * be modified.
	 * <p>
	 * Both <code>s</code> and <code>t</code> are supposed to
	 * be their class representative. It is also supposed
	 * that <code>s != t</code>.
	 * <p>
	 * Moreover, this term is supposed to be the schema term
	 * of <code>s</code>.
	 *
	 * @param s a term whose schema term is this term
	 * @param t a term
	 * @return <code>true</code> iff <code>s</code> and
	 * <code>t</code> are unifiable, or they contain a cycle
	 * at the end of this method
	 */
	@Override
	protected boolean unifyClosureAux(Term s, Term t) {
		Term tSchema = t.getSchema();

		if (tSchema instanceof Variable) {
			s.union(t);
			return true;
		}

		if (!(tSchema instanceof Function schemaFunction) || this.rootSymbol != schemaFunction.rootSymbol)
			return false;

		s.union(t);
		return this.unifyClosureArguments(schemaFunction);
	}

	/**
	 * Tries to close unification recursively on this function's arguments
	 * against the corresponding arguments of the specified schema function.
	 *
	 * @param schemaFunction the schema function whose arguments are matched
	 * against this function's arguments
	 * @return <code>true</code> iff every corresponding argument pair can be
	 * closed by unification
	 */
	private boolean unifyClosureArguments(Function schemaFunction) {
		for (int argumentIndex = 0; argumentIndex < this.arguments.length; argumentIndex++) {
			Term sourceArgument = this.arguments[argumentIndex];
			if (!sourceArgument.unifyClosure(schemaFunction.arguments[argumentIndex]))
				return false;
		}

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for finding a unification solution from this
	 * term.
	 * <p>
	 * If a solution is found and <code>theta != null</code>,
	 * then <code>theta</code> is completed with the solution.
	 * <p>
	 * This term is supposed to be the schema of its class
	 * representative.
	 *
	 * @param theta a substitution
	 * @return <code>true</code> iff a solution could be found
	 */
	@Override
	protected boolean findUnifSolutionAux(Substitution theta) {
		this.visited = true;
		for (Term argument : this.arguments)
			if (!argument.findUnifSolution(theta))
				return false;
		this.visited = false;

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for applying the distributivity rule to this
	 * term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative. It is not modified by
	 * this method.
	 * <p>
	 * Used in the left-unification decision procedure.
	 *
	 * @param rho the number of applications of rho
	 * to this term
	 * @return the resulting term
	 */
	@Override
	protected Term distributeAux(int rho) {
		return this.copyWithMappedArguments(argument -> argument.distribute(rho));
	}

	/**
	 * An auxiliary, internal method, which is used
	 * for reducing this term by a single step of rewriting
	 * using the provided rule (specified as an oriented
	 * equation). The resulting term is this term
	 * modified in place.
	 * <p>
	 * If something has changed after reduction
	 * (meaning that this term is reducible with
	 * the provided rule) then the <code>changed</code>
	 * flag of this term is set to <code>true</code>
	 * (can be checked using method <code>hasChanged</code>).
	 * <p>
	 * The provided equation is supposed to be in normal
	 * form: the substitution rho is distributed through
	 * it and its left-hand side either is a variable or
	 * has the form rho^i(a variable).
	 * <p>
	 * It is supposed that the substitution rho is
	 * already distributed through this term before
	 * it is reduced. It is also distributed after the
	 * reduction.
	 * <p>
	 * It is supposed that the <code>changed</code>
	 * flag of this term is set to <code>false</code>.
	 * <p>
	 * Used in the left-unification decision procedure.
	 *
	 * @param equation a rule (specified as an oriented
	 * equation)
	 * @return the resulting term
	 */
	@Override
	protected Term reduceWithLeftUnificationRuleAux(LuEquation equation) {
		for (int argumentIndex = 0; argumentIndex < this.arguments.length; argumentIndex++)
			this.reduceArgumentWithLeftUnificationRule(argumentIndex, equation);

		return this;
	}

	/**
	 * Reduces the argument at the specified index with the provided
	 * left-unification rule and propagates its changed flag.
	 *
	 * @param argumentIndex the index of the argument to reduce
	 * @param equation the left-unification rule
	 */
	private void reduceArgumentWithLeftUnificationRule(
			int argumentIndex,
			LuEquation equation) {

		Term sourceArgument = this.arguments[argumentIndex];
		Term reducedArgument = sourceArgument.reduceWithLeftUnificationRule(equation);
		this.changed = this.changed || sourceArgument.changed;
		this.arguments[argumentIndex] = reducedArgument;
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term is this term.
	 * <p>
	 * Used in the implementation of step 2 of
	 * Alg. A-2.
	 *
	 * @param rho a substitution to apply to, and
	 * complete from, this term
	 * @return this term
	 */
	@Override
	protected Term applyAndCompleteRho(Substitution rho) {
		for (int argumentIndex = 0; argumentIndex < this.arguments.length; argumentIndex++)
			this.applyAndCompleteRhoToArgument(argumentIndex, rho);

		return this;
	}

	/**
	 * Applies and completes the specified substitution from the argument at
	 * the provided index, then stores the resulting argument.
	 *
	 * @param argumentIndex the index of the argument to update
	 * @param rho the substitution to apply to, and complete from, the argument
	 */
	private void applyAndCompleteRhoToArgument(
			int argumentIndex,
			Substitution rho) {

		Term sourceArgument = this.arguments[argumentIndex];
		this.arguments[argumentIndex] = sourceArgument.applyAndCompleteRho(rho);
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * This term is not modified by this method.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param theta a substitution
	 * @return a term resulting from applying
	 * the specified substitution to this term
	 */
	@Override
	protected Term applyAux(Substitution theta) {

		if (this.arguments.length == UNARY_ARITY) {
			// We introduce a slight improvement here.
			// If this term has the form s(t) where s
			// is a unary function symbol and
			// theta(t) = s^{a_1,...,a_l,b)(u)
			// then we return s^{a_1,...,a_l,b+1)(u).
			Term appliedArgument =
					this.arguments[FIRST_ARGUMENT_INDEX].apply(theta);
			Term optimizedTerm = this.tryIncrementMatchingHatFunction(appliedArgument);
			if (optimizedTerm != null)
				return optimizedTerm;

			return this.shallowCopyWithArgument(
					FIRST_ARGUMENT_INDEX,
					appliedArgument);
		}

		return this.copyWithAppliedArguments(theta);
	}

	/**
	 * Builds a copy of this function after applying the specified substitution
	 * to each argument.
	 *
	 * @param theta the substitution to apply
	 * @return the resulting function
	 */
	private Function copyWithAppliedArguments(Substitution theta) {
		return this.copyWithMappedArguments(argument -> argument.apply(theta));
	}

	/**
	 * Tries to apply the unary hat-function optimization to the specified
	 * already-applied argument.
	 *
	 * @param appliedArgument the argument after applying the substitution
	 * @return the incremented hat function, or <code>null</code> if the
	 *         optimization does not apply
	 * @throws ArithmeticException if the incremented closing exponent cannot be
	 * represented as an <code>int</code>
	 */
	private Term tryIncrementMatchingHatFunction(Term appliedArgument) {
		if (!(appliedArgument instanceof HatFunction hatFunction) ||
				this.rootSymbol !=
						hatFunction.getRootSymbol().getSimpleContext().getRootSymbol())
			return null;

		HatFunction incrementedHatFunction = new HatFunction(hatFunction);
		incrementedHatFunction.setB(
				Math.incrementExact(incrementedHatFunction.getB()));
		return incrementedHatFunction;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term (which is modified by this method).
	 *
	 * @param theta a substitution
	 */
	@Override
	protected void applyInPlaceAux(Substitution theta) {
		int argumentIndex = 0;
		for (Term argument : this.arguments)
			this.arguments[argumentIndex++] =
					applyInPlaceReplacementFor(argument, theta);
	}

	/**
	 * Applies the specified substitution to the provided argument, preserving
	 * the current in-place behavior for non-variable arguments.
	 *
	 * @param argument the argument to update
	 * @param theta the substitution to apply
	 * @return the term that must replace the specified argument
	 */
	private static Term applyInPlaceReplacementFor(Term argument, Substitution theta) {
		if (argument instanceof Variable variable) {
			Term replacement = theta.get(variable);
			if (replacement != null)
				return replacement.shallowCopy();
			return argument;
		}

		argument.applyInPlace(theta);
		return argument;
	}

	/**
	 * Rewrites this term at inner positions with the
	 * rules of the provided TRS.
	 * <p>
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * <p>
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param trs a TRS for rewriting this term
	 * @return the collection of terms resulting from
	 * rewriting this term at inner positions
	 */
	@Override
	protected Collection<Term> rewriteAtInnerPositions(Trs trs) {
		// The collection to return at the end.
		Collection<Term> result = new ArrayList<>();

		// We rewrite each subterm just below the root.
		for (int rewrittenArgumentIndex = 0;
				rewrittenArgumentIndex < this.arguments.length;
				rewrittenArgumentIndex++)
			this.addRewritesAtArgument(result, rewrittenArgumentIndex, trs);

		return result;
	}

	/**
	 * Adds the terms obtained by rewriting the argument at the specified index.
	 *
	 * @param rewrittenTerms the collection to complete
	 * @param rewrittenArgumentIndex the index of the rewritten argument
	 * @param trs the TRS used for rewriting
	 */
	private void addRewritesAtArgument(
			Collection<Term> rewrittenTerms, int rewrittenArgumentIndex, Trs trs) {

		for (Term rewrittenArgument :
				this.arguments[rewrittenArgumentIndex].rewriteWith(trs))
			rewrittenTerms.add(this.shallowCopyWithArgument(
					rewrittenArgumentIndex,
					rewrittenArgument));
	}

	/**
	 * Returns a shallow copy of this function where the argument at the
	 * specified index is replaced with the provided term.
	 *
	 * @param replacedArgumentIndex the index of the argument to replace
	 * @param replacementArgument the replacing argument
	 * @return the resulting function
	 */
	private Function shallowCopyWithArgument(
			int replacedArgumentIndex,
			Term replacementArgument) {

		Function result = new Function(this.rootSymbol);
		for (int argumentIndex = 0;
				argumentIndex < result.arguments.length;
				argumentIndex++)
			result.arguments[argumentIndex] = (argumentIndex == replacedArgumentIndex ?
					replacementArgument :
					this.arguments[argumentIndex].shallowCopy());

		return result;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * unfold this term with the provided rule at the
	 * provided position (specified as an iterator).
	 * <p>
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative. Moreover, <code>it</code>
	 * is supposed to have a next element.
	 *
	 * @param rule a rule for unfolding this term
	 * @param it an iterator, that has a next element,
	 * over a position where the unfolding takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param unfoldVariablePositions a boolean indicating whether
	 * unfolding of variable positions is enabled
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>, a subterm of this term
	 * @return the term resulting from unfolding
	 * this term, or <code>null</code> if the
	 * unfolding fails
	 * @throws IndexOutOfBoundsException when the
	 * provided iterator does not correspond to a
	 * valid position in this term
	 */
	@Override
	protected Term unfoldWithAux(RuleTrs rule,
			Iterator<Integer> it,
			boolean dir, boolean unfoldVariablePositions,
			Map<Term, Term> copies) {

		int childIndex = this.nextValidChildIndex(it);
		return this.copyUnfoldingArgument(
				childIndex,
				rule,
				it,
				dir,
				unfoldVariablePositions,
				copies);
	}

	/**
	 * Builds a copy of this function by unfolding the argument at the specified
	 * index and deep-copying all other arguments.
	 *
	 * @param childIndex the index of the child below which unfolding occurs
	 * @param rule the rule used for unfolding
	 * @param it an iterator over the remaining unfolding position
	 * @param dir a boolean indicating the unfolding direction
	 * @param unfoldVariablePositions a boolean indicating whether unfolding of
	 *        variable positions is enabled
	 * @param copies a set of subterm copies
	 * @return the function resulting from unfolding, or <code>null</code> if
	 *         unfolding fails
	 */
	private Function copyUnfoldingArgument(
			int childIndex,
			RuleTrs rule,
			Iterator<Integer> it,
			boolean dir,
			boolean unfoldVariablePositions,
			Map<Term, Term> copies) {

		Function result = new Function(this.rootSymbol);
		int argumentIndex = 0;
		for (Term argument : this.arguments) {
			Term unfoldedArgument = this.unfoldOrCopyArgument(
					argument,
					argumentIndex == childIndex,
					rule,
					it,
					dir,
					unfoldVariablePositions,
					copies);

			if (unfoldedArgument == null)
				return null;

			result.arguments[argumentIndex++] = unfoldedArgument;
		}

		return result;
	}

	/**
	 * Unfolds or copies the specified argument depending on whether it is at
	 * the unfolded position.
	 *
	 * @param argument the argument to unfold or copy
	 * @param shouldUnfold a boolean indicating whether the argument must be
	 *        unfolded
	 * @param rule the rule used for unfolding
	 * @param position an iterator over the unfolded position
	 * @param dir a boolean indicating the unfolding direction
	 * @param unfoldVariablePositions a boolean indicating whether unfolding of
	 *        variable positions is enabled
	 * @param copies a set of subterm copies
	 * @return the unfolded or copied argument, or <code>null</code> if
	 *         unfolding fails
	 */
	private Term unfoldOrCopyArgument(
			Term argument,
			boolean shouldUnfold,
			RuleTrs rule,
			Iterator<Integer> position,
			boolean dir,
			boolean unfoldVariablePositions,
			Map<Term, Term> copies) {

		if (shouldUnfold)
			return argument.unfoldWith(
					rule, position, dir, unfoldVariablePositions, copies);

		return argument.deepCopy(copies);
	}

	/**
	 * An iterator over the positions of a function.
	 *
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	private class FunctionIterator implements Iterator<Position> {

		/**
		 * The current argument index of the iterated function.
		 */
		protected int currentArgumentIndex = -1;

		/**
		 * An iterator over the current argument of the iterated function.
		 */
		protected Iterator<Position> argumentIterator = null;

		/**
		 * Returns <code>true</code> if the iteration has more elements and
		 * <code>false</code> otherwise.
		 *
		 * @return <code>true</code> if the iterator has more elements and
		 *   <code>false</code> otherwise
		 */
		@Override
		public boolean hasNext() {
			return this.isBeforeRootPosition() ||
					this.hasUnvisitedArgument() ||
					this.currentArgumentHasNextPosition();
		}

		/**
		 * Checks whether the iterator has not returned the root position yet.
		 *
		 * @return <code>true</code> iff the root position is still pending
		 */
		private boolean isBeforeRootPosition() {
			return currentArgumentIndex == -1;
		}

		/**
		 * Checks whether an argument remains to be visited and no argument
		 * iterator is currently active.
		 *
		 * @return <code>true</code> iff an argument iterator can still be opened
		 */
		private boolean hasUnvisitedArgument() {
			return argumentIterator == null && currentArgumentIndex < arguments.length;
		}

		/**
		 * Checks whether the current argument iterator can still produce a
		 * position, or whether a later argument remains.
		 *
		 * @return <code>true</code> iff iteration can continue from the current
		 *         argument state
		 */
		private boolean currentArgumentHasNextPosition() {
			return argumentIterator != null &&
					(argumentIterator.hasNext() ||
							currentArgumentIndex < arguments.length - 1);
		}

		/**
		 * Returns the next element in the iteration.
		 *
		 * @return the next element in the iteration
		 * @throws NoSuchElementException when iteration has no more elements
		 */
		@Override
		public Position next() throws NoSuchElementException {
			if (this.isBeforeRootPosition())
				return this.nextRootPosition();

			while (currentArgumentIndex < arguments.length) {
				this.ensureArgumentIterator();

				if (argumentIterator.hasNext())
					return argumentIterator.next().addFirst(currentArgumentIndex);

				this.moveToNextArgument();
			}

			throw new NoSuchElementException();
		}

		/**
		 * Returns the root position and moves the iterator to the first argument.
		 *
		 * @return the root position
		 */
		private Position nextRootPosition() {
			currentArgumentIndex = 0;
			return new Position();
		}

		/**
		 * Opens an iterator over the current argument when none is active.
		 */
		private void ensureArgumentIterator() {
			if (argumentIterator == null)
				argumentIterator = iteratorForArgument(currentArgumentIndex);
		}

		/**
		 * Moves the iterator state to the next argument.
		 */
		private void moveToNextArgument() {
			currentArgumentIndex++;
			argumentIterator = null;
		}

		/**
		 * Returns an iterator over the positions of the argument at the
		 * specified index.
		 *
		 * @param argumentIndex the argument index
		 * @return an iterator over the argument positions
		 */
		protected Iterator<Position> iteratorForArgument(int argumentIndex) {
			return arguments[argumentIndex].iterator();
		}

		/**
		 * Unsupported operation.
		 */
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}

	/**
	 * An auxiliary, internal, method which returns
	 * an iterator over the positions of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	protected Iterator<Position> iteratorAux() {
		return new FunctionIterator();
	}

	/**
	 * Applies the specified action directly to this function and its
	 * arguments, in prefix order.
	 *
	 * @param action the action to apply to each subterm
	 */
	@Override
	protected void forEachSubtermAux(Consumer<? super Term> action) {
		action.accept(this);
		for (Term argument : this.arguments)
			argument.findSchema().forEachSubtermAux(action);
	}

	/**
	 * A shallow iterator over the positions of a function.
	 * Such an iterator stops at variable positions: it
	 * does not consider the parent of a variable position.
	 *
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	private final class ShallowFunctionIterator extends FunctionIterator {

		/**
		 * Returns a shallow iterator over the positions of the argument at the
		 * specified index.
		 *
		 * @param argumentIndex the argument index
		 * @return a shallow iterator over the argument positions
		 */
		@Override
		protected Iterator<Position> iteratorForArgument(int argumentIndex) {
			return arguments[argumentIndex].shallowIterator();
		}
	}

	/**
	 * Returns a shallow iterator over the positions of
	 * this term. Such an iterator stops at subterms i.e.,
	 * it does not consider the class representative nor
	 * the schema of the subterms.
	 *
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<Position> shallowIterator() {
		return new ShallowFunctionIterator();
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the depth of this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return the depth of this term
	 */
	@Override
	protected int depthAux() {
		// Constant symbols have depth 0.
		if (this.arguments.length == 0)
			return 0;

		int maxArgumentDepth = -1;
		for (Term argument : this.arguments) {
			int argumentDepth = argument.depth();
			maxArgumentDepth = Math.max(maxArgumentDepth, argumentDepth);
		}
		return 1 + maxArgumentDepth;
	}

	/**
	 * An auxiliary, internal, method for computing
	 * the maximum arity of a function symbol in
	 * this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return the maximum arity of a function
	 * symbol in this term
	 */
	@Override
	protected int maxArityAux() {

		// The arity of the root symbol of this term.
		int maxArity = this.arguments.length;

		// We compute the max arity by considering
		// the direct subterms of this term.
		for (Term argument : this.arguments) {
			int argumentMaxArity = argument.maxArity();
			maxArity = Math.max(maxArity, argumentMaxArity);
		}

		return maxArity;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * check whether this term embeds the specified term
	 * (homeomorphic embedding).
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * <p>
	 * Moreover, it is supposed that <code>this != t</code>.
	 *
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term embeds the
	 * specified term
	 */
	@Override
	protected boolean embedsAux(Term t) {
		if (t instanceof Function targetFunction &&
				this.rootSymbol == targetFunction.rootSymbol &&
				this.embedsFunctionWithSameRoot(targetFunction))
			return true;

		return this.hasArgumentEmbedding(t);
	}

	/**
	 * Checks whether this function embeds the specified function by matching
	 * arguments pairwise, assuming both functions have the same root symbol.
	 *
	 * @param targetFunction the function to compare with this one
	 * @return <code>true</code> iff every argument of this function embeds the
	 * corresponding argument of <code>targetFunction</code>
	 */
	private boolean embedsFunctionWithSameRoot(Function targetFunction) {
		for (int argumentIndex = 0;
				argumentIndex < this.arguments.length;
				argumentIndex++) {
			Term sourceArgument = this.arguments[argumentIndex];
			if (!sourceArgument.embeds(targetFunction.arguments[argumentIndex]))
				return false;
		}

		return true;
	}

	/**
	 * Checks whether one of this function's arguments embeds the specified term.
	 *
	 * @param t the term to search for through argument embeddings
	 * @return <code>true</code> iff some argument of this function embeds
	 * <code>t</code>
	 */
	private boolean hasArgumentEmbedding(Term t) {
		for (Term sourceArgument : this.arguments)
			if (sourceArgument.embeds(t))
				return true;

		return false;
	}

	/**
	 * An internal method which returns
	 * <code>REN(CAP(this term))</code>.
	 * <p>
	 * See [Arts &amp; Giesl, TCS'00] for a definition
	 * of <code>REN</code> and <code>CAP</code>.
	 * <p>
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 *
	 * @param trs the TRS whose defined symbols are used
	 * for computing the result
	 * @param root a boolean indicating whether the term
	 * at root position has to be replaced with a variable
	 * if its root symbol is defined in <code>trs</code>
	 * @return <code>REN(CAP(this term))</code>
	 */
	@Override
	protected Term rencap(Trs trs, boolean root) {
		if (root && trs.isDefined(this.rootSymbol))
			return new Variable();

		return this.copyWithMappedArguments(
				argument -> argument.findSchema().rencap(trs, true));
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing the polynomial corresponding to this term.
	 * It fills the provided <code>Coefficients</code>
	 * with missing coefficients.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param coefficients the coefficients of the polynomials
	 * associated with each function symbol and each tuple symbol
	 * @return the polynomial corresponding to this term
	 */
	@Override
	protected Polynomial toPolynomialAux(PolyInterpretation coefficients) {

		// First, we get the coefficients corresponding
		// to the root symbol of this term.
		PolynomialConst[] coefficientsForSymbol = coefficients.get(this.rootSymbol);

		// We also compute the polynomials corresponding
		// to each argument of this term.
		Polynomial[] argumentPolynomials =
				this.computeArgumentPolynomials(coefficients);

		List<Polynomial> operands =
				polynomialOperands(coefficientsForSymbol, argumentPolynomials);

		return PolynomialComp.simplified(ArithOperator.PLUS, operands);
	}

	/**
	 * Computes the polynomials corresponding to each argument of this term.
	 *
	 * @param coefficients the coefficients of the polynomials associated
	 * with each function symbol and each tuple symbol
	 * @return the polynomial of each argument
	 */
	private Polynomial[] computeArgumentPolynomials(PolyInterpretation coefficients) {

		int arity = this.arguments.length;
		Polynomial[] argumentPolynomials = new Polynomial[arity];
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++) {
			Term sourceArgument = this.arguments[argumentIndex];
			argumentPolynomials[argumentIndex] =
					sourceArgument.toPolynomial(coefficients);
		}

		return argumentPolynomials;
	}

	/**
	 * Builds the operands of the polynomial corresponding to this term.
	 *
	 * @param coefficientsForSymbol the coefficients corresponding to this
	 * function's root symbol
	 * @param argumentPolynomials the polynomials corresponding to the
	 * arguments of this term
	 * @return the operands of the polynomial
	 */
	private static List<Polynomial> polynomialOperands(
			PolynomialConst[] coefficientsForSymbol,
			Polynomial[] argumentPolynomials) {

		// Let us compute each operand. We have to consider all
		// the possible combinations of elements of argumentPolynomials. We proceed
		// as explained on this Web page:
		// http://owaisahussain.blogspot.com/2014/03/a-faster-non-recursive-algorithm-to.html
		List<Polynomial> operands = new ArrayList<>();
		operands.add(coefficientsForSymbol[CONSTANT_COEFFICIENT_INDEX]);
		addNonConstantPolynomialOperands(
				operands,
				coefficientsForSymbol,
				argumentPolynomials);

		return operands;
	}

	/**
	 * Adds the operands built from non-constant coefficients.
	 *
	 * @param operands the operand list to complete
	 * @param coefficientsForSymbol the coefficients corresponding to this
	 * function's root symbol
	 * @param argumentPolynomials the polynomials corresponding to the
	 * arguments of this term
	 */
	private static void addNonConstantPolynomialOperands(
			List<Polynomial> operands,
			PolynomialConst[] coefficientsForSymbol,
			Polynomial[] argumentPolynomials) {

		for (int coefficientIndex = CONSTANT_COEFFICIENT_INDEX + 1;
				coefficientIndex < coefficientsForSymbol.length;
				coefficientIndex++)
			operands.add(polynomialOperand(
					coefficientsForSymbol[coefficientIndex],
					coefficientIndex,
					argumentPolynomials));
	}

	/**
	 * Builds one operand of the polynomial corresponding to this term.
	 *
	 * @param coefficient the coefficient at the selected index
	 * @param coefficientIndex the selected coefficient index
	 * @param argumentPolynomials the polynomials corresponding to the
	 * arguments of this term
	 * @return the operand
	 */
	private static Polynomial polynomialOperand(
			PolynomialConst coefficient,
			int coefficientIndex,
			Polynomial[] argumentPolynomials) {

		return PolynomialComp.simplified(
				ArithOperator.TIMES,
				polynomialOperandFactors(
						coefficient,
						coefficientIndex,
						argumentPolynomials));
	}

	/**
	 * Builds the factors of one operand of the polynomial corresponding to this
	 * term.
	 *
	 * @param coefficient the coefficient at the selected index
	 * @param coefficientIndex the selected coefficient index
	 * @param argumentPolynomials the polynomials corresponding to the
	 * arguments of this term
	 * @return the factors of the operand
	 */
	private static List<Polynomial> polynomialOperandFactors(
			PolynomialConst coefficient,
			int coefficientIndex,
			Polynomial[] argumentPolynomials) {

		List<Polynomial> factors = new ArrayList<>();
		factors.add(coefficient);
		addSelectedArgumentPolynomialFactors(
				factors,
				coefficientIndex,
				argumentPolynomials);

		return factors;
	}

	/**
	 * Adds the argument polynomial factors selected by the binary
	 * representation of the specified coefficient index.
	 *
	 * @param factors the factor list to complete
	 * @param coefficientIndex the selected coefficient index
	 * @param argumentPolynomials the polynomials corresponding to the
	 * arguments of this term
	 */
	private static void addSelectedArgumentPolynomialFactors(
			List<Polynomial> factors,
			int coefficientIndex,
			Polynomial[] argumentPolynomials) {

		char[] coefficientBits = coefficientSelectionBits(coefficientIndex);
		int rightmostBitIndex = coefficientBits.length - 1;
		for (int bitIndex = rightmostBitIndex; 0 <= bitIndex; bitIndex--)
			if (coefficientBits[bitIndex] == '1')
				factors.add(argumentPolynomials[
						argumentIndexSelectedBy(bitIndex, rightmostBitIndex)]);
	}

	/**
	 * Returns the binary selection bits of the specified coefficient index.
	 *
	 * @param coefficientIndex the selected coefficient index
	 * @return the binary selection bits
	 */
	private static char[] coefficientSelectionBits(int coefficientIndex) {
		return Integer.toBinaryString(coefficientIndex).toCharArray();
	}

	/**
	 * Returns the argument index selected by the specified coefficient bit.
	 *
	 * @param bitIndex the index of the selected bit
	 * @param rightmostBitIndex the index of the rightmost bit
	 * @return the argument index selected by the bit
	 */
	private static int argumentIndexSelectedBy(
			int bitIndex,
			int rightmostBitIndex) {

		return rightmostBitIndex - bitIndex;
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * generating a weight for each function symbol
	 * and each tuple symbol occurring in this term.
	 * The generated weights are added to the provided
	 * weight function.
	 * <p>
	 * Used for implementing the Knuth-Bendix order
	 * technique for proving termination of TRSs.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param weights a weight function for storing
	 * the weight of each function symbol and each
	 * tuple symbol occurring in this term
	 */
	@Override
	protected void generateKBOWeightsAux(WeightFunction weights) {
		if (this.hasAlreadyBeenVisitedInCurrentTraversal())
			return;

		// First, we add the root symbol of this term
		// to the provided weight function.
		weights.get(this.rootSymbol);

		// Then, we add the symbols occurring in the
		// proper subterms of this term to the provided
		// weight function.
		for (Term argument : this.arguments)
			argument.findSchema().generateKBOWeightsAux(weights);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing a tuple version of this term when this
	 * term is a function. If this term is not a function
	 * then this method merely returns this term.
	 * <p>
	 * Used in the dependency pair framework.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return a tuple version of this term
	 */
	@Override
	protected Term toTupleAux() {
		FunctionSymbol tupleSymbol = this.rootSymbol.toTupleSymbol();
		return this.convertedWithRootSymbol(tupleSymbol);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing a function version of this term when
	 * this term is a tuple. If this term is not a tuple
	 * then this method merely returns this term.
	 * <p>
	 * Used in the dependency pair framework.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @return a function version of this term
	 */
	@Override
	protected Term toFunctionAux() {
		FunctionSymbol functionSymbol = this.rootSymbol.toFunctionSymbol();
		return this.convertedWithRootSymbol(functionSymbol);
	}

	/**
	 * Returns this term converted to the specified root symbol.
	 *
	 * @param targetSymbol the root symbol of the converted term
	 * @return this term if the root symbol is unchanged, or a converted function
	 */
	private Term convertedWithRootSymbol(FunctionSymbol targetSymbol) {
		if (this.rootSymbol == targetSymbol)
			return this;

		Function converted = new Function(targetSymbol);
		this.copyArgumentsTo(converted);

		return converted;
	}

	/**
	 * Copies this function's arguments into the specified function.
	 *
	 * @param targetFunction the function receiving the copied argument references
	 */
	private void copyArgumentsTo(Function targetFunction) {
		System.arraycopy(
				this.arguments,
				0,
				targetFunction.arguments,
				0,
				this.arguments.length);
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO1) in the definition of a lexicographic path
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 *
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	@Override
	protected boolean lpo1(LexOrder order, Term t) {
		if (t instanceof Variable)
			return this.contains(t);

		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2a) in the definition of a lexicographic path
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 *
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	@Override
	protected boolean lpo2a(LexOrder order, Term t) {
		if (!(t instanceof Function))
			return false;

		// We try to set s_i >= t for some i.
		for (Term sourceArgument : this.arguments)
			if (tryCompleteLPOFromArgument(order, sourceArgument, t))
				return true;

		return false;
	}

	/**
	 * Tries to complete the specified order by checking whether the provided
	 * source argument is greater than or equal to the target term.
	 *
	 * @param order the order to complete when the attempt succeeds
	 * @param sourceArgument the argument from which the completion is attempted
	 * @param targetTerm the term compared with the source argument
	 * @return <code>true</code> iff the completion succeeds
	 */
	private static boolean tryCompleteLPOFromArgument(
			LexOrder order, Term sourceArgument, Term targetTerm) {
		LexOrder speculativeOrder = LexOrder.speculativeViewOf(order);
		if (!sourceArgument.completeLPO(speculativeOrder, targetTerm))
			return false;

		speculativeOrder.commitTo(order);
		return true;
	}

	/**
	 * Tries to complete the specified order through a copied order, committing
	 * the copied order only when the completion succeeds.
	 *
	 * @param order the order to complete when the attempt succeeds
	 * @param completionAttempt the completion attempt to run on the copy
	 * @return <code>true</code> iff the completion attempt succeeds
	 */
	private static boolean tryCompleteWithCopiedOrder(
			LexOrder order,
			Predicate<LexOrder> completionAttempt) {
		LexOrder copiedOrder = new LexOrder(order);
		if (!completionAttempt.test(copiedOrder))
			return false;

		order.addAll(copiedOrder);
		return true;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2b) in the definition of a lexicographic path
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 *
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	@Override
	protected boolean lpo2b(LexOrder order, Term t) {
		if (!(t instanceof Function targetFunction))
			return false;

		return this.tryCompleteLPOWithRootPrecedence(order, targetFunction);
	}

	/**
	 * Tries to complete the specified order by orienting this function's root
	 * symbol above the target function's root symbol, then checking all target
	 * arguments.
	 *
	 * @param order the order to complete when the attempt succeeds
	 * @param targetFunction the target function whose root and arguments are
	 * checked
	 * @return <code>true</code> iff the root precedence and all target
	 * argument checks succeed
	 */
	private boolean tryCompleteLPOWithRootPrecedence(LexOrder order, Function targetFunction) {
		LexOrder speculativeOrder = LexOrder.speculativeViewOf(order);
		if (!this.canCompleteLPOWithRootPrecedence(
				speculativeOrder, targetFunction))
			return false;

		speculativeOrder.commitTo(order);
		return true;
	}

	/**
	 * Checks whether this function can complete LPO with root precedence using
	 * the specified copied order.
	 *
	 * @param copiedOrder the copied order to complete
	 * @param targetFunction the target function whose root and arguments are
	 * checked
	 * @return <code>true</code> iff the copied order can be completed
	 */
	private boolean canCompleteLPOWithRootPrecedence(
			LexOrder copiedOrder,
			Function targetFunction) {
		// We try to add f > g to the copy of the order,
		// where f is the root symbol of this term and g
		// is that of t.
		if (!copiedOrder.add(this.rootSymbol, targetFunction.rootSymbol))
			return false;

		// If success, we try to set this > t_j for all j.
		for (Term targetArgument : targetFunction.arguments)
			if (!this.completeLPOStrict(copiedOrder, targetArgument))
				return false;

		return true;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2c) in the definition of a lexicographic path
	 * order (see [Baader &amp; Nipkow, 1998], p. 118) is satisfied.
	 * <p>
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 *
	 * @param order a strict partial order on function symbols
	 * @param t a term
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	@Override
	protected boolean lpo2c(LexOrder order, Term t) {
		if (!(t instanceof Function targetFunction) || this.rootSymbol != targetFunction.rootSymbol)
			return false;

		return this.tryCompleteLPOWithSameRoot(order, targetFunction);
	}

	/**
	 * Tries to complete the specified order for the LPO same-root case.
	 *
	 * @param order the order to complete when the attempt succeeds
	 * @param targetFunction the same-root target function
	 * @return <code>true</code> iff all target arguments are strictly smaller
	 * and the first differing argument can be oriented strictly
	 */
	private boolean tryCompleteLPOWithSameRoot(LexOrder order, Function targetFunction) {
		LexOrder speculativeOrder = LexOrder.speculativeViewOf(order);
		if (!this.canCompleteLPOWithSameRoot(speculativeOrder, targetFunction))
			return false;

		speculativeOrder.commitTo(order);
		return true;
	}

	/**
	 * Checks whether this function can complete LPO in the same-root case using
	 * the specified copied order.
	 *
	 * @param copiedOrder the copied order to complete
	 * @param targetFunction the same-root target function
	 * @return <code>true</code> iff the copied order can be completed
	 */
	private boolean canCompleteLPOWithSameRoot(
			LexOrder copiedOrder,
			Function targetFunction) {
		// We try to set this > t_j for all j.
		for (Term targetArgument : targetFunction.arguments)
			if (!this.completeLPOStrict(copiedOrder, targetArgument))
				return false;

		// Let i be such that this_k = t_k for all k < i and
		// this_i != t_i. We try to set this_i > t_i.
		int differingArgumentIndex = this.firstDifferingArgumentIndex(targetFunction);
		if (differingArgumentIndex < 0)
			return false;

		Term sourceArgument = this.arguments[differingArgumentIndex];
		Term targetArgument = targetFunction.arguments[differingArgumentIndex];
		return sourceArgument.completeLPOStrict(copiedOrder, targetArgument);
	}

	/**
	 * Returns the index of the first argument that differs between this
	 * function and the provided function.
	 *
	 * @param targetFunction the function to compare with this one
	 * @return the first differing argument index, or <code>-1</code>
	 * if all arguments are equal
	 */
	private int firstDifferingArgumentIndex(Function targetFunction) {
		for (int argumentIndex = 0; argumentIndex < this.arguments.length; argumentIndex++)
			if (!this.arguments[argumentIndex].deepEquals(
					targetFunction.arguments[argumentIndex]))
				return argumentIndex;

		return -1;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for computing the weight of this term relatively
	 * to the provided weight function.
	 * <p>
	 * The weight of a term results from adding up the
	 * weights of all occurrences of symbols in the
	 * term (see p. 124 of [Baader &amp; Nipkow, 1998]).
	 *
	 * @param weights a weight function
	 * @return the weight of this term relatively
	 * to the provided weight function
	 */
	@Override
	protected Integer getWeightAux(WeightFunction weights) {
		// First, we get the weight of this function's root symbol.
		Integer rootWeight = weights.get(this.rootSymbol)[0].integerValue(null);

		if (rootWeight == null)
			return null;

		return this.addArgumentWeights(rootWeight, weights);
	}

	/**
	 * Adds this function's argument weights to the specified initial weight.
	 *
	 * @param initialWeight the weight accumulated before processing arguments
	 * @param weights a weight function
	 * @return the total weight, or <code>null</code> if some argument has no
	 * computable weight
	 */
	private Integer addArgumentWeights(int initialWeight, WeightFunction weights) {
		int totalWeight = initialWeight;
		for (Term argument : this.arguments) {
			Integer argumentWeight = argument.getWeight(weights);
			if (argumentWeight == null)
				return null;

			totalWeight += argumentWeight;
		}

		return totalWeight;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2a) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader &amp; Nipkow, 1998]).
	 * <p>
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 *
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	@Override
	protected boolean kbo2a(LexOrder order, WeightFunction weights, Term t) {
		// We have to check whether this term has the form f^n(x)
		// where x is a variable and t = x.
		return this.arguments.length == UNARY_ARITY &&
				t instanceof Variable &&
				this.isUnaryIterationEndingAt(t);
	}

	/**
	 * Checks whether this term has the form <code>f^n(x)</code>, where
	 * <code>f</code> is this term's root symbol and <code>x</code> is
	 * the specified target variable.
	 *
	 * @param targetVariable the variable expected at the end of the unary
	 *        iteration
	 * @return <code>true</code> iff this term is a unary iteration of its
	 *         root symbol ending at the specified variable
	 */
	private boolean isUnaryIterationEndingAt(Term targetVariable) {
		Term nestedArgument = this.arguments[FIRST_ARGUMENT_INDEX];
		while (nestedArgument instanceof Function nestedFunction) {
			if (nestedFunction.rootSymbol != this.rootSymbol)
				return false;
			nestedArgument = nestedFunction.arguments[FIRST_ARGUMENT_INDEX];
		}

		return nestedArgument == targetVariable;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2b) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader &amp; Nipkow, 1998]).
	 * <p>
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 *
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	@Override
	protected boolean kbo2b(LexOrder order, WeightFunction weights, Term t) {
		return t instanceof Function targetFunction &&
				order.add(this.rootSymbol, targetFunction.rootSymbol);
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2c) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader &amp; Nipkow, 1998]).
	 * <p>
	 * Both this term and <code>t</code> are supposed
	 * to be the schema of their class representative.
	 *
	 * @param order a strict partial order on function symbols
	 * @param weights a weight function
	 * @param t a term
	 * @return <code>true</code> iff the completion of
	 * the specified order succeeds
	 */
	@Override
	protected boolean kbo2c(LexOrder order, WeightFunction weights, Term t) {
		if (!(t instanceof Function targetFunction) ||
				this.rootSymbol != targetFunction.rootSymbol)
			return false;

		return this.tryCompleteKBOWithSameRoot(order, weights, targetFunction);
	}

	/**
	 * Tries to complete the specified order for the KBO same-root case.
	 *
	 * @param order the order to complete when the attempt succeeds
	 * @param weights the weight function used for strict KBO completion
	 * @param targetFunction the same-root target function
	 * @return <code>true</code> iff the first differing argument can be
	 *         oriented strictly
	 */
	private boolean tryCompleteKBOWithSameRoot(
			LexOrder order, WeightFunction weights, Function targetFunction) {

		return tryCompleteWithCopiedOrder(
				order,
				copiedOrder -> this.canCompleteKBOWithSameRoot(
						copiedOrder,
						weights,
						targetFunction));
	}

	/**
	 * Checks whether this function can complete KBO in the same-root case using
	 * the specified copied order.
	 *
	 * @param copiedOrder the copied order to complete
	 * @param weights the weight function used for strict KBO completion
	 * @param targetFunction the same-root target function
	 * @return <code>true</code> iff the copied order can be completed
	 */
	private boolean canCompleteKBOWithSameRoot(
			LexOrder copiedOrder,
			WeightFunction weights,
			Function targetFunction) {
		// Let i be such that this_k = t_k for all k < i and
		// this_i != t_i. We try to set this_i > t_i.
		int differingArgumentIndex =
				this.firstDifferingArgumentIndex(targetFunction);
		if (differingArgumentIndex < 0)
			return false;

		Term sourceArgument = this.arguments[differingArgumentIndex];
		Term targetArgument = targetFunction.arguments[differingArgumentIndex];
		return sourceArgument.completeKBOStrict(
				copiedOrder,
				weights,
				targetArgument);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * building empty filters for the function and tuple
	 * symbols occurring in this term.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param filtering the data structure to complete
	 * with the filters built from this term
	 */
	@Override
	protected void buildFiltersAux(ArgFiltering filtering) {
		filtering.add(this.rootSymbol);

		for (Term argument : this.arguments)
			argument.buildFilters(filtering);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * applying the specified argument filtering to this
	 * term.
	 * <p>
	 * This term is not modified by this method.
	 * <p>
	 * This term is supposed to be the schema of its
	 * class representative.
	 *
	 * @param filtering an argument filtering to apply
	 * to this term
	 * @return the resulting term
	 */
	@Override
	protected Term applyFiltersAux(ArgFiltering filtering) {
		Filter filter = filtering.get(this.rootSymbol);
		return filter == null ? this : this.filteredTerm(filtering, filter);
	}

	/**
	 * Applies the specified filter to this function.
	 *
	 * @param filtering the argument filtering to apply recursively
	 * @param filter the filter associated with this function's root symbol
	 * @return the filtered term, or this function if the filter has no
	 *         supported value
	 */
	private Term filteredTerm(ArgFiltering filtering, Filter filter) {
		Term filteredSingleArgument =
				this.filteredSingleArgument(filtering, filter);
		if (filteredSingleArgument != null)
			return filteredSingleArgument;

		Term filteredFunction =
				this.filteredFunctionWithSelectedArguments(filtering, filter);
		return filteredFunction == null ? this : filteredFunction;
	}

	/**
	 * Applies the single-argument form of the specified filter.
	 *
	 * @param filtering the argument filtering to apply recursively
	 * @param filter the filter associated with this function's root symbol
	 * @return the selected filtered argument, or <code>null</code> if the
	 *         filter is not a single-argument filter
	 */
	private Term filteredSingleArgument(ArgFiltering filtering, Filter filter) {
		Integer selectedIndex = filter.getIntValue();
		if (selectedIndex == null)
			return null;

		return this.arguments[selectedIndex].applyFilters(filtering);
	}

	/**
	 * Applies the argument-list form of the specified filter.
	 *
	 * @param filtering the argument filtering to apply recursively
	 * @param filter the filter associated with this function's root symbol
	 * @return the filtered function, or <code>null</code> if the filter is not
	 *         an argument-list filter
	 */
	private Term filteredFunctionWithSelectedArguments(
			ArgFiltering filtering,
			Filter filter) {

		List<Integer> selectedIndices = filter.getListValue();
		if (selectedIndices == null)
			return null;

		List<Term> filteredArguments =
				this.filteredArguments(filtering, selectedIndices);

		return new Function(
				this.filteredSymbolFor(filteredArguments.size()), filteredArguments);
	}

	/**
	 * Builds the filtered arguments selected by the specified indices.
	 *
	 * @param filtering the argument filtering to apply recursively
	 * @param selectedIndices the selected argument indices
	 * @return the filtered arguments, in selected-index order
	 */
	private List<Term> filteredArguments(
			ArgFiltering filtering,
			List<Integer> selectedIndices) {

		List<Term> filteredArguments = new ArrayList<>();
		for (Integer selectedArgumentIndex : selectedIndices) {
			Term selectedArgument = this.arguments[selectedArgumentIndex];
			filteredArguments.add(selectedArgument.applyFilters(filtering));
		}

		return filteredArguments;
	}

	/**
	 * Returns the root symbol to use for a filtered function with the
	 * specified arity.
	 *
	 * @param arity the arity of the filtered function
	 * @return the filtered root symbol, preserving tuple-symbol status
	 */
	private FunctionSymbol filteredSymbolFor(int arity) {
		FunctionSymbol filteredSymbol =
				FunctionSymbol.intern(this.rootSymbol.getName(), arity);
		if (this.rootSymbol.isTupleSymbol())
			filteredSymbol = filteredSymbol.toTupleSymbol();
		return filteredSymbol;
	}

	/**
	 * Computes a substitution form of this term.
	 * <p>
	 * More precisely, if this term has the form
	 * <code>f(t_1,...,t_n)</code> then, for all
	 * <code>i</code> such that <code>t_i</code>
	 * is ground, this method adds the mapping
	 * <code>x_i -> t_i</code> to the provided
	 * substitution <code>theta</code>, where
	 * <code>x_i</code> is a new variable. At
	 * the same time, it replaces <code>t_i</code>
	 * by <code>x_i</code> in this term.
	 * The term <code>s</code> resulting from
	 * these replacements is returned.
	 * <p>
	 * This term is not modified by this method.
	 * <p>
	 * Moreover, at the end of this method
	 * <code>s theta</code> is equal to this term.
	 *
	 * @param theta a substitution
	 * @return the term resulting from replacing
	 * subterms of this term by new variables
	 */
	@Override
	public Term toSubstitution(Substitution theta) {
		return this.copyWithMappedArguments(
				argument -> substitutionReplacementFor(argument, theta));
	}

	/**
	 * Returns the term to use in substitution form for the specified argument.
	 *
	 * @param argument the argument to replace if it is ground
	 * @param theta the substitution to complete when a fresh variable is used
	 * @return the original argument if it is not ground, or a fresh variable
	 *         mapped to it otherwise
	 */
	private static Term substitutionReplacementFor(Term argument, Substitution theta) {
		if (!argument.isGround())
			return argument;

		Variable replacementVariable = new Variable();
		theta.add(replacementVariable, argument);
		return replacementVariable;
	}

	/**
	 * An auxiliary, internal, method which returns a string
	 * representation of this term relatively to the given
	 * set of variable symbols.
	 * <p>
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * <p>
	 * If <code>shallow == false</code> then a deep search
	 * is processed through this term i.e., the schema of
	 * the class representative of each subterm is considered.
	 * Moreover, this term is supposed to be the schema of
	 * its class representative.
	 *
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return a string representation of this term
	 */
	@Override
	protected String toStringAux(Map<Variable, String> variables, boolean shallow) {
		StringBuilder result = new StringBuilder(this.rootSymbol.toString());
		if (this.arguments.length > 0)
			this.appendArgumentsTo(result, variables, shallow);

		return result.toString();
	}

	/**
	 * Appends this function's arguments to the specified string builder.
	 *
	 * @param result the string builder to complete
	 * @param variables a set of pairs <code>(V,s)</code> where
	 *        <code>s</code> is the string associated to variable
	 *        <code>V</code>
	 * @param shallow a boolean indicating whether a shallow search has
	 *        to be processed through this term
	 */
	private void appendArgumentsTo(
			StringBuilder result, Map<Variable, String> variables, boolean shallow) {

		int remainingArguments = this.arguments.length;
		result.append("(");
		for (Term argument : this.arguments) {
			result.append(argument.toString(variables, shallow));
			if (0 < --remainingArguments)
				result.append(",");
		}
		result.append(")");
	}
}
