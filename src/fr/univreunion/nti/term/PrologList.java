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

package fr.univreunion.nti.term;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Iterator;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.program.trs.argfiltering.ArgFiltering;
import fr.univreunion.nti.program.trs.polynomial.Polynomial;
import fr.univreunion.nti.program.trs.reducpair.LexOrder;
import fr.univreunion.nti.program.trs.reducpair.PolyInterpretation;
import fr.univreunion.nti.program.trs.reducpair.WeightFunction;
import fr.univreunion.nti.term.leftunif.LuEquation;

/**
 * A Prolog list i.e., [], [e_1,...,e_n], [e_1,...,e_n|L]
 * 
 * An object of this class is mutable.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PrologList extends Term {

	/**
	 * The root symbol for a Prolog list.
	 */
	public final static FunctionSymbol PROLOG_LIST_ROOT_SYMBOL =
			FunctionSymbol.getInstance("|", 2);

	/**
	 * The empty list, as a constant object.
	 */
	private final static PrologList EMPTY_PROLOG_LIST =
			new PrologList((Term) null, (Term) null);  

	/**
	 * The first element of this Prolog list.
	 */
	private final Term first;

	/**
	 * The tail of this Prolog list.
	 */
	private final Term tail;

	/**
	 * Constructs a Prolog list with the given first
	 * element and tail.
	 * 
	 * @param first the first element of this Prolog list
	 * @param tail the tail of this Prolog list
	 */
	private PrologList(Term first, Term tail) {
		this.first = first;
		this.tail = tail;	
	}

	/**
	 * Constructs a Prolog list using the given iterator
	 * over a list of elements and the given suffix.
	 * The given iterator must have a next element.
	 * 
	 * @param it an iterator over a list of elements
	 * @param suffix the suffix of this Prolog list
	 * @throws NoSuchElementException if <code>it</code>
	 * does not have a next element
	 * @throws NullPointerException if <code>suffix</code>
	 * is <code>null</code> or <code>it.next()</code>
	 * is <code>null</code>
	 */
	private PrologList(ListIterator<Term> it, Term suffix) {
		if (suffix == null)
			throw new NullPointerException("cannot build a Prolog list with a null tail");

		this.first = it.next();

		if (this.first == null)
			throw new NullPointerException("cannot build a Prolog list with a null element");

		if (it.hasNext())
			this.tail = new PrologList(it, suffix);
		else 
			this.tail = suffix;
	}

	/**
	 * Returns the empty Prolog list.
	 * 
	 * @return the empty Prolog list
	 */
	public static PrologList emptyPrologList() {
		return EMPTY_PROLOG_LIST;
	}

	/**
	 * Constructs a Prolog list with the given elements.
	 * The given list of elements must be non-empty.
	 * 
	 * @param elements the elements of this Prolog list
	 * @throws NoSuchElementException if <code>elements</code>
	 * is empty
	 * @throws NullPointerException if an element of
	 * <code>elements</code> is <code>null</code>
	 */
	public PrologList(List<Term> elements) {
		this(elements.listIterator(), EMPTY_PROLOG_LIST);
	}

	/**
	 * Constructs a Prolog list with the given elements
	 * and suffix. The given list of elements must be
	 * non-empty.
	 * 
	 * @param elements the elements of this Prolog list
	 * @param suffix the suffix of this Prolog list
	 * @throws NoSuchElementException if <code>elements</code>
	 * is empty
	 * @throws NullPointerException if <code>suffix</code>
	 * is <code>null</code> or an element of <code>elements</code>
	 * is <code>null</code>
	 */
	public PrologList(List<Term> elements, Term suffix) {
		this(elements.listIterator(), suffix);
	}

	/**
	 * An auxiliary, internal method, that flattens the
	 * subterms of this term i.e., makes each subterm
	 * its own schema and the only element of its class.
	 */
	/*
	@Override
	protected void flattenAux() {
		if (this.first != null)
			this.first.flatten();
		if (this.tail != null)
			this.tail.flatten();
	}
	 */

	/**
	 * Returns the root symbol of this term.
	 * 
	 * @return the root symbol of this term
	 */
	@Override
	public FunctionSymbol getRootSymbol() {
		return PROLOG_LIST_ROOT_SYMBOL;
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean hasSameStructureAsAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether some other term is equal to
	 * this one.
	 * 
	 * This a deep, structural, comparison which is
	 * used in the implementation of substitutions.
	 * 
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
		// As this != t, if this list is the empty list then
		// t is not, hence we have to return false.
		if (this == EMPTY_PROLOG_LIST)
			return false;

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.
		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			if (t instanceof PrologList) {
				PrologList other = (PrologList) t;
				// As this != t, if other is the empty list then
				// this list is not, hence we have to return false.
				if (other == EMPTY_PROLOG_LIST)
					return false;
				return this.first.deepEqualsAux1(other.first) &&
						this.tail.deepEqualsAux1(other.tail);
			}

			return false;
		}

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to return a shallow copy of this term i.e.,
	 * a copy where each variable is kept unchanged.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return a shallow copy of this term
	 */
	@Override
	protected Term shallowCopyAux() {
		if (this == EMPTY_PROLOG_LIST) return this;

		return new PrologList(
				this.first.shallowCopy(),
				this.tail.shallowCopy());
	}

	/**
	 * An auxiliary, internal, method which returns a
	 * deep copy of this term i.e., a copy where each
	 * subterm is also copied, except the variables
	 * not occurring in the specified collection.
	 * 
	 * The specified collection contains the variables
	 * that must be copied. If it is <code>null</code>
	 * then all the variables must be copied. 
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
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
			Map<Term,Term> copies) {

		if (this == EMPTY_PROLOG_LIST) return this;

		return new PrologList(
				this.first.deepCopy(varsToBeCopied, copies),
				this.tail.deepCopy(varsToBeCopied, copies));
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains the given
	 * term.
	 * 
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
		// If this list is the empty list, then we return false.
		// Otherwise, we check whether the first element or the
		// tail of this list contain the provided term.
		if (this != EMPTY_PROLOG_LIST) {
			// If this term's mark is not set to the current time,
			// then this term has not been visited yet. Otherwise,
			// it has already been visited and then we have to
			// return false.
			long time = Term.getCurrentTime();
			if (this.mark < time) {
				this.mark = time;
				return this.first.containsAux1(t) ||
						this.tail.containsAux1(t);
			}
		}

		return false;
	}
	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	@Override
	protected boolean containsRhoAux() {
		// If this list is the empty list, then we return false.
		// Otherwise, we check whether the first element or the
		// tail of this list contain rho.
		if (this != EMPTY_PROLOG_LIST) {
			// If this term's mark is not set to the current time,
			// then this term has not been visited yet. Otherwise,
			// it has already been visited and then we have to
			// return false.
			long time = Term.getCurrentTime();
			if (this.mark < time) {
				this.mark = time;
				return this.first.findSchema().containsRhoAux() ||
						this.tail.findSchema().containsRhoAux();
			}
		}

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * check whether this term is ground i.e., contains
	 * no variable.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return <code>true</code> iff this term contains
	 * no variable
	 */
	@Override
	protected boolean isGroundAux() {
		// If this list is the empty list, then we return true.
		// Otherwise, we check whether the first element and
		// the tail of this list are ground.
		if (this != EMPTY_PROLOG_LIST) {
			// If this term's mark is not set to the current time,
			// then this term has not been visited yet. Otherwise,
			// it has already been visited and then we have to
			// return true.
			long time = Term.getCurrentTime();
			if (this.mark < time) {
				this.mark = time;
				return this.first.findSchema().isGroundAux() &&
						this.tail.findSchema().isGroundAux();
			}
		}

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of variables of this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return the set of variables of this term
	 */
	@Override
	protected Set<Variable> getVariablesAux() {
		// The set to return at the end of this method.
		HashSet<Variable> Vars = new HashSet<Variable>();

		// If this list is the empty list, then we return
		// an empty set. Otherwise, we return the set
		// consisting of the variables in the first element
		// of this list and the variables in the tail of this
		// list.
		if (this != EMPTY_PROLOG_LIST) {
			// If this term's mark is not set to the current time,
			// then this term has not been visited yet. Otherwise,
			// it has already been visited and then we have to
			// return an empty set because the set of variables
			// of this term has already been considered.
			long time = Term.getCurrentTime();
			if (this.mark < time) {
				this.mark = time;
				Vars.addAll(this.first.findSchema().getVariablesAux());
				Vars.addAll(this.tail.findSchema().getVariablesAux());
			}
		}

		return Vars;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to compute the number of occurrences of each
	 * variable of this term.
	 * 
	 * The provided mapping is filled accordingly.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param occurrences a mapping which associates
	 * variables with their number of occurrences in 
	 * this term
	 */
	@Override
	protected void getVariableOccurrencesAux(Map<Variable, Integer> occurrences) {
		// If this list is the empty list, then it contains no variable.
		// Otherwise, we count the variables in its first element and
		// in its tail.
		if (this != EMPTY_PROLOG_LIST) {
			this.first.getVariableOccurrences(occurrences);
			this.tail.getVariableOccurrences(occurrences);
		}
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * build the set of function symbols of this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return the set of function symbols of this term
	 */
	@Override
	protected Set<FunctionSymbol> getFunSymbolsAux() {
		// The set to return at the end of this method.
		HashSet<FunctionSymbol> symbols = new HashSet<FunctionSymbol>();

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return an empty set because the set of function
		// symbols of this term has already been considered.
		
		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			symbols.add(this.getRootSymbol());
			if (this != EMPTY_PROLOG_LIST) {
				symbols.addAll(this.first.findSchema().getFunSymbolsAux());
				symbols.addAll(this.tail.findSchema().getFunSymbolsAux());
			}
		}

		return symbols;
	}
	
	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term getAux(int i) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Collection<Position> dposAux(Term t, boolean var) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term replaceAux(Iterator<Integer> it, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, each variable with the provided term
	 * <code>t</code>.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term and <code>t</code> are not modified by
	 * this method.
	 * 
	 * Both this term and <code>t</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * 
	 * @param t a replacing term
	 * @return the term resulting from the replacement
	 */
	@Override
	protected Term replaceVariablesAux(Term t) {
		if (this == EMPTY_PROLOG_LIST) return this;

		return new PrologList(
				this.first.replaceVariables(t),
				this.tail.replaceVariables(t));
	}

	/**
	 * An auxiliary, internal, method which tries to complete
	 * <code>theta</code> into a matcher of this term onto
	 * <code>t</code>.
	 * 
	 * This term and <code>t</code> are not modified by this
	 * method. On the contrary, <code>theta</code> may be
	 * modified, even if this method fails.
	 * 
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
		if (this == t) return true;

		if (t instanceof PrologList) {
			PrologList other = (PrologList) t;

			// As here this != t, if one of this or t is the empty list
			// then we have to return false.
			if (this == EMPTY_PROLOG_LIST || other == EMPTY_PROLOG_LIST)
				return false;

			// Here, neither this list nor t is the empty list.
			return this.first.isMoreGeneralThan(other.first, theta) &&
					this.tail.isMoreGeneralThan(other.tail, theta);
		}

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether the terms <code>s</code> and <code>t</code>
	 * are unifiable. If they are unifiable, then the computed
	 * most general unifier is applied to them (hence, they are
	 * modified). If they are not unifiable, then they may also
	 * be modified.
	 * 
	 * Both <code>s</code> and <code>t</code> are supposed to
	 * be their class representative. It is also supposed
	 * that <code>s != t</code>.
	 * 
	 * Moreover, this term is supposed to be the schema term
	 * of <code>s</code>.
	 * 
	 * @param s a term whose schema term is this term
	 * @param t a term
	 * @return <code>true</code> iff <code>s</code> and
	 * <code>t</code> are unifiable or they contain a cycle
	 * at the end of this method
	 */
	@Override
	protected boolean unifyClosureAux(Term s, Term t) {
		Term tSchema = t.getSchema();

		if (tSchema instanceof PrologList) {
			PrologList l = (PrologList) tSchema;
			if (this == EMPTY_PROLOG_LIST && l == EMPTY_PROLOG_LIST) return true;
			if (this == EMPTY_PROLOG_LIST || l == EMPTY_PROLOG_LIST) return false;
			// Here, both this and l are not the empty Prolog list.
			s.union(t);
			return (this.first.unifyClosure(l.first) &&
					this.tail.unifyClosure(l.tail));
		}
		else if (tSchema instanceof Variable) {
			s.union(t);
			return true;
		}

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for finding a unification solution from this
	 * term.
	 * 
	 * If a solution is found and <code>theta != null</code>,
	 * then <code>theta</code> is completed with the solution.
	 * 
	 * This term is supposed to be the schema of its class
	 * representative.
	 * 
	 * @param theta a substitution
	 * @return <code>true</code> iff a solution could be found
	 */
	@Override
	protected boolean findUnifSolutionAux(Substitution theta) {

		this.visited = true;

		boolean result = (this == EMPTY_PROLOG_LIST) ||
				(this.first.findUnifSolution(theta)
						&& this.tail.findUnifSolution(theta));

		this.visited = false;

		return result;
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term distributeAux(int rho) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Term reduceWithAux(LuEquation E) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term applyAndCompleteRho(Substitution rho) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	/*
	@Override
	protected boolean propagate(Term hnode, int cost, boolean dir) {
		throw new UnsupportedOperationException();
	}
	 */

	/**
	 * An auxiliary, internal, method which is used
	 * to apply the specified substitution to this
	 * term.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * This term is not modified by this method.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param theta a substitution
	 * @return a term resulting from applying
	 * the specified substitution to this term
	 */
	@Override
	protected Term applyAux(Substitution theta) {
		if (this == EMPTY_PROLOG_LIST)
			return this;

		return new PrologList(
				this.first.apply(theta), this.tail.apply(theta));
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Collection<Term> rewriteAtInnerPositions(Trs IR) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term unfoldWithAux(RuleTrs R,
			Iterator<Integer> it,
			boolean dir, boolean var,
			Map<Term,Term> variables) {

		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Iterator<Position> iteratorAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	public Iterator<Position> shallowIterator() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected int depthAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected int maxArityAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @param t a term
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean embedsAux(Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term rencap(Trs IR, boolean root) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Polynomial toPolynomialAux(PolyInterpretation coefficients) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected void generateKBOWeightsAux(WeightFunction weights) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term toTupleAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term toFunctionAux() {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo1(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo2a(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo2b(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean lpo2c(LexOrder order, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Integer getWeightAux(WeightFunction weights) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean kbo2a(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean kbo2b(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected boolean kbo2c(LexOrder order, WeightFunction weights, Term t) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected void buildFiltersAux(ArgFiltering filtering) {
		throw new UnsupportedOperationException();
	}

	/**
	 * Unsupported operation.
	 * 
	 * @throws UnsupportedOperationException
	 */
	@Override
	protected Term applyFiltersAux(ArgFiltering filtering) {
		throw new UnsupportedOperationException();
	}

	/**
	 * An auxiliary, internal, method which returns a string
	 * representation of this term relatively to the given
	 * set of variable symbols.
	 * 
	 * If <code>shallow == true</code> then only a shallow
	 * search is processed through this term: it stops at
	 * subterms i.e., it does not consider the class
	 * representative nor the schema of the subterms.
	 * 
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
	protected String toStringAux(Map<Variable,String> variables, boolean shallow) {
		StringBuffer s = new StringBuffer("[");

		boolean first = true;
		PrologList l = this;
		while (l != EMPTY_PROLOG_LIST) {
			// We consider the first element of this list.
			if (first) first = false;
			else s.append(",");
			s.append(l.first.toString(variables, shallow));

			// Then, we consider the tail of this list.
			if (shallow) {
				s.append("|");
				s.append(l.tail.toString(variables, shallow));
				break;
			}
			// From here, shallow = false.
			Term t = l.tail.findSchema();
			if (t instanceof PrologList)
				l = (PrologList) t;
			else {
				s.append("|");
				s.append(t.toString(variables, shallow));
				break;
			}
		}

		s.append("]");

		return s.toString();
	}
}
