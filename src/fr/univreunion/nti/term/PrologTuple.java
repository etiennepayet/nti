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
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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
 * A flat Prolog tuple i.e., (e_1,...,e_n) where n >= 1 and
 * each e_i is not a tuple.
 * 
 * An object of this class is mutable.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PrologTuple extends Term {

	/**
	 * The root symbol for a Prolog tuple.
	 */
	public final static FunctionSymbol PROLOG_TUPLE_ROOT_SYMBOL =
			FunctionSymbol.getInstance(",", 2);

	/**
	 * The elements of this Prolog tuple.
	 */
	private final List<Term> elements = new LinkedList<Term>();

	/**
	 * Builds a flat Prolog tuple.
	 * 
	 * @param elements the elements of this tuple
	 * @throws IllegalArgumentException if the given
	 * list of elements is empty or contains
	 * <code>null</code>
	 */
	public PrologTuple(List<? extends Term> elements) {
		if (elements.isEmpty())
			throw new IllegalArgumentException("Prolog tuples cannot be empty");

		for (Term t : elements) {
			if (t == null)
				throw new NullPointerException("Prolog tuples do not permit null elements");

			if (t instanceof PrologTuple)
				// This Prolog tuple has to be flat,
				// hence if t is already a tuple, we
				// add the elements of t instead of t.
				this.elements.addAll(((PrologTuple) t).elements);
			else
				this.elements.add(t);
		}
	}

	/**
	 * Builds an empty Prolog tuple.
	 * For internal use only.
	 */
	private PrologTuple() {}

	/**
	 * Appends the specified term to the end of this 
	 * Prolog tuple.
	 * 
	 * For internal use only.
	 * 
	 * @param t term to be appended to this Prolog tuple
	 * @return true if this tuple changed as a result of
	 * the call
	 * @throws NullPointerException if the specified term
	 * is <code>null</code>
	 */
	private boolean add(Term t) {
		if (t == null)
			throw new NullPointerException("Prolog tuples do not permit null elements");

		return this.elements.add(t);
	}

	/**
	 * Appends all of the elements in the specified Prolog
	 * tuple to the end of this Prolog tuple.
	 * 
	 * For internal use only.
	 * 
	 * @param tuple Prolog tuple containing elements to be
	 * added to this Prolog tuple
	 * @return true if this tuple changed as a result of
	 * the call
	 * @throws NullPointerException if the specified term
	 * is <code>null</code>
	 */
	private boolean addAll(PrologTuple tuple) {
		return this.elements.addAll(tuple.elements);
	}

	/**
	 * Returns the root symbol of this term.
	 * 
	 * @return the root symbol of this term
	 */
	@Override
	public FunctionSymbol getRootSymbol() {
		return PROLOG_TUPLE_ROOT_SYMBOL;
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
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			if (t instanceof PrologTuple) {
				PrologTuple other = (PrologTuple) t;
				if (this.elements.size() == other.elements.size()) {
					for (Iterator<Term> it_this = this.elements.iterator(),
							it_other = other.elements.iterator();
							it_this.hasNext(); )
						if (!it_this.next().deepEqualsAux1(it_other.next()))
							return false;
					return true;
				}
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
		// The term that will be returned at the end.
		PrologTuple thisCopy = new PrologTuple();

		for (Term t : this.elements) {
			Term tCopy = t.shallowCopy();
			if (tCopy instanceof PrologTuple)
				thisCopy.addAll((PrologTuple) tCopy);
			else
				thisCopy.add(tCopy);
		}

		return thisCopy;
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

		// The term that will be returned at the end.
		PrologTuple thisCopy = new PrologTuple();

		for (Term t : this.elements) {
			Term tCopy = t.deepCopy(varsToBeCopied, copies);
			if (tCopy instanceof PrologTuple)
				thisCopy.addAll((PrologTuple) tCopy);
			else
				thisCopy.add(tCopy);
		}

		return thisCopy;
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
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return false.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			for (Term s : this.elements)
				if (s.containsAux1(t)) return true;
		}

		return false;
	}
	/**
	 * An auxiliary, internal, method which is used
	 * to check whether this term contains rho i.e.,
	 * an instance of <code>LUVariable</code> whose
	 * rho component is not 0.
	 * 
	 * Used in the implementation of step 3 of
	 * Alg. A-2.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return <code>true</code> iff this term
	 * contains rho
	 */
	@Override
	protected boolean containsRhoAux() {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return false.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			for (Term t : this.elements)
				if (t.findSchema().containsRhoAux()) return true;
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
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return true.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			for (Term t : this.elements)
				if (!t.findSchema().isGroundAux())
					return false;
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

		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have to
		// return an empty set because the set of variables
		// of this term has already been considered.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;
			for (Term t : this.elements)
				Vars.addAll(t.findSchema().getVariablesAux());
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
		for (Term t : this.elements)
			t.getVariableOccurrences(occurrences);
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
			for (Term t : this.elements)
				symbols.addAll(t.findSchema().getFunSymbolsAux());
		}

		return symbols;
	}

	/**
	 * An auxiliary, internal, method which returns
	 * the subterm of this term at the given single
	 * position.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. 
	 * 
	 * @param i a single position
	 * @return the subterm of this term at the given
	 * position
	 * @throws IndexOutOfBoundsException if <code>i</code>
	 * is not a valid position in this term
	 */
	@Override
	protected Term getAux(int i) {
		// Check whether i is out of bounds.
		if (i < 0 || i >= this.elements.size())
			throw new IndexOutOfBoundsException(i + " -- " + this);

		return this.elements.get(i);
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * return the subterm of this term at the position
	 * specified by the provided iterator.
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
	 * It is also supposed that <code>it</code> has a
	 * next element.
	 * 
	 * @param it an iterator (over a position) that has a
	 * next element
	 * @param shallow a boolean indicating whether a shallow
	 * search has to be processed through this term
	 * @return the subterm of this term at the given position
	 * @throws IndexOutOfBoundsException if the provided
	 * iterator does not correspond to a valid position in
	 * this term
	 */
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		// 'it' is supposed to have a next element, hence we can
		// safely write this.
		Integer i = it.next();

		// Check whether i is out of bounds.
		if (i < 0 || i >= this.elements.size())
			throw new IndexOutOfBoundsException(i + " -- " + this);

		return this.elements.get(i).get(it, shallow);
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the disagreement positions
	 * of this term and the specified term.
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * Moreover, it is supposed that <code>this != t</code>.
	 * 
	 * If the specified term is <code>null</code> then a
	 * collection consisting of the empty position (epsilon)
	 * is returned.
	 * 
	 * @param t a term
	 * @param var <code>true</code> iff disagreement pairs of the
	 * form <variable,variable> are allowed
	 * @return a collection consisting of the disagreement positions
	 * of this term and the given term
	 */
	@Override
	protected Collection<Position> dposAux(Term t, boolean var) {
		// We prefer not to support this operation so that
		// the method 'isUnifiableWithAux' in class Term is
		// not supported for Prolog tuples. Indeed, currently
		// the algorithm implemented by this method does not
		// work for Prolog tuples. 
		throw new UnsupportedOperationException();

		// The following code can be used in case this operation
		// becomes really needed in the future:

		/*
		// The collection to return at the end.
		Collection<Position> C = new LinkedList<Position>();

		if (t instanceof PrologTuple) {
			PrologTuple other = (PrologTuple) t;

			Iterator<Term> it1, it2;

			if (this.elements.size() <= other.elements.size()) {
				it1 = this.elements.iterator();
				it2 = other.elements.iterator();
			}
			else {
				it2 = this.elements.iterator();
				it1 = other.elements.iterator();
			}

			// Here, it1 is supposed to point to the
			// beginning of the shortest tuple.
			for (int i = 0; it1.hasNext(); i++) {
				Term s1 = it1.next(), s2 = it2.next();
				if (!it1.hasNext() && it2.hasNext())
					C.add(new Position(i));
				else
					for (Position p : s1.dpos(s2, var))
						C.add(p.addFirst(i));
			}
		}
		else
			C.add(new Position());

		return C;
		 */
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
		// The term that will be returned at the end.
		PrologTuple thisCopy = new PrologTuple();

		for (Term s : this.elements) {
			Term sCopy = s.replaceVariablesAux(t);
			if (sCopy instanceof PrologTuple)
				thisCopy.addAll((PrologTuple) sCopy);
			else
				thisCopy.add(sCopy);
		}

		return thisCopy;
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

		if (t instanceof PrologTuple) {

			PrologTuple other = (PrologTuple) t;
			if (this.elements.size() <= other.elements.size()) {

				Iterator<Term> it_this = this.elements.iterator();
				Iterator<Term> it_other = other.elements.iterator();
				while (it_this.hasNext()) {
					Term s_this = it_this.next(), s_other = it_other.next();
					if (!it_this.hasNext() && it_other.hasNext()) {
						PrologTuple tail = new PrologTuple();
						tail.add(s_other);
						while (it_other.hasNext())
							tail.add(it_other.next());
						if (!s_this.isMoreGeneralThan(tail, theta))
							return false;
					}
					else if (!s_this.isMoreGeneralThan(s_other, theta))
						return false; 
				}

				return true;
			}
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

		if (tSchema instanceof PrologTuple) {
			s.union(t);

			PrologTuple other = (PrologTuple) tSchema;
			Iterator<Term> it1, it2;

			if (this.elements.size() <= other.elements.size()) {
				it1 = this.elements.iterator();
				it2 = other.elements.iterator();
			}
			else {
				it2 = this.elements.iterator();
				it1 = other.elements.iterator();
			}

			// Here, it1 is supposed to point to the
			// beginning of the shortest tuple.
			while (it1.hasNext()) {
				Term s1 = it1.next(), s2 = it2.next();
				if (!it1.hasNext() && it2.hasNext()) {
					PrologTuple tail = new PrologTuple();
					tail.add(s2);
					while (it2.hasNext())
						tail.add(it2.next());
					if (!s1.unifyClosure(tail))
						return false;
				}
				else if (!s1.unifyClosure(s2))
					return false;
			}

			return true;			
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
		for (Term t : this.elements)
			if (!t.findUnifSolution(theta))
				return false;
		this.visited = false;

		return true;
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
		PrologTuple t = new PrologTuple();

		for (Term s : this.elements) {
			Term u = s.apply(theta);
			if (u instanceof PrologTuple)
				t.addAll((PrologTuple) u);
			else
				t.add(u);
		}

		return t;
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
		StringBuffer s = new StringBuffer("(");
		int l = this.elements.size();

		for (Term t : this.elements) {
			s.append(t.toString(variables, shallow));
			if (0 < --l) s.append(",");
		}

		s.append(")");

		return s.toString();
	}
}
