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
 * along with NTI. If not, see <http://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.term;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.NoSuchElementException;
import java.util.Set;

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
 * 
 * An object of this class is mutable.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Function extends Term {

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
		int i = 0;
		for (Term t : arguments) {
			if (t == null)
				throw new IllegalArgumentException(
						"construction of a term with a null subterm");
			this.arguments[i++] = t;
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
	 * An auxiliary, internal, method which is used to
	 * flatten this term i.e., make each of its subterms
	 * its own schema and the only element of its class.
	 */
	/*
	@Override
	protected void flattenAux() {
		for (Term t : this.arguments)
			t.flatten();
	}
	 */

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
	 * Returns the <code>i</code>-th child of this
	 * function.
	 * 
	 * @param i the index of the child to be returned
	 * @return the <code>i</code>-th child of this
	 * function, or <code>null</code> if <code>i</code>
	 * is not a valid child index in this function
	 */
	public Term getChild(int i) {
		// Check whether i is out of bounds.
		if (i < 0 || i >= this.arguments.length)
			return null;

		return this.arguments[i];
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether this term has the same structure as the specified
	 * term <code>t</code>. This term and <code>t</code> are
	 * not modified by this method.
	 * 
	 * This method implements a rough, but quickly computable,
	 * over-approximation of both the subsumption and the
	 * unification tests. It is essentially used for computing
	 * families (see method <code>getFamily</code> in class
	 * <code>FD_Graph</code>).
	 * 
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

		if (t instanceof Function) {
			Function other = (Function) t;
			if (this.rootSymbol == other.rootSymbol) {
				for (int i = 0; i < this.arguments.length; i++)
					if (!this.arguments[i].hasSameStructureAs(other.arguments[i]))
						return false;
				return true;
			}
		}

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * to check whether some other term is equal to
	 * this one.
	 * 
	 * This a deep, structural, comparison.
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
			if (t instanceof Function) {
				Function f = (Function) t;
				if (this.rootSymbol == f.rootSymbol) {
					for (int i = 0; i < this.arguments.length; i++)
						if (!this.arguments[i].deepEqualsAux1(f.arguments[i]))
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
		Function f = new Function(this.rootSymbol);

		int i = 0;
		for (Term t : this.arguments)
			f.arguments[i++] = t.shallowCopy();

		return f;
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
			Map<Term, Term> copies) {

		Function f = new Function(this.rootSymbol);

		int i = 0;
		for (Term t : this.arguments)
			f.arguments[i++] = t.deepCopy(varsToBeCopied, copies);

		return f;
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
			for (Term s : this.arguments)
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
			for (Term t : this.arguments)
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
			for (Term t : this.arguments)
				if (!t.findSchema().isGroundAux())
					return false;
		}

		return true;
	}

	/**
	 * Returns the function resulting from replacing,
	 * in this function, the arguments at the positions
	 * given by <code>m</code> with ground terms built
	 * from <code>tau</code>.
	 * 
	 * This function is not modified by this method.
	 * 
	 * The specified mode <code>m</code> is supposed to
	 * be compatible with this function and with the 
	 * specified set of positions <code>tau</code>. I.e.,
	 * if <code>p</code> denotes the root symbol of this
	 * function, then <code>p</code> is also the predicate
	 * symbol of <code>m</code>. Moreover, the argument
	 * positions given by <code>m</code> are included
	 * in the domain of <code>tau(p)</code>.
	 * 
	 * The returned function is built as follows.
	 * For each mapping <code>i -> t</code> in
	 * <code>tau(p)</code>, if <code>i</code> is
	 * in <code>m</code> then the <code>i</code>-th argument
	 * of this function is replaced with a ground instance
	 * of <code>t</code> (variables are replaced with the
	 * constant symbol <code>a</code>). The other arguments
	 * are deep copies of the corresponding arguments in
	 * this function.
	 * 
	 * @param m a mode, compatible with <code>tau</code>
	 * @param tau a set of positions
	 * @return the function resulting from grounding
	 * this function at some specific positions
	 */
	public Function ground(Mode m, SoP tau) {
		// The function that will be returned.
		Function f = new Function(this.rootSymbol);

		// The constant symbol that we use for grounding.
		FunctionSymbol symb = FunctionSymbol.getInstance("a", 0);
		LinkedList<Term> args = new LinkedList<Term>();
		Function zero = new Function(symb, args);

		// A data structure used for copying the arguments
		// that are not distinguished by tau.
		Map<Term, Term> copies = new HashMap<Term, Term>();

		for (int i = 0; i < this.arguments.length; i++)
			if (m.contains(i) && tau.inDomain(this.rootSymbol, i))
				f.arguments[i] = tau.get(this.rootSymbol, i).replaceVariables(zero);
			else
				f.arguments[i] = this.arguments[i].deepCopy(copies);

		return f;
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
			for (Term t : this.arguments)
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
		for (Term t : this.arguments)
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
			for (Term t : this.arguments)
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
	 * @return the subterm of this term at position
	 * <code>i</code>, or <code>null</code> if
	 * <code>i</code> is not a valid position in
	 * this term
	 */
	@Override
	protected Term getAux(int i) {
		return this.getChild(i);
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
	 * or <code>null</code> if the provided iterator does not
	 * correspond to a valid position in this term
	 */
	@Override
	protected Term getAux(Iterator<Integer> it, boolean shallow) {
		// 'it' is supposed to have a next element, hence we can
		// safely write this.
		Integer i = it.next();

		// Check whether i is out of bounds.
		if (i < 0 || i >= this.arguments.length)
			return null;

		return this.arguments[i].get(it, shallow);
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * a collection consisting of the hat subterms of this
	 * term.
	 * 
	 * There are no duplicate in the returned collection,
	 * i.e., if s and t are in the returned collection
	 * then they are not equal (w.r.t. a deep, structural,
	 * comparison).
	 *  
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return a collection consisting of the hat subterms
	 * of this term
	 */
	@Override
	protected Collection<Term> getHatSubtermsAux() {
		Collection<Term> result =  new LinkedList<>();

		for (Term s : this.arguments) {
			Collection<Term> result_s = s.findSchema().getHatSubtermsAux();
			// We add the elements of result_s to result
			// but only if they do not already occur in
			// result.
			for (Term u : result_s) {
				boolean found = false;
				for (Term v : result)
					if (u.deepEquals(v)) { found = true; break; }
				if (!found) result.add(u);
			}
		}

		if (result.isEmpty() && this.rootSymbol.isHatSymbol())
			result.add(this);

		return result;
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
		// The collection to return at the end.
		Collection<Position> C = new LinkedList<Position>();

		if (t instanceof Function) {
			Function f = (Function)t;
			if (this.rootSymbol == f.rootSymbol)
				for (int i = 0; i < this.arguments.length; i++)
					for (Position p : this.arguments[i].dpos(f.arguments[i], var))
						C.add(p.addFirst(i));
			else
				C.add(new Position());
		}
		else
			C.add(new Position());

		return C;
	}

	/**
	 * An auxiliary, internal, method which is used to build
	 * the term obtained from replacing, in a copy of this
	 * term, the subterm at the position specified by
	 * <code>it</code> with <code>t</code>.
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
		// 'it' is supposed to have a next element, hence we can
		// safely write this.
		Integer i = it.next();

		// Check whether i is out of bounds.
		if (i < 0 || i >= this.arguments.length)
			throw new IndexOutOfBoundsException(i + " -- " + this);

		// If i is a valid position, then we build a copy of this
		// term where the subterm at position i is replaced.
		Function F = new Function(this.rootSymbol);
		int k = 0;
		for (Term F_k : this.arguments) {
			F.arguments[k] = (k == i ?
					F_k.replace(it, t) : F_k.shallowCopy());
			k++;
		}

		return F;
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
		// The function that will be returned.
		Function f = new Function(this.rootSymbol);

		for (int i = 0; i < this.arguments.length; i++)
			f.arguments[i] = this.arguments[i].replaceVariables(t);

		return f;
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

		if (t instanceof Function) {
			Function f = (Function) t;
			if (this.rootSymbol == f.rootSymbol) {
				for (int i = 0; i < this.arguments.length; i++)
					if (!this.arguments[i].isMoreGeneralThan(f.arguments[i], theta))
						return false;
				return true;
			}
		}

		return false;
	}

	/**
	 * Tries to complete <code>theta</code> into a
	 * <code>tau</code>-matcher of <code>s</code> onto
	 * <code>t</code> ie, tries to complete
	 * <code>theta</code> so that <code>s</code> is
	 * <code>tau</code>-more general than <code>t</code>
	 * for <code>theta</code>.
	 * 
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

		if (s == t) return true;
		else return s.isTauMoreGeneralThan(t, tau, theta);
	}

	/**
	 * An auxiliary, internal, method which tries to complete
	 * <code>theta</code> into a <code>tau</code>-matcher of
	 * this function onto <code>f</code>.
	 * 
	 * This function and <code>f</code> are not modified by this
	 * method. On the contrary, <code>theta</code> may be modified,
	 * even if this method fails.
	 * 
	 * Both this function and <code>f</code> are supposed to be
	 * the schemas of their respective class representatives.
	 * 
	 * Moreover, it is supposed that <code>this != f</code>.
	 * 
	 * @param f a function
	 * @param tau a set of positions
	 * @param theta a substitution
	 * @return <code>true</code> iff the provided substitution
	 * could be completed into a <code>tau</code>-matcher of this
	 * function onto <code>f</code>
	 */
	private boolean isTauMoreGeneralThan(Function f, SoP tau, Substitution theta) {
		if (this.rootSymbol == f.rootSymbol) {
			for (int i = 0; i < this.arguments.length; i++) {
				Term tau_i = tau.get(this.rootSymbol, i);
				if (tau_i != null &&
						!tau_i.isMoreGeneralThan(this.arguments[i]))
					return false;
				if (tau_i == null &&
						!this.arguments[i].isMoreGeneralThan(f.arguments[i], theta))
					return false;
			}
			return true;
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

		if (tSchema instanceof Function) {
			Function f = (Function) tSchema;
			if (this.rootSymbol == f.rootSymbol) {
				s.union(t);
				for (int i = 0; i < this.arguments.length; i++)
					if (!this.arguments[i].unifyClosure(f.arguments[i]))
						return false; 
				return true;
			}
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
		for (Term t : this.arguments)
			if (!t.findUnifSolution(theta))
				return false;
		this.visited = false;

		return true;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for applying the distributivity rule to this
	 * term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. It is not modified by
	 * this method.
	 * 
	 * Used in the left-unification decision procedure.
	 * 
	 * @param rho the number of applications of rho
	 * to this term
	 * @return the resulting term
	 */
	@Override
	protected Term distributeAux(int rho) {
		Function f = new Function(this.rootSymbol);

		int i = 0;
		for (Term t: this.arguments)
			f.arguments[i++] = t.distribute(rho);

		return f;
	}

	/**
	 * An auxiliary, internal method, which is used
	 * for reducing this term by a single step of rewriting
	 * using the provided rule (specified as an oriented
	 * equation). The resulting term is this term
	 * modified in place.
	 * 
	 * If something has changed after reduction
	 * (meaning that this term is reducible with
	 * the provided rule) then the <code>changed</code>
	 * flag of this term is set to <code>true</code>
	 * (can be checked using method <code>hasChanged</code>).
	 * 
	 * The provided equation is supposed to be in normal
	 * form: the substitution rho is distributed through
	 * it and its left-hand side either is a variable or
	 * has the form rho^i(a variable).
	 * 
	 * It is supposed that the substitution rho is
	 * already distributed through this term before
	 * it is reduced. It is also distributed after the
	 * reduction.
	 * 
	 * It is supposed that the <code>changed</code>
	 * flag of this term is set to <code>false</code>.
	 * 
	 * Used in the left-unification decision procedure.
	 * 
	 * @param E a rule (specified as an oriented
	 * equation)
	 * @return the resulting term
	 */
	@Override
	public Term reduceWithAux(LuEquation E) {
		for (int i = 0; i < this.arguments.length; i++) {
			Term t_i = this.arguments[i].reduceWith(E);
			this.changed = this.changed || this.arguments[i].changed;
			this.arguments[i] = t_i;
		}

		return this;
	}

	/**
	 * Applies the specified <code>rho</code> to this
	 * term (which is supposed to be the right-hand
	 * side of an equation) and completes <code>rho</code>
	 * if necessary. The resulting term is this term.
	 * 
	 * Used in the implementation of step 2 of
	 * Alg. A-2.
	 * 
	 * @param rho a substitution to apply to, and
	 * complete from, this term
	 * @return this term
	 */
	@Override
	protected Term applyAndCompleteRho(Substitution rho) {
		for (int i = 0; i < this.arguments.length; i++)
			this.arguments[i] = this.arguments[i].applyAndCompleteRho(rho);

		return this;
	}

	/**
	 * An auxiliary, internal, method which is used to check
	 * whether this term left-unifies with the specified term.
	 * Both this term and the specified term may be modified
	 * by this method.
	 * 
	 * @param hnode a term
	 * @param cost a cost
	 * @param dir a direction (<code>true</code> for
	 * left-to-right, <code>false</code> for right-to-left)
	 * @return <code>true</code> iff this term left-unifies
	 * with <code>t</code> or this term and <code>t</code>
	 * contain a cycle at the end of this method
	 */
	/*
	@Override
	protected boolean propagate(Term hnode, int cost, boolean dir) {
		if (hnode instanceof Function) {
			Function f = (Function) hnode;
			if (this.rootSymbol == f.rootSymbol) {
				for (int i = 0; i < this.arguments.length; i++)
					if (!this.arguments[i].propagate(f.arguments[i], cost, dir))
						return false; 
				return true;
			}
		}
		else if (hnode instanceof Variable)
			return this.addArc(hnode, cost, dir);

		return false;
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

		if (this.arguments.length == 1) {
			// We introduce a slight improvement here.
			// If this term has the form s(t) where s
			// is a unary function symbol and
			// theta(t) = s^{a_1,...,a_l,b)(u)
			// then we return s^{a_1,...,a_l,b+1)(u).
			Term t = this.arguments[0].apply(theta);
			if (t instanceof HatFunction) {
				HatFunction hf = (HatFunction) t;
				if (this.rootSymbol == hf.getRootSymbol().getSimpleContext().getRootSymbol()) {
					HatFunction hf2 = new HatFunction(hf);
					hf2.setB(hf2.getB() + 1);
					return hf2;
				}
			}

			Function f = new Function(this.rootSymbol);
			f.arguments[0] = t;
			return f;
		}

		Function f = new Function(this.rootSymbol);

		int i = 0;
		for (Term t: this.arguments)
			f.arguments[i++] = t.apply(theta);

		return f;
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
		int i = 0;
		for (Term s: this.arguments) {
			if (s instanceof Variable) {
				Term t = theta.get((Variable) s);
				if (t != null) s = t.shallowCopy();
			}
			else s.applyInPlace(theta);
			this.arguments[i++] = s;
		}
	}

	/**
	 * Rewrites this term at inner positions with the
	 * rules of the provided TRS.
	 * 
	 * The returned term is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * Both this term and the provided TRS are not
	 * modified by this method.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param IR a TRS for rewriting this term
	 * @return the collection of terms resulting from
	 * rewriting this term at inner positions
	 */
	@Override
	protected Collection<Term> rewriteAtInnerPositions(Trs IR) {
		// The collection to return at the end.
		Collection<Term> result = new LinkedList<Term>();

		// We rewrite each subterm just below the root.
		for (int i = 0; i < this.arguments.length; i++)
			for (Term u : this.arguments[i].rewriteWith(IR)) {
				// For each rewriting, we create a new term.
				Function f = new Function(this.rootSymbol);
				for (int j = 0; j < f.arguments.length; j++)
					f.arguments[j] = (j == i ? u : this.arguments[j].shallowCopy());
				result.add(f);
			}

		return result;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * unfold this term with the provided rule at the
	 * provided position (specified as an iterator).
	 * 
	 * The specified map is used to store subterm copies
	 * and is constructed incrementally.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative. Moreover, <code>it</code>
	 * is supposed to have a next element.
	 * 
	 * @param R a rule for unfolding this term
	 * @param it an iterator, that has a next element,
	 * over a position where the unfolding takes place
	 * @param dir a boolean indicating whether it is a
	 * backward (when <code>dir==true</code>) or a
	 * forward (when <code>dir==false</code>) unfolding
	 * @param var a boolean indicating whether unfolding
	 * of variable positions is enabled
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
	protected Term unfoldWithAux(RuleTrs R,
			Iterator<Integer> it,
			boolean dir, boolean var,
			Map<Term, Term> copies) {

		// 'it' is supposed to have a next element, hence we can
		// safely write this.
		int i = it.next();

		// Check whether i is out of bounds.
		if (i < 0 || i >= this.arguments.length)
			throw new IndexOutOfBoundsException(i + " -- " + this);

		Function f = new Function(this.rootSymbol);
		int j = 0;
		for (Term s : this.arguments) {
			Term t = (j == i ?
					s.unfoldWith(R, it, dir, var, copies) :
						s.deepCopy(copies));

			if (t == null) return null;

			f.arguments[j++] = t;
		}

		return f;
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
		protected int currentIndex = -1;

		/**
		 * An iterator over the current argument of the iterated function.
		 */
		protected Iterator<Position> it = null;

		/**
		 * Returns <code>true</code> if the iteration has more elements and 
		 * <code>false</code> otherwise.
		 * 
		 * @return <code>true</code> if the iterator has more elements and
		 *   <code>false</code> otherwise
		 */
		@Override
		public boolean hasNext() {
			return currentIndex == -1 ||
					(it == null && currentIndex < arguments.length) ||
					(it != null && (it.hasNext() || currentIndex < arguments.length - 1));
		}

		/**
		 * Returns the next element in the iteration.
		 * 
		 * @return the next element in the iteration
		 * @throws NoSuchElementException when iteration has no more elements
		 */
		@Override
		public Position next() throws NoSuchElementException {
			if (currentIndex == -1) {
				currentIndex = 0;
				return new Position();
			}

			if (currentIndex >= arguments.length)
				throw new NoSuchElementException();

			if (it == null)
				it = arguments[currentIndex].iterator();

			try {
				return it.next().addFirst(currentIndex);
			}
			catch (NoSuchElementException e) {
				currentIndex++;
				it = null;
				return next();
			}
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
	 * 
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
	 * A shallow iterator over the positions of a function.
	 * Such an iterator stops at variable positions: it
	 * does not consider the parent of a variable position.
	 * 
	 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
	 */
	private final class ShallowFunctionIterator extends FunctionIterator {

		/**
		 * Returns the next element in the iteration.
		 * 
		 * @return the next element in the iteration
		 * @throws NoSuchElementException when iteration has no more elements
		 */
		@Override
		public Position next() throws NoSuchElementException {
			if (currentIndex == -1) {
				currentIndex = 0;
				return new Position();
			}

			if (currentIndex >= arguments.length)
				throw new NoSuchElementException();

			if (it == null)
				it = arguments[currentIndex].shallowIterator();

			try {
				return it.next().addFirst(currentIndex);
			}
			catch (NoSuchElementException e) {
				currentIndex++;
				it = null;
				return next();
			}
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
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return the depth of this term
	 */
	@Override
	protected int depthAux() {
		// Constant symbols have depth 0.
		if (this.arguments.length == 0) return 0;

		int d = -1;
		for (Term t: this.arguments) {
			int depth_t = t.depth();
			d = (d <  depth_t ? depth_t : d);
		}
		return 1 + d;
	}

	/**
	 * An auxiliary, internal, method for computing
	 * the maximum arity of a function symbol in
	 * this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return the maximum arity of a function
	 * symbol in this term
	 */
	@Override
	protected int maxArityAux() {

		// The arity of the root symbol of this term.
		int a = this.arguments.length;

		// We compute the max arity by considering
		// the direct subterms of this term.
		for (Term t: this.arguments) {
			int a_t = t.maxArity();
			a = (a <  a_t ? a_t : a);
		}

		return a;
	}

	/**
	 * An auxiliary, internal, method which is used to
	 * check whether this term embeds the specified term
	 * (homeomorphic embedding).
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * Moreover, it is supposed that <code>this != t</code>.
	 * 
	 * @param t the reference term with which to compare
	 * @return <code>true</code> iff this term embeds the
	 * specified term
	 */
	@Override
	protected boolean embedsAux(Term t) {
		boolean embeds = false;

		int n = this.rootSymbol.getArity();

		if (t instanceof Function) {
			Function f = (Function) t;
			if (this.rootSymbol == f.rootSymbol) {
				embeds = true;
				for (int i = 0; i < n && embeds; i++)
					embeds = this.arguments[i].embeds(f.arguments[i]);
			}
		}

		if (!embeds)
			for (int i = 0; i < n && !embeds; i++)
				embeds = this.arguments[i].embeds(t);

		return embeds;
	}

	/**
	 * An internal method which returns
	 * <code>REN(CAP(this term))</code>.
	 * 
	 * See [Arts & Giesl, TCS'00] for a definition
	 * of <code>REN</code> and <code>CAP</code>.
	 * 
	 * Both this term and the specified term are supposed
	 * to be the schemas of their respective class
	 * representatives.
	 * 
	 * @param IR the TRS whose defined symbols are used
	 * for computing the result
	 * @param root a boolean indicating whether the term
	 * at root position has to be replaced with a variable
	 * if its root symbol is defined in <code>IR</code>
	 * @return <code>REN(CAP(this term))</code>
	 */
	@Override
	protected Term rencap(Trs IR, boolean root) {
		if (root && IR.isDefined(this.rootSymbol))
			return new Variable();

		Function f = new Function(this.rootSymbol);

		int i = 0;
		for (Term t : this.arguments)
			f.arguments[i++] = t.findSchema().rencap(IR, true);

		return f;
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing the polynomial corresponding to this term.
	 * It fills the provided <code>Coefficients</code>
	 * with missing coefficients.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param coefficients the coefficients of the polynomials
	 * associated with each function symbol and each tuple symbol
	 * @return the polynomial corresponding to this term
	 */
	@Override
	protected Polynomial toPolynomialAux(PolyInterpretation coefficients) {

		// The number of arguments of the root of this term.
		int n = this.arguments.length;

		// First, we get the coefficients corresponding
		// to the root symbol of this term.
		PolynomialConst[] C = coefficients.get(this.rootSymbol);

		// We also compute the polynomials corresponding
		// to each argument of this term.
		Polynomial P[] = new Polynomial[n];
		for (int i = 0; i < n; i++)
			P[i] = this.arguments[i].toPolynomial(coefficients);

		// The operands of the polynomial that will be returned.
		List<Polynomial> Operands = new LinkedList<Polynomial>();
		// Let us compute each operand. We have to consider all
		// the possible combinations of elements of P. We proceed
		// as explained on this Web page:
		// http://owaisahussain.blogspot.com/2014/03/a-faster-non-recursive-algorithm-to.html
		Operands.add(C[0]);
		for (int i = 1; i < C.length; i++) {
			List<Polynomial> Operand_i = new LinkedList<Polynomial>();
			Operand_i.add(C[i]);
			char[] charArray = Integer.toBinaryString(i).toCharArray();
			int l = charArray.length - 1;
			for (int j = l; 0 <= j; j--)
				if (charArray[j] == '1')
					Operand_i.add(P[l - j]);
			Operands.add(PolynomialComp.getInstance(ArithOperator.TIMES, Operand_i));
		}

		return PolynomialComp.getInstance(ArithOperator.PLUS, Operands);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * generating a weight for each function symbol
	 * and each tuple symbol occurring in this term.
	 * The generated weights are added to the provided
	 * weight function.
	 * 
	 * Used for implementing the Knuth-Bendix order
	 * technique for proving termination of TRSs.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param weights a weight function for storing
	 * the weight of each function symbol and each
	 * tuple symbol occurring in this term
	 */
	@Override
	protected void generateKBOWeightsAux(WeightFunction weights) {
		// If this term's mark is not set to the current time,
		// then this term has not been visited yet. Otherwise,
		// it has already been visited and then we have nothing
		// to do.

		long time = Term.getCurrentTime();
		if (this.mark < time) {
			this.mark = time;

			// First, we add the root symbol of this term
			// to the provided weight function.
			weights.get(this.rootSymbol);

			// Then, we add the symbols occurring in the
			// proper subterms of this term to the provided
			// weight function.
			for (Term t : this.arguments)
				t.findSchema().generateKBOWeightsAux(weights);
		}
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing a tuple version of this term when this
	 * term is a function. If this term is not a function
	 * then this method merely returns this term.
	 * 
	 * Used in the dependency pair framework.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return a tuple version of this term
	 */
	@Override
	protected Term toTupleAux() {
		// The tuple to return at the end.
		Function F = this;

		FunctionSymbol f = this.rootSymbol.toTupleSymbol();
		// If this term is already a tuple, then we merely
		// return this term. Otherwise, we build a tuple
		// version of this term.
		if (this.rootSymbol != f) {
			F = new Function(f);

			for (int i = 0; i < this.rootSymbol.getArity(); i++)
				F.arguments[i] = this.arguments[i];
		}

		return F;
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * computing a function version of this term when
	 * this term is a tuple. If this term is not a tuple
	 * then this method merely returns this term.
	 * 
	 * Used in the dependency pair framework.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @return a function version of this term
	 */
	@Override
	protected Term toFunctionAux() {
		// The function to return at the end.
		Function F = this;

		FunctionSymbol f = this.rootSymbol.toFunctionSymbol();
		// If this term is already a function, then we merely
		// return this term. Otherwise, we build a function
		// version of this term.
		if (this.rootSymbol != f) {
			F = new Function(f);

			for (int i = 0; i < this.rootSymbol.getArity(); i++)
				F.arguments[i] = this.arguments[i];
		}

		return F;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO1) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
			return this.contains((Variable) t);

		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2a) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
		if (t instanceof Function) {
			// We try to set s_i >= t for some i.
			for (Term s_i : this.arguments) {
				// We work on a copy of the specified order, so that
				// the specified order is not modified if everything
				// goes wrong.
				LexOrder O = new LexOrder(order);
				if (s_i.completeLPO(O, t)) {
					order.addAll(O);
					return true;
				}
			}
		}

		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2b) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
		if (t instanceof Function) {
			Function F_t = (Function) t;

			// We work on a copy of the specified order, so that
			// the specified order is not modified if everything
			// goes wrong.
			LexOrder O = new LexOrder(order);

			// We try to add f > g to the copy of the order,
			// where f is the root symbol of this term and g
			// is that of t.
			if (O.add(this.rootSymbol, F_t.rootSymbol)) {
				// If success, we try to set this > t_j for all j.
				for (Term t_j : F_t.arguments)
					if (!this.completeLPOStrict(O, t_j))
						return false;

				// If everything worked, we move the content
				// of the copy to the specified order.
				order.addAll(O);
				return true;
			}
		}

		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (LPO2c) in the definition of a lexicographic path
	 * order (see [Baader & Nipkow, 1998], p. 118) is satisfied.
	 * 
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
		if (t instanceof Function) {
			Function F_t = (Function) t;

			if (this.rootSymbol == F_t.rootSymbol) {
				// We work on a copy of the specified order, so that
				// the specified order is not modified if everything
				// goes wrong.
				LexOrder O = new LexOrder(order);

				// We try to set this > t_j for all j.
				for (Term t_j : F_t.arguments)
					if (!this.completeLPOStrict(O, t_j))
						return false;

				// Let i be such that this_k = t_k for all k < i and
				// this_i != t_i. We try to set this_i > t_i.
				for (int i = 0; i < this.arguments.length; i++) {
					Term s_i = this.arguments[i];
					Term t_i = F_t.arguments[i];
					if (!s_i.deepEquals(t_i))
						if (s_i.completeLPOStrict(O, t_i)) {
							order.addAll(O);
							return true;
						}
						else
							return false;
				}
			}
		}

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used
	 * for computing the weight of this term relatively
	 * to the provided weight function.
	 * 
	 * The weight of a term results from adding up the
	 * weights of all occurrences of symbols in the
	 * term (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
	 * @param weights a weight function
	 * @return the weight of this term relatively
	 * to the provided weight function
	 */
	@Override
	protected Integer getWeightAux(WeightFunction weights) {
		// First, we get the weight of this function's root symbol.
		Integer w1 = weights.get(this.rootSymbol)[0].integerValue(null);

		// Then, we add the weights of the subterms to
		// the weight of the root symbol.
		if (w1 != null) {
			int w = w1.intValue();
			for (Term t : this.arguments) { 
				Integer w2 = t.getWeight(weights);
				if (w2 == null) return null;
				w += w2;
			}

			return w;
		}

		return null;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2a) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
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
		if (this.rootSymbol.getArity() == 1 && t instanceof Variable) {
			Term s = this.arguments[0];
			while (s instanceof Function) {
				Function F_s = (Function) s;
				if (F_s.rootSymbol != this.rootSymbol) return false;
				s = F_s.arguments[0];
			}

			return (s == t);
		}

		return false;
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2b) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
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
		return t instanceof Function &&
				order.add(this.rootSymbol, ((Function) t).rootSymbol);
	}

	/**
	 * Completes the specified partial order on function symbols
	 * so that (KBO2c) in the definition of a Knuth-Bendix order
	 * is satisfied (see p. 124 of [Baader & Nipkow, 1998]).
	 * 
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
		if (t instanceof Function) {
			Function F_t = (Function) t;

			if (this.rootSymbol == F_t.rootSymbol) {
				// We work on a copy of the specified order, so that
				// the specified order is not modified if everything
				// goes wrong.
				LexOrder O = new LexOrder(order);

				// Let i be such that this_k = t_k for all k < i and
				// this_i != t_i. We try to set this_i > t_i.
				for (int i = 0; i < this.arguments.length; i++) {
					Term s_i = this.arguments[i];
					Term t_i = F_t.arguments[i];
					if (!s_i.deepEquals(t_i))
						if (s_i.completeKBOStrict(O, weights, t_i)) {
							order.addAll(O);
							return true;
						}
						else
							return false;
				}
			}
		}

		return false;
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * building empty filters for the function and tuple
	 * symbols occurring in this term.
	 * 
	 * This term is supposed to be the schema of its
	 * class representative.
	 * 
	 * @param filtering the data structure to complete
	 * with the filters built from this term
	 */
	@Override
	protected void buildFiltersAux(ArgFiltering filtering) {
		filtering.add(this.rootSymbol);

		for (Term t : this.arguments)
			t.buildFilters(filtering);
	}

	/**
	 * An auxiliary, internal, method which is used for
	 * applying the specified argument filtering to this
	 * term.
	 * 
	 * This term is not modified by this method.
	 * 
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

		if (filter != null) {
			Integer I = filter.getIntValue();
			if (I != null)
				return this.arguments[I].applyFilters(filtering);

			List<Integer> L = filter.getListValue();
			if (L != null) {
				List<Term> Args = new LinkedList<Term>();
				for (Integer i : L)
					Args.add(this.arguments[i].applyFilters(filtering));
				FunctionSymbol g = FunctionSymbol.getInstance(
						this.rootSymbol.getName(), Args.size());
				if (this.rootSymbol.isTupleSymbol())
					g = g.toTupleSymbol();
				return new Function(g, Args);	
			}
		}

		return this;
	}

	/**
	 * Computes a substitution form of this term.
	 * 
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
	 * 
	 * This term is not modified by this method.
	 * 
	 * Moreover, at the end of this method
	 * <code>s theta</code> is equal to this term.
	 * 
	 * @param theta a substitution
	 * @return the term resulting from replacing
	 * subterms of this term by new variables
	 */
	public Term toSubstitution(Substitution theta) {
		// The term to return at the end.
		Function f = new Function(this.rootSymbol);

		int i = 0;
		for (Term t : this.arguments) {
			Term new_t = t;
			if (t.isGround()) {
				Variable x = new Variable();
				theta.add(x, t);
				new_t = x;
			}
			f.arguments[i++] = new_t;
		}

		return f;
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
	protected String toStringAux(Map<Variable, String> variables, boolean shallow) {
		StringBuffer s = new StringBuffer(this.rootSymbol.toString());
		int l = this.arguments.length;

		if (l > 0) {
			s.append("(");
			for (Term t: this.arguments) {
				s.append(t.toString(variables, shallow));
				if (0 < --l) s.append(",");
			}
			s.append(")");
		}

		return s.toString();
	}
}
