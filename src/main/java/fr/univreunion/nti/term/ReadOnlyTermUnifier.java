/*
 * Copyright 2026 Etienne Payet <etiennepayet at univ-reunion.fr>
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

import java.util.Arrays;
import java.util.NoSuchElementException;

/**
 * Checks unifiability without modifying or copying its terms.
 * <p>
 * One instance is reusable for several targets of the same source term. Its
 * local bindings are separated by generation and its work queues are cleared
 * between tests.
 * <p>
 * The objects of this class are mutable and not thread safe.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class ReadOnlyTermUnifier {

	/** The source term shared by all tests performed by this instance. */
	private final Term source;

	/** The generation-stamped local variable bindings. */
	private final IdentityBindings bindings = new IdentityBindings();

	/** The left sides of the equations that remain to process. */
	private final TermQueue leftTerms = new TermQueue();

	/** The right sides of the equations that remain to process. */
	private final TermQueue rightTerms = new TermQueue();

	/** Work queue used by the occurs check. */
	private final TermQueue occursTerms;

	/** Whether equations for fresh linear source variables can be discarded. */
	private final boolean discardSourceVariables;

	/**
	 * Builds a reusable unifier for the specified source term.
	 *
	 * @param source the source term
	 */
	public ReadOnlyTermUnifier(Term source) {
		this(source, true);
	}

	/**
	 * Builds a reusable unifier for a fresh linear source whose variables are
	 * disjoint from every target. Under these conditions, unification is not
	 * subject to the occurs check. The caller is responsible for establishing
	 * both conditions.
	 *
	 * @param source the fresh linear source term
	 * @return an unifier which omits occurs checks and dead source bindings
	 */
	public static ReadOnlyTermUnifier forFreshLinearSource(Term source) {
		return new ReadOnlyTermUnifier(source, false);
	}

	/**
	 * Builds a reusable unifier for the specified source term.
	 *
	 * @param source the source term
	 * @param checkOccurrences whether variable bindings require occurs checks
	 */
	private ReadOnlyTermUnifier(Term source, boolean checkOccurrences) {
		this.source = source;
		this.occursTerms = checkOccurrences ? new TermQueue() : null;
		this.discardSourceVariables = !checkOccurrences;
	}

	/**
	 * Returns <code>true</code> iff the source and target terms are unifiable.
	 * Neither term is modified by this method.
	 *
	 * @param target the target term
	 * @return <code>true</code> iff the source and target terms are unifiable
	 */
	public boolean isUnifiableWith(Term target) {
		this.bindings.startGeneration();
		this.leftTerms.reset();
		this.rightTerms.reset();
		this.leftTerms.addLast(this.source);
		this.rightTerms.addLast(target);

		while (this.leftTerms.hasTerms())
			if (!this.unifyNextEquation())
				return false;

		return true;
	}

	/**
	 * Processes the next equation in the work queues.
	 *
	 * @return <code>true</code> iff the next equation is unifiable
	 */
	private boolean unifyNextEquation() {
		Term left = this.leftTerms.removeFirst();
		Term right = this.rightTerms.removeFirst();

		// A fresh linear source variable occurs in no other equation. Since this
		// unifier returns no substitution, its sole binding is dead.
		if (this.discardSourceVariables && left instanceof Variable)
			return true;

		left = this.dereference(left);
		right = this.dereference(right);

		if (left == right)
			return true;
		if (left instanceof Variable leftVariable)
			return this.bindIfAcyclic(leftVariable, right);
		if (right instanceof Variable rightVariable)
			return this.bindIfAcyclic(rightVariable, left);
		if (left instanceof Function leftFunction &&
				right instanceof Function rightFunction)
			return this.decompose(leftFunction, rightFunction);
		return false;
	}

	/**
	 * Adds an acyclic variable binding to the current local substitution.
	 *
	 * @param variable the variable to bind
	 * @param term the term to bind to the variable
	 * @return <code>true</code> iff the binding is acyclic and was added
	 */
	private boolean bindIfAcyclic(Variable variable, Term term) {
		if (this.occursTerms != null && this.occurs(variable, term))
			return false;
		this.bindings.put(variable, term);
		return true;
	}

	/**
	 * Adds corresponding function arguments to the equation queues.
	 *
	 * @param left the left function of the equation
	 * @param right the right function of the equation
	 * @return <code>true</code> iff the functions have the same root symbol
	 */
	private boolean decompose(Function left, Function right) {
		if (left.getRootSymbol() != right.getRootSymbol())
			return false;

		int arity = left.getRootSymbol().getArity();
		for (int argumentIndex = 0; argumentIndex < arity; argumentIndex++) {
			this.leftTerms.addLast(left.getChild(argumentIndex));
			this.rightTerms.addLast(right.getChild(argumentIndex));
		}
		return true;
	}

	/**
	 * Returns the term reached by following the current variable bindings.
	 *
	 * @param term the term to dereference
	 * @return the dereferenced term
	 */
	private Term dereference(Term term) {
		Term result = term;
		while (result instanceof Variable variable) {
			Term binding = this.bindings.get(variable);
			if (binding == null)
				break;
			result = binding;
		}
		return result;
	}

	/**
	 * Returns whether the specified variable occurs in the dereferenced term.
	 *
	 * @param variable the variable to find
	 * @param term the term to inspect
	 * @return <code>true</code> iff the variable occurs in the dereferenced term
	 */
	private boolean occurs(Variable variable, Term term) {
		this.occursTerms.reset();
		this.occursTerms.addLast(term);

		while (this.occursTerms.hasTerms()) {
			Term subterm = this.dereference(this.occursTerms.removeFirst());
			if (subterm == variable)
				return true;
			if (subterm instanceof Function function) {
				int arity = function.getRootSymbol().getArity();
				for (int argumentIndex = 0;
					 argumentIndex < arity;
					 argumentIndex++)
					this.occursTerms.addLast(function.getChild(argumentIndex));
			}
		}

		return false;
	}

	/**
	 * Reusable circular FIFO queue. Resetting a queue is constant-time and old
	 * slots are overwritten lazily, so its retained references and capacity are
	 * bounded by the largest live queue.
	 */
	private static final class TermQueue {

		/** Initial power-of-two queue capacity. */
		private static final int INITIAL_CAPACITY = 16;

		/** Terms stored in circular FIFO order. */
		private Term[] elements = new Term[INITIAL_CAPACITY];

		/** Index of the first live term. */
		private int head;

		/** Number of live terms. */
		private int size;

		/** Resets this queue without clearing its backing array. */
		private void reset() {
			this.head = 0;
			this.size = 0;
		}

		/**
		 * Returns whether this queue contains at least one live term.
		 *
		 * @return <code>true</code> iff this queue contains a live term
		 */
		private boolean hasTerms() {
			return this.size > 0;
		}

		/**
		 * Adds a term at the end of this queue.
		 *
		 * @param term the term to add
		 */
		private void addLast(Term term) {
			if (this.size == this.elements.length)
				this.grow();
			int tail = (this.head + this.size) & (this.elements.length - 1);
			this.elements[tail] = term;
			this.size++;
		}

		/**
		 * Removes and returns the first term of this queue.
		 *
		 * @return the first term
		 * @throws NoSuchElementException if this queue is empty
		 */
		private Term removeFirst() {
			if (this.size == 0)
				throw new NoSuchElementException("empty term queue");
			Term first = this.elements[this.head];
			this.head = (this.head + 1) & (this.elements.length - 1);
			this.size--;
			return first;
		}

		/** Doubles the backing array while preserving FIFO order. */
		private void grow() {
			Term[] previousElements = this.elements;
			int capacity = Math.multiplyExact(previousElements.length, 2);
			this.elements = new Term[capacity];

			int suffixLength = Math.min(
					this.size, previousElements.length - this.head);
			System.arraycopy(
					previousElements, this.head,
					this.elements, 0,
					suffixLength);
			System.arraycopy(
					previousElements, 0,
					this.elements, suffixLength,
					this.size - suffixLength);
			this.head = 0;
		}
	}

	/**
	 * Identity-based bindings whose old entries become logically empty when a
	 * new generation starts. Stale slots are reused during insertion, so the
	 * table is bounded by the largest individual unification rather than by the
	 * number of targets tested.
	 */
	private static final class IdentityBindings {

		/** Initial power-of-two table capacity. */
		private static final int INITIAL_CAPACITY = 16;

		/** Variables stored in the open-addressed table. */
		private Variable[] variables = new Variable[INITIAL_CAPACITY];

		/** Terms paired with the stored variables. */
		private Term[] terms = new Term[INITIAL_CAPACITY];

		/** Generation in which each table slot was written. */
		private int[] slotGenerations = new int[INITIAL_CAPACITY];

		/** The current nonzero generation. */
		private int generation;

		/** The number of bindings in the current generation. */
		private int size;

		/** Maximum current-generation size before the table grows. */
		private int resizeThreshold = resizeThreshold(INITIAL_CAPACITY);

		/** Starts with a logically empty table without clearing its entries. */
		private void startGeneration() {
			if (this.generation == Integer.MAX_VALUE) {
				Arrays.fill(this.slotGenerations, 0);
				this.generation = 1;
			}
			else
				this.generation++;
			this.size = 0;
		}

		/**
		 * Returns the current binding of the specified variable, if any.
		 *
		 * @param variable the variable whose binding is requested
		 * @return the current binding, or <code>null</code> if none exists
		 */
		private Term get(Variable variable) {
			int tableMask = this.variables.length - 1;
			int slot = slotFor(variable, tableMask);
			while (this.slotGenerations[slot] == this.generation) {
				if (this.variables[slot] == variable)
					return this.terms[slot];
				slot = (slot + 1) & tableMask;
			}
			return null;
		}

		/**
		 * Adds or replaces a binding in the current generation.
		 *
		 * @param variable the variable to bind
		 * @param term the term to bind to the variable
		 */
		private void put(Variable variable, Term term) {
			int tableMask = this.variables.length - 1;
			int slot = slotFor(variable, tableMask);
			while (this.slotGenerations[slot] == this.generation) {
				if (this.variables[slot] == variable) {
					this.terms[slot] = term;
					return;
				}
				slot = (slot + 1) & tableMask;
			}

			if (this.size == this.resizeThreshold) {
				this.grow();
				this.put(variable, term);
				return;
			}

			this.variables[slot] = variable;
			this.terms[slot] = term;
			this.slotGenerations[slot] = this.generation;
			this.size++;
		}

		/** Doubles the table and retains only current-generation bindings. */
		private void grow() {
			Variable[] previousVariables = this.variables;
			Term[] previousTerms = this.terms;
			int[] previousGenerations = this.slotGenerations;

			int capacity = Math.multiplyExact(previousVariables.length, 2);
			this.variables = new Variable[capacity];
			this.terms = new Term[capacity];
			this.slotGenerations = new int[capacity];
			this.resizeThreshold = resizeThreshold(capacity);
			this.size = 0;

			for (int slot = 0; slot < previousVariables.length; slot++)
				if (previousGenerations[slot] == this.generation)
					this.insertRetained(
							previousVariables[slot], previousTerms[slot]);
		}

		/**
		 * Inserts one retained binding into an empty-enough grown table.
		 *
		 * @param variable the retained variable
		 * @param term the retained term bound to the variable
		 */
		private void insertRetained(Variable variable, Term term) {
			int tableMask = this.variables.length - 1;
			int slot = slotFor(variable, tableMask);
			while (this.slotGenerations[slot] == this.generation)
				slot = (slot + 1) & tableMask;

			this.variables[slot] = variable;
			this.terms[slot] = term;
			this.slotGenerations[slot] = this.generation;
			this.size++;
		}

		/**
		 * Returns the first candidate slot for an identity key.
		 *
		 * @param variable the identity key
		 * @param tableMask the table-length mask
		 * @return the first candidate slot
		 */
		private static int slotFor(Variable variable, int tableMask) {
			int hash = System.identityHashCode(variable);
			return (hash ^ (hash >>> 16)) & tableMask;
		}

		/**
		 * Returns the two-thirds load threshold for a capacity.
		 *
		 * @param capacity the table capacity
		 * @return the corresponding resize threshold
		 */
		private static int resizeThreshold(int capacity) {
			return capacity - capacity / 3;
		}
	}
}
