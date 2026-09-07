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

package fr.univreunion.nti.program.trs.argfiltering;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.NoSuchElementException;

/**
 * A class used for instantiating filters for function symbols.
 * For each function symbol <code>f/n</code>, it only generates,
 * in order, the argument filterings <code>pi(f)=[i]</code>,
 * for all <code>1 &le; i &le; n</code>, and the full argument
 * filtering <code>pi(f)=[1,...,n]</code>.
 * Moreover, <b>it does not generate the argument filtering
 * which is such that <code>pi(f)=[1,...,n]</code> for all
 * <code>f/n</code></b>.
 * <p>
 * NB: we do not implement the <em>some</em> heuristic presented by
 * N. Hirokawa and A. Middeldorp in
 * <a href="https://doi.org/10.1007/978-3-540-45085-6_4"><i>Automating the
 * Dependency Pair Method</i></a>, CADE 2003, LNAI 2741, pp. 32--46, because
 * it does not solve AG01/#3.1, Example 2 of T. Arts and J. Giesl,
 * <a href="https://doi.org/10.1016/S0304-3975(99)00207-8"><i>Termination of
 * Term Rewriting Using Dependency Pairs</i></a>, Theoretical Computer Science
 * 236(1--2), pp. 133--178, 2000.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class FilterInstantiator {

	/**
	 * The filters to instantiate.
	 */
	private final ArrayList<Filter> filters;

	/**
	 * An array that will contain all the possible
	 * values for each filter: values[i] is the
	 * current value for filters[i].
	 */
	private final int[] values;

	/**
	 * The total number of instantiations that
	 * this object will produce.
	 */
	private final int nbInstantiationPossibilities;

	/**
	 * An integer used for stopping this instantiator.
	 * It corresponds to the number of remaining
	 * instantiation possibilities.
	 */
	private int nb;


	/**
	 * Builds an instantiator on the provided filters.
	 * 
	 * @param filters the filters to instantiate
	 */
	public FilterInstantiator(Collection<Filter> filters) {

		this.filters = new ArrayList<>(filters.size());
		
		// We insert the filters into this object, in
		// ascending order. We do this for ensuring
		// determinism, because 'filters' may come
		// from the entry set of a map, see method
		// 'getAllFilters' in class 'ArgFiltering'.
		for (Filter filter : filters) {
			int insertionIndex = 0;
			for (Filter storedFilter : this.filters) {
				if (filter.getSymbol().lt(storedFilter.getSymbol())) break;
				insertionIndex++;
			}
			this.filters.add(insertionIndex, filter);
		}

		// We set the array that will contain all the
		// possible values for each filter.
		this.values = new int[filters.size()];

		// We compute the total number of instantiations
		// that this object will produce.
		int possibilityCount = 1;
		for (Filter filter : this.filters) 
			try {
				int arity = filter.getSymbol().getArity();
				// For symbols of arity 1, there is only 1
				// instantiation, i.e., [0]. For the other
				// symbols, there are (arity + 1).
				possibilityCount = Math.multiplyExact(
						possibilityCount, (arity == 1 ? 1 : arity + 1));
			} catch (ArithmeticException ignored) {
				possibilityCount = Integer.MAX_VALUE;
				break;
			}
		// We do not consider the instantiation of all
		// the filters to their full list of argument
		// indices. Hence, we subtract 1 from the computed
		// value.
		this.nbInstantiationPossibilities = possibilityCount - 1;

		// Finally, we set the initial value of the
		// variable used for stopping this instantiator.
		this.nb = this.nbInstantiationPossibilities;
	}

	/**
	 * Returns <code>true</code> iff this instantiator
	 * has a next instantiation to deliver.
	 */
	public boolean hasNext() {
		return this.nb != 0;
	}

	/**
	 * Computes a new instantiation of the filters
	 * and points to the next one. 
	 */
	public void next() {
		if (!this.hasNext())
			throw new NoSuchElementException(
					"No values left for instantiation.");

		this.loadNewInstantiation();
		this.incrementValues();
	}

	/**
	 * Instantiates the filters with the current values.
	 */
	protected void loadNewInstantiation() {

		int filterIndex = 0;

		for (Filter filter : this.filters) {

			// The arity of the function symbol of 'filter'.
			int arity = filter.getSymbol().getArity();
			List<Integer> positions = new ArrayList<>();

			if (arity <= this.values[filterIndex]) {
				// We generate the list [0,...,n-1].
				for (int j = 0; j < arity; j++) positions.add(j);
			}
			// We do not implement the 'some' heuristic presented in
			// [Hirokawa & Middeldorp, CADE'03] because it does not
			// solve AG01/#3.1 (example 2 of [Arts & Giesl, TCS'00]).
			// Therefore, a non-full instantiation keeps only the
			// selected argument.
			else
				positions.add(this.values[filterIndex]);

			filter.setValue(positions);
			filterIndex++;
		}
	}

	/**
	 * Points to the next instantiation.
	 */
	protected void incrementValues() {

		// We compute the next instantiation 
		// only if there are others left.
		if (0 < this.nb) {
			for (int filterIndex = this.values.length - 1;
					filterIndex >= 0; --filterIndex) {
				// The arity of the function symbol of the i-th filter.
				int arity = this.filters.get(filterIndex).getSymbol().getArity();

				// For symbols of arity 1, there is only 1 instantiation,
				// i.e., [0]. Hence, if i refers to a symbol of arity 1,
				// then this.values[i] can only contain 0.
				if (1 < arity && this.values[filterIndex] < arity) {
					this.values[filterIndex]++;

					this.resetValues(filterIndex + 1);

					// We have produced a new instantiation,
					// hence we reduce the number of remaining
					// possibilities.
					this.nb--;

					return;
				}
			}

			// If we get there, then there are no more
			// instantiations left. This is useful when
			// nb has been initialized to a value that 
			// is greater than the total number of
			// instantiations that are produced.
			this.nb = 0;
		}
	}

	/**
	 * Resets the array of values from the provided
	 * start index to the end of the array.
	 * <p>
	 * For internal use only.
	 * 
	 * @param start the index from which the values
	 * have to be reset
	 */
	protected void resetValues(int start) {
		for (int i = start; i < this.values.length; i++)
			this.values[i] = 0;
	}

	/**
	 * Returns the total number of instantiations that
	 * this object will produce.
	 * <p>
	 * If the total number of instantiations is greater
	 * than <code>Integer.MAX_VALUE</code> (the maximum
	 * value an <code>int</code> can have), then this
	 * method returns <code>Integer.MAX_VALUE</code>.
	 * 
	 * @return the total number of instantiations that
	 * this object will produce or
	 * <code>Integer.MAX_VALUE</code>
	 */
	public int getNbInstantiationPossibilities() {
		return this.nbInstantiationPossibilities;
	}
}
