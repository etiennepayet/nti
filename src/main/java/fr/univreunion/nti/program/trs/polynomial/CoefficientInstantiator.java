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

package fr.univreunion.nti.program.trs.polynomial;

import java.util.ArrayList;
import java.util.Collection;
import java.util.NoSuchElementException;

/**
 * A class used for instantiating coefficients of polynomials with
 * values in <code>{0,1,...,n}</code>, where <code>n</code> is an
 * integer that has to be specified.
 * 
 * Inspired from a solution given on 
 * <A HREF="https://codereview.stackexchange.com/questions/177317/algorithm-that-generate-all-possible-strings-from-n-tuples-found-brute-force-ve">
 * this web page</A>
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class CoefficientInstantiator {

	/**
	 * The intervals of values that have to be used
	 * for instantiating some coefficient.
	 */
	private final Intervals intervals = new Intervals();

	/**
	 * The coefficients to instantiate, sorted in
	 * ascending order of identifiers.
	 */
	private final ArrayList<PolynomialConst> coefficients = new ArrayList<PolynomialConst>();

	/**
	 * The total number of instantiations that
	 * this object will produce.
	 */
	private final int nbInstantiationPossibilities;

	/**
	 * An array that contains the current value of
	 * each coefficient: values[i] is the current
	 * value for coefficients[i].
	 */
	private final int[] values; 

	/**
	 * A boolean used for stopping this instantiator.
	 */
	private boolean stop; // Default value = false.

	/**
	 * Builds an instantiator on the provided coefficients.
	 * 
	 * @param coefficients the coefficients to instantiate
	 * @param intervals the intervals of values used for
	 * instantiating some coefficients
	 * @param maxval the maximum value that is allowed for
	 * instantiating the coefficients
	 */
	public CoefficientInstantiator(Collection<PolynomialConst> coefficients,
			Intervals intervals, int maxval) {

		// We insert the coefficients into this object, in
		// ascending order of identifiers. We do this to
		// ensure determinism, because 'coefficients' may
		// come from the entry set of a map, see method
		// 'getAllCoefficients' in class 'PolyInterpretation'.
		// We also fill the structure that stores the intervals
		// of values associated with the coefficients. Moreover,
		// we compute the total number of instantiations that
		// this object will produce.
		int n = 1;
		for (PolynomialConst c : coefficients) {
			// First, we insert c at the right position.
			int i = 0;
			for (PolynomialConst cc : this.coefficients) {
				if (c.getID() < cc.getID()) break;
				i++;
			}
			this.coefficients.add(i, c);

			// Then, we insert the upper and lower limits
			// associated with c.
			//
			// We get the upper limit associated with c.
			int max_c = intervals.getMaxOrDefault(c, maxval);
			// If it is greater than the maximum value
			// that is allowed for instantiating the
			// coefficients, then we fix it.
			if (max_c > maxval) max_c = maxval;
			this.intervals.putMax(c, max_c);
			//
			// We get the lower limit associated with c.
			int min_c = intervals.getMinOrDefault(c, 0);
			// If it is less than 0, then we fix it.
			if (min_c < 0) min_c = 0;
			this.intervals.putMin(c, min_c);

			// Finally, we update the current number of
			// instantiations.
			try {
				// The size of the interval associated with c
				// is 1 + max_c - min_c.
				n = Math.multiplyExact(n, 1 + max_c - min_c);
			} catch (ArithmeticException e) {
				n = Integer.MAX_VALUE;
			}
		}
		this.nbInstantiationPossibilities = n;

		this.values = new int[this.coefficients.size()];
		this.resetValues(0);
	}

	/**
	 * Returns <code>true</code> iff this instantiator
	 * has a next instantiation to deliver.
	 */
	public boolean hasNext() {
		return !this.stop;
	}

	/**
	 * Computes a new instantiation of the coefficients
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
	 * Instantiates the coefficients with the current values.
	 */
	private void loadNewInstantiation() {
		int i = 0;
		for (PolynomialConst C : this.coefficients)
			C.setValue(this.values[i++]);
	}

	/**
	 * Points to the next instantiation.
	 */
	private void incrementValues() {
		for (int i = this.values.length - 1; i >= 0; --i)
			if (this.values[i] < this.intervals.getMax(this.coefficients.get(i))) {
				this.values[i]++;

				this.resetValues(i + 1);

				return;
			}

		this.stop = true;
	}

	/**
	 * Resets the array of values from the provided
	 * start index to the end of the array.
	 * 
	 * For internal use only.
	 * 
	 * @param start the index from which the values
	 * have to be reset
	 */
	protected void resetValues(int start) {
		for (int i = start; i < this.values.length; i++)
			this.values[i] = this.intervals.getMin(this.coefficients.get(i));
	}

	/**
	 * Resets this instantiator, i.e., sets it
	 * to its initial state.
	 */
	public void reset() {
		this.stop = false;
		this.resetValues(0);
	}

	/**
	 * Returns the total number of instantiations that
	 * this object will produce.
	 * 
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

	/**
	 * Returns a String representation of the current
	 * instantiation provided by this instantiator.
	 * 
	 * @return a String representation of the current
	 * instantiation provided by this instantiator
	 */
	@Override
	public String toString() {
		return this.coefficients.toString();
	}
}
