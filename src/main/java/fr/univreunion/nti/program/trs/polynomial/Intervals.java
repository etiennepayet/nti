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

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

/**
 * A mapping from coefficients of polynomials
 * to intervals of integer values used for
 * instantiation.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Intervals {

	/**
	 * The lower limits of the intervals of values.
	 */
	private final Map<PolynomialConst, Integer> minvals = new HashMap<PolynomialConst, Integer>();

	/**
	 * The upper limits of the intervals of values.
	 */
	private final Map<PolynomialConst, Integer> maxvals = new HashMap<PolynomialConst, Integer>();

	/**
	 * Returns the lower limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>null</code> if no lower limit
	 * exists.
	 * 
	 * @param c a coefficient of a polynomial
	 * @return the lower limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>null</code> if no lower limit
	 * exists
	 */
	public Integer getMin(PolynomialConst c) {
		return this.minvals.get(c);
	}

	/**
	 * Returns the lower limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>defaultValue</code> if no lower
	 * limit exists.
	 * 
	 * @param c a coefficient of a polynomial
	 * @return the lower limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>defaultValue</code> if no lower
	 * limit exists
	 */
	public Integer getMinOrDefault(PolynomialConst c, Integer defaultValue) {
		return this.minvals.getOrDefault(c, defaultValue);
	}

	/**
	 * Returns the upper limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>null</code> if no upper limit
	 * exists.
	 * 
	 * @param c a coefficient of a polynomial
	 * @return the upper limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>null</code> if no upper limit
	 * exists
	 */
	public Integer getMax(PolynomialConst c) {
		return this.maxvals.get(c);
	}

	/**
	 * Returns the upper limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>defaultValue</code> if no upper
	 * limit exists.
	 * 
	 * @param c a coefficient of a polynomial
	 * @return the upper limit of the interval 
	 * associated with the specified coefficient,
	 * or <code>defaultValue</code> if no upper
	 * limit exists
	 */
	public Integer getMaxOrDefault(PolynomialConst c, Integer defaultValue) {
		return this.maxvals.getOrDefault(c, defaultValue);
	}

	/**
	 * Associates the specified lower limit <code>i</code>
	 * with the specified coefficient <code>c</code>.
	 * 
	 * If there is already a lower limit for <code>c</code>,
	 * then the value that minimizes the size of the interval
	 * associated with <code>c</code> is chosen.
	 * 
	 * If there is already an upper limit <code>max</code>
	 * for <code>c</code> with <code>max &lt; i</code>,
	 * then this operation fails, i.e., this interval is
	 * not modified and <code>false</code> is returned.
	 * 
	 * @param c a coefficient of a polynomial
	 * @param i a lower limit
	 * @return <code>true</code> iff this operation succeeds
	 */
	public boolean putMin(PolynomialConst c, Integer i) {
		Integer min = this.minvals.get(c);
		Integer max = this.maxvals.get(c);

		if (min == null && max == null) {
			this.minvals.put(c, i);
			return true;
		}

		// From here, min != null or max != null.

		if (min == null) {
			// Here, max != null.
			if (i <= max) {
				this.minvals.put(c, i);
				return true;
			}
			// Here, i > max.
			return false;
		}

		// From here, min != null.

		// The new min we want to insert reduces
		// the size of the interval corresponding
		// to c.
		i = Math.max(min, i);

		if (max == null || i <= max) {
			this.minvals.put(c, i);
			return true;
		}

		// From here, max != null and i > max.
		return false;
	}

	/**
	 * Associates the specified upper limit <code>i</code>
	 * with the specified coefficient <code>c</code>.
	 * 
	 * If there is already an upper limit for <code>c</code>,
	 * then the value that minimizes the size of the interval
	 * associated with <code>c</code> is chosen.
	 * 
	 * If there is already a lower limit <code>min</code>
	 * for <code>c</code> with <code>min &gt; i</code>,
	 * then this operation fails, i.e., this interval is
	 * not modified and <code>false</code> is returned.
	 * 
	 * @param c a coefficient of a polynomial
	 * @param i an upper limit
	 * @return <code>true</code> iff this operation succeeds
	 */
	public boolean putMax(PolynomialConst c, Integer i) {
		Integer min = this.minvals.get(c);
		Integer max = this.maxvals.get(c);

		if (min == null && max == null) {
			this.maxvals.put(c, i);
			return true;
		}

		// From here, min != null or max != null.

		if (max == null) {
			// Here, min != null.
			if (min <= i) {
				this.maxvals.put(c, i);
				return true;
			}
			// Here, min > i.
			return false;
		}

		// From here, max != null.

		// The new max we want to insert reduces
		// the size of the interval corresponding
		// to c.
		i = Math.min(max, i);

		if (min == null || min <= i) {
			this.maxvals.put(c, i);
			return true;
		}

		// From here, min != null and min > i.
		return false;
	}

	/**
	 * Returns a string representation of this object.
	 * 
	 * @return a string representation of this object
	 */
	@Override
	public String toString() {
		StringBuffer s1 = new StringBuffer();

		boolean first = true;
		
		for (Entry<PolynomialConst, Integer> e : this.minvals.entrySet()) {
			PolynomialConst c = e.getKey();
			
			if (first) first = false;
			else s1.append(", ");
			
			s1.append(e.getValue() + " <= " + c);
			
			Integer max = this.maxvals.get(c);
			if (max != null) s1.append(" <= " + max);
		}
		
		StringBuffer s2 = new StringBuffer();

		first = true;

		for (Entry<PolynomialConst, Integer> e : this.maxvals.entrySet()) {
			PolynomialConst c = e.getKey();
			
			if (this.minvals.get(c) == null) {
				if (first) first = false;
				else s1.append(", ");
				
				s2.append(c + " <= " + e.getValue());
			}
		}
		
		if (0 < s1.length() && 0 < s2.length()) s1.append(", ");
		s1.append(s2);
		s1.append("]");

		return "[" + s1.toString();
	}
}
