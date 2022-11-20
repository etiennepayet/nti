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

package fr.univreunion.nti;

import java.util.LinkedList;

import fr.univreunion.nti.program.trs.polynomial.CoefficientInstantiator;
import fr.univreunion.nti.program.trs.polynomial.Intervals;
import fr.univreunion.nti.program.trs.polynomial.PolynomialConst;

public class Main {

	public static void main(String args[]) {
		PolynomialConst.resetIDs();
		
		PolynomialConst c1 = new PolynomialConst();
		PolynomialConst c2 = new PolynomialConst();
		PolynomialConst c3 = new PolynomialConst();

		LinkedList<PolynomialConst> l = new LinkedList<PolynomialConst>();
		l.add(c1); l.add(c2); l.add(c3);

		Intervals intervals = new Intervals();
		intervals.putMin(c2, 1);
		intervals.putMax(c2, 10);
		intervals.putMax(c3, 1);

		if (intervals.putMin(c2, 2)) {
			
			System.out.println("# Intervals = " + intervals);

			CoefficientInstantiator it = new CoefficientInstantiator(l, intervals, 2);
			
			System.out.println("# Nb inst = " + it.getNbInstantiationPossibilities());

			while (it.hasNext()) {
				it.next();
				System.out.println(it);
			}
		}
		else 
			System.out.println("Unsatisfiable");
	}
	
}
