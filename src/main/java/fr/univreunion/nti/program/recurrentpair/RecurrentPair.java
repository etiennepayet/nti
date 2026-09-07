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

package fr.univreunion.nti.program.recurrentpair;

import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.Term;

/**
 * A recurrent pair for proving the existence of a binary chain, as defined
 * in Sect. 5 of E. Payet,
 * <a href="https://doi.org/10.1007/s10817-023-09693-z"><i>Non-Termination
 * in Term Rewriting and Logic Programming</i></a>, Journal of Automated
 * Reasoning 68, article 4, 2024.
 *
 * <p>The accepted form also includes the extension of E. Payet,
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10"><i>Recurrent Pairs
 * Revisited</i></a>, LOPSTR 2025, LNCS 16117, pp. 154--164, 2026.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class RecurrentPair {

	/**
	 * The components of this recurrent-pair certificate.
	 */
	private final RecurrentPairData data;


	/**
	 * Tries to build a recurrent pair from the provided elements.
	 * <p>
	 * If a recurrent pair cannot be built then
	 * <code>null</code> is returned.
	 *
	 * @param u1 the lhs of the first  finite chain
	 * @param v1 the rhs of the first  finite chain
	 * @param u2 the lhs of the second finite chain
	 * @param v2 the rhs of the second finite chain
	 * @return a recurrent pair, or <code>null</code>
	 */
	public static synchronized RecurrentPair tryBuild(
			Function u1, Term v1, Function u2, Term v2) {

		return RecurrentPairBuilder.tryBuild(u1, v1, u2, v2);
	}

	/**
	 * Builds a recurrent pair from the provided certificate components.
	 *
	 * @param data the components of this recurrent-pair certificate
	 */
	RecurrentPair(RecurrentPairData data) {
		this.data = data;
	}

	/**
	 * Returns the components of this recurrent-pair certificate.
	 */
	RecurrentPairData data() {
		return this.data;
	}

	/**
	 * Returns the left-hand side of the first
	 * finite chain of this recurrent pair.
	 */
	public Function getLeft1() {
		return this.data.u1();
	}

	/**
	 * Returns the right-hand side of the first
	 * finite chain of this recurrent pair.
	 */
	public Function getRight1() {
		return this.data.v1();
	}

	/**
	 * Returns the left-hand side of the second
	 * finite chain of this recurrent pair.
	 */
	public Function getLeft2() {
		return this.data.u2();
	}

	/**
	 * Returns the right-hand side of the second
	 * finite chain of this recurrent pair.
	 */
	public Function getRight2() {
		return this.data.v2();
	}

	/**
	 * Returns the context c1
	 * of this recurrent pair.
	 */
	public Term getContextC1() {
		return this.data.c1();
	}

	/**
	 * Returns the context c2
	 * of this recurrent pair.
	 */
	public Term getContextC2() {
		return this.data.c2();
	}

	/**
	 * Returns the ground term s of
	 * this recurrent pair.
	 */
	public Term getS() {
		return this.data.s();
	}

	/**
	 * Returns the term t of
	 * this recurrent pair.
	 */
	public Term getT() {
		return this.data.t();
	}

	/**
	 * Returns the integer m1 of
	 * this recurrent pair.
	 */
	public int getM1() {
		return this.data.m1();
	}

	/**
	 * Returns the integer m2 of
	 * this recurrent pair.
	 */
	public int getM2() {
		return this.data.m2();
	}

	/**
	 * Returns the integer n1 of
	 * this recurrent pair.
	 */
	public int getN1() {
		return this.data.n1();
	}

	/**
	 * Returns the integer n2 of
	 * this recurrent pair.
	 */
	public int getN2() {
		return this.data.n2();
	}

	/**
	 * Returns the integer n3 of
	 * this recurrent pair.
	 */
	public int getN3() {
		return this.data.n3();
	}

	/**
	 * Returns the integer n4 of
	 * this recurrent pair.
	 */
	public int getN4() {
		return this.data.n4();
	}

	/**
	 * Returns a nonterminating term from this
	 * recurrent pair.
	 *
	 * @return a nonterminating term
	 */
	public Function getNonTerminatingTerm() {
		return this.data.nonTerminatingTerm();
	}

	/**
	 * Returns a String representation of this
	 * recurrent pair.
	 */
	@Override
	public String toString() {
		return RecurrentPairFormatter.formatDetailedCertificate(this);
	}

}
