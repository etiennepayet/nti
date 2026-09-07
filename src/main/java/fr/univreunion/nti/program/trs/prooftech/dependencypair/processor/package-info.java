/*
 * Copyright 2026 Etienne Payet <etienne.payet at univ-reunion.fr>
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

/**
 * Dependency pair processors and their result abstraction.
 *
 * <p>This package contains finiteness and infiniteness processors used by the
 * dependency pair framework, including reduction-pair, unfolding, embedding,
 * and pattern-unfolding processors.</p>
 *
 * <p>The standard subterm, reduction-pair, argument-filtering, and usable-rule
 * processors are based on N. Hirokawa and A. Middeldorp,
 * <a href="https://doi.org/10.1007/978-3-540-25979-4_18"><i>Dependency Pairs
 * Revisited</i></a>, RTA 2004, LNCS 3091, pp. 249--268.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
package fr.univreunion.nti.program.trs.prooftech.dependencypair.processor;
