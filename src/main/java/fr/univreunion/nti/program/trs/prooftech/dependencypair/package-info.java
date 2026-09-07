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
 * Dependency pair analysis orchestration for term rewrite systems.
 *
 * <p>{@link fr.univreunion.nti.program.trs.prooftech.dependencypair.DependencyPairAnalysis}
 * is the public facade. Package-private collaborators collect initial
 * dependency pair problems, configure and run framework variants, apply
 * finiteness processors sequentially, and manage concurrent infiniteness
 * searches. Concrete processors are grouped in the {@code processor}
 * subpackage.</p>
 *
 * <p>The framework follows J. Giesl, R. Thiemann, and P. Schneider-Kamp,
 * <a href="https://doi.org/10.1007/978-3-540-32275-7_21"><i>The Dependency
 * Pair Framework: Combining Techniques for Automated Termination
 * Proofs</i></a>, LPAR 2004, LNCS 3452, pp. 301--331, 2005.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
package fr.univreunion.nti.program.trs.prooftech.dependencypair;
