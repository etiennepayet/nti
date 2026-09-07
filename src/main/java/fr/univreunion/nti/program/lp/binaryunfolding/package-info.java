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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

/**
 * Binary unfolding support for logic-program nontermination proofs.
 *
 * <p>The package is organized around a few groups of collaborators:</p>
 * <ul>
 *   <li>{@link LpBinaryNonTerminationProver} orchestrates proof iterations,
 *       termination fallback, witness generation, and mode checking.</li>
 *   <li>{@link LpBinaryUnfolder}, {@link RuleLpBinaryUnfolder},
 *       {@link BinaryUnfoldingRuleApplicator}, and related
 *       {@code BinaryUnfolding...} value types compute unfolded rules.</li>
 *   <li>{@link LpBinaryWitnessGenerator}, {@link UnitWitnessBuilder},
 *       {@link WitnessExtender}, and {@link LpBinaryWitnessGeneration}
 *       construct nontermination witnesses from unfolded binary rules.</li>
 *   <li>{@link RecurrentPairLpFinder}, {@link RecurrentPairLp}, and
 *       {@link RecurrentPairLpFormatter} search for and render recurrent-pair
 *       witnesses.</li>
 *   <li>{@link LpBinaryProofState} and {@link LpBinaryProofIterationResult}
 *       are small proof-iteration support types used by the prover.</li>
 * </ul>
 *
 * <p>The binary unfolding semantics is due to M. Codish and C. Taboch,
 * <a href="https://doi.org/10.1016/S0743-1066(99)00006-0"><i>A Semantic
 * Basis for the Termination Analysis of Logic Programs</i></a>, Journal of
 * Logic Programming 41(1), pp. 103--123, 1999. Loop inference follows
 * E. Payet and F. Mesnard,
 * <a href="https://doi.org/10.1145/1119479.1119481"><i>Non-Termination
 * Inference of Logic Programs</i></a>, ACM Transactions on Programming
 * Languages and Systems 28(2), pp. 256--289, 2006.</p>
 *
 * <p>Recurrent-pair witnesses follow E. Payet,
 * <a href="https://doi.org/10.1007/s10817-023-09693-z"><i>Non-Termination
 * in Term Rewriting and Logic Programming</i></a>, Journal of Automated
 * Reasoning 68, article 4, 2024, and the extension in
 * <a href="https://doi.org/10.1007/978-3-032-04848-6_10"><i>Recurrent
 * Pairs Revisited</i></a>, LOPSTR 2025, LNCS 16117, pp. 154--164, 2026.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
package fr.univreunion.nti.program.lp.binaryunfolding;
