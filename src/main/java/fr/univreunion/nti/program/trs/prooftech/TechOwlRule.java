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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech;

import java.util.List;

import fr.univreunion.nti.program.AnalysisContext;
import fr.univreunion.nti.program.Argument;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * Recognizes the Owl rule {@code delta x y -> y (x y)} and certifies its
 * nontermination with an occurrence-count invariant.
 * <p>
 * This rule is Example 30 in J. Endrullis and H. Zantema,
 * <cite>Proving non-termination by finite automata</cite>, RTA 2015,
 * LIPIcs 36, pp. 160--176.
 *
 * @author <A HREF="mailto:etiennepayet@univ-reunion.fr">Etienne Payet</A>
 * @see <a href="https://doi.org/10.4230/LIPIcs.RTA.2015.160">
 * Endrullis and Zantema, RTA 2015</a>
 */
public class TechOwlRule implements ProofTechnique {

	/** Maximum number of rules inspected by this bounded technique. */
	private static final int MAX_RULE_COUNT = 200;

	/** Message emitted when the Owl rule was not found. */
	private static final String NOT_FOUND_MESSAGE = "No Owl rule found!";

	/**
	 * Runs this technique on the specified TRS.
	 *
	 * @param trs the TRS to analyze
	 * @param context the context of the analysis
	 * @return the proof built by this technique
	 */
	@Override
	public Proof run(Trs trs, AnalysisContext context) {
		Proof proof = context.createProof();
		proof.printlnIfVerbose("## Searching for a bounded Owl rule " +
				"[Endrullis and Zantema, RTA'15]...");
		OwlRule owlRule = findOwlRule(trs);
		OwlWitness witness = owlRule == null ? null : buildWitness(owlRule);
		if (witness == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		proof.printlnIfVerbose("Found an Owl rule!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(new OwlRuleArgument(witness));
		return proof;
	}

	/** Finds the first Owl rule in input order. */
	private static OwlRule findOwlRule(Trs trs) {
		int ruleNumber = 1;
		for (RuleTrs rule : trs) {
			if (ruleNumber > MAX_RULE_COUNT)
				return null;
			OwlRule owlRule = match(ruleNumber, rule);
			if (owlRule != null)
				return owlRule;
			ruleNumber++;
		}
		return null;
	}

	/** Matches {@code a(a(delta,x),y) -> a(y,a(x,y))}. */
	private static OwlRule match(int ruleNumber, RuleTrs rule) {
		Function left = rule.getLeft();
		FunctionSymbol application = left.getRootSymbol();
		if (application.getArity() != 2 ||
				lacksRoot(left.get(0), application) ||
				!isConstant(left.get(0).get(0)) ||
				!(left.get(0).get(1) instanceof Variable x) ||
				!(left.get(1) instanceof Variable y) || x.deepEquals(y))
			return null;

		Term right = rule.getRight();
		if (lacksRoot(right, application) || !right.get(0).deepEquals(y) ||
				lacksRoot(right.get(1), application) ||
				!right.get(1).get(0).deepEquals(x) ||
				!right.get(1).get(1).deepEquals(y))
			return null;

		return new OwlRule(
				ruleNumber, rule, application, left.get(0).get(0));
	}

	/** Builds and replays the first reduction from the invariant language. */
	private static OwlWitness buildWitness(OwlRule owlRule) {
		Term delta = owlRule.delta();
		Term partialApplication = apply(
				owlRule.application(), delta, delta);
		Term source = apply(
				owlRule.application(), partialApplication, partialApplication);

		Substitution substitution = new Substitution();
		RuleTrs rule = owlRule.rule();
		if (!rule.getLeft().isMoreGeneralThan(source, substitution))
			return null;
		Term target = rule.getRight().apply(substitution);
		Term expected = apply(owlRule.application(), partialApplication,
				apply(owlRule.application(), delta, partialApplication));
		return target.deepEquals(expected) ?
				new OwlWitness(owlRule, source, target) : null;
	}

	/** Builds one application term. */
	private static Term apply(
			FunctionSymbol application,
			Term left,
			Term right) {

		return new Function(application, List.of(left, right));
	}

	/** Returns whether the term does not have the specified root symbol. */
	private static boolean lacksRoot(Term term, FunctionSymbol root) {
		return term.isVariable() || term.getRootSymbol() != root;
	}

	/** Returns whether the term is a constant. */
	private static boolean isConstant(Term term) {
		return !term.isVariable() && term.getRootSymbol().getArity() == 0;
	}

	/** A matched Owl rule and its source location. */
	private record OwlRule(
			int ruleNumber,
			RuleTrs rule,
			FunctionSymbol application,
			Term delta) {}

	/** The matched rule and its replayed first step. */
	private record OwlWitness(OwlRule owlRule, Term source, Term target) {}

	/** Proof argument for the occurrence-count invariant of an Owl rule. */
	private record OwlRuleArgument(OwlWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			return spaces + this.witness.source() + " -> " +
					this.witness.target() + " (rule " +
					this.witness.owlRule().ruleNumber() +
					", position " + new Position() + ")";
		}

		@Override
		public String getWitnessKind() {
			return "Owl-rule invariant";
		}

		@Override
		public String toString() {
			OwlRule owlRule = this.witness.owlRule();
			String application = owlRule.application().toString();
			String delta = owlRule.delta().toString();
			String partial = application + "(" + delta + "," + delta + ")";
			return "* Technique: bounded Owl-rule recognition\n" +
					"* Certificate: " + this.witness.source() +
					" is non-terminating\n" +
					"* Description:\n" +
					"For a closed term t over " + application + " and " + delta +
					", let P(t) count occurrences of " + partial + ". " +
					"The normal forms are generated by N ::= " + delta + " | " +
					application + "(" + delta + ",N), so every normal form " +
					"has P(t) <= 1.\n" +
					"For one contraction with ground instances x and y, the two " +
					"occurrence counts are P(x)+P(y)+[x=" + delta + "] and " +
					"P(x)+2P(y)+[x=" + delta + " and y=" + delta + "]. " +
					"If x=" + delta + " and y!=" + delta + ", then P(y)>=1; " +
					"hence contraction never decreases P.\n" +
					"Since the displayed term has P(t) = 2, every term " +
					"reached from it has another redex, yielding an infinite " +
					"rewrite sequence. The first step is:\n" + getDetails(0);
		}
	}
}
