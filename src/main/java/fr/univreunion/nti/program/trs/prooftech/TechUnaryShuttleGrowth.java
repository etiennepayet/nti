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

package fr.univreunion.nti.program.trs.prooftech;

import java.util.ArrayList;
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
 * Recognizes bounded schemas that grow unary counters by shuttling either a
 * counter between two arguments or markers along unary spines.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
public class TechUnaryShuttleGrowth implements ProofTechnique {

	/** Maximum number of rules inspected by this bounded technique. */
	private static final int MAX_RULE_COUNT = 200;

	/** Message emitted when no certified schema was found. */
	private static final String NOT_FOUND_MESSAGE =
			"No unary shuttle growth found!";

	/** Witness kind shared by every schema recognized by this technique. */
	private static final String WITNESS_KIND = "unary shuttle growth";

	/** Prefix of the certificate line in every proof argument. */
	private static final String CERTIFICATE_PREFIX = "* Certificate: ";

	/** Header shared by every proof argument of this technique. */
	private static final String TECHNIQUE_HEADER =
			"* Technique: bounded unary-shuttle growth recognition\n";

	/** Shared transition from a replayed step count to its result. */
	private static final String STEPS_TO_RESULT = " steps to\n";

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
		proof.printlnIfVerbose("## Searching for bounded unary shuttle growth...");
		ShuttleSchema schema = findSchema(trs);
		ShuttleGrowthWitness witness = schema == null ? null : buildWitness(schema);
		Argument argument = witness == null ?
				UnaryMarkerShuttleGrowth.findArgument(trs) :
				new UnaryShuttleGrowthArgument(witness);
		if (argument == null) {
			proof.printlnIfVerbose(NOT_FOUND_MESSAGE);
			return proof;
		}

		proof.printlnIfVerbose("Found unary shuttle growth!");
		proof.setResult(Proof.ProofResult.NO);
		proof.setArgument(argument);
		return proof;
	}

	/** Finds the first complete schema in input-rule order. */
	private static ShuttleSchema findSchema(Trs trs) {
		List<NumberedRule> rules = numberRules(trs);
		if (rules == null)
			return null;

		for (NumberedRule transferRightRule : rules) {
			FirstRuleShape first = firstRuleShape(transferRightRule);
			if (first == null)
				continue;
			for (NumberedRule switchToLeftRule : rules) {
				SecondRuleShape second = secondRuleShape(switchToLeftRule, first);
				if (second == null)
					continue;
				NumberedRule transferLeftRule =
						findTransferLeftRule(rules, first, second);
				NumberedRule switchToRightRule =
						findSwitchToRightRule(rules, first, second);
				if (transferLeftRule != null && switchToRightRule != null)
					return new ShuttleSchema(
							transferRightRule, switchToLeftRule,
							transferLeftRule, switchToRightRule,
							first.rightState(), second.leftState(),
							first.successor(), second.zero());
			}
		}
		return null;
	}

	/** Numbers the bounded input prefix, or rejects an input beyond the bound. */
	private static List<NumberedRule> numberRules(Trs trs) {
		List<NumberedRule> rules = new ArrayList<>();
		int ruleNumber = 1;
		for (RuleTrs rule : trs) {
			if (rules.size() >= MAX_RULE_COUNT)
				return null;
			rules.add(new NumberedRule(ruleNumber++, rule));
		}
		return rules;
	}

	/** Extracts {@code R(x,a(y)) -> R(a(x),y)}. */
	private static FirstRuleShape firstRuleShape(NumberedRule numberedRule) {
		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		FunctionSymbol rightState = left.getRootSymbol();
		if (rightState.getArity() != 2 ||
				!(left.get(0) instanceof Variable x) ||
				left.get(1).isVariable() ||
				left.get(1).getRootSymbol().getArity() != 1 ||
				!(left.get(1).get(0) instanceof Variable y) || x.deepEquals(y))
			return null;
		FunctionSymbol successor = left.get(1).getRootSymbol();

		Term right = rule.getRight();
		if (lacksRoot(right, rightState) ||
				lacksRoot(right.get(0), successor) ||
				!right.get(0).get(0).deepEquals(x) ||
				!right.get(1).deepEquals(y))
			return null;
		return new FirstRuleShape(rightState, successor);
	}

	/** Extracts {@code R(x,b) -> L(x,a(b))}. */
	private static SecondRuleShape secondRuleShape(
			NumberedRule numberedRule,
			FirstRuleShape first) {

		RuleTrs rule = numberedRule.rule();
		Function left = rule.getLeft();
		if (lacksRoot(left, first.rightState()) ||
				!(left.get(0) instanceof Variable x) ||
				!isConstant(left.get(1)))
			return null;
		Term zero = left.get(1);

		Term right = rule.getRight();
		if (right.isVariable() || right.getRootSymbol().getArity() != 2 ||
				!right.get(0).deepEquals(x) ||
				lacksRoot(right.get(1), first.successor()) ||
				!right.get(1).get(0).deepEquals(zero))
			return null;
		return new SecondRuleShape(right.getRootSymbol(), zero);
	}

	/** Finds {@code L(a(x),y) -> L(x,a(y))}. */
	private static NumberedRule findTransferLeftRule(
			List<NumberedRule> rules,
			FirstRuleShape first,
			SecondRuleShape second) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, second.leftState()) ||
					lacksRoot(left.get(0), first.successor()) ||
					!(left.get(0).get(0) instanceof Variable x) ||
					!(left.get(1) instanceof Variable y) || x.deepEquals(y))
				continue;

			Term right = rule.getRight();
			if (!lacksRoot(right, second.leftState()) &&
					right.get(0).deepEquals(x) &&
					!lacksRoot(right.get(1), first.successor()) &&
					right.get(1).get(0).deepEquals(y))
				return numberedRule;
		}
		return null;
	}

	/** Finds {@code L(b,x) -> R(a(b),x)}. */
	private static NumberedRule findSwitchToRightRule(
			List<NumberedRule> rules,
			FirstRuleShape first,
			SecondRuleShape second) {

		for (NumberedRule numberedRule : rules) {
			RuleTrs rule = numberedRule.rule();
			Function left = rule.getLeft();
			if (lacksRoot(left, second.leftState()) ||
					!left.get(0).deepEquals(second.zero()) ||
					!(left.get(1) instanceof Variable x))
				continue;

			Term right = rule.getRight();
			if (!lacksRoot(right, first.rightState()) &&
					!lacksRoot(right.get(0), first.successor()) &&
					right.get(0).get(0).deepEquals(second.zero()) &&
					right.get(1).deepEquals(x))
				return numberedRule;
		}
		return null;
	}

	/** Builds and replays the first three-step shuttle phase. */
	private static ShuttleGrowthWitness buildWitness(ShuttleSchema schema) {
		Term one = successor(schema.zero(), schema.successor());
		Term two = successor(one, schema.successor());
		Term start = state(one, schema.zero(), schema.rightState());
		List<RewriteStep> steps = new ArrayList<>();
		Term current = addStep(
				steps, start, schema.switchToLeftRule(), new Position());
		current = addStep(
				steps, current, schema.transferLeftRule(), new Position());
		current = addStep(
				steps, current, schema.switchToRightRule(), new Position());

		Term expected = state(one, two, schema.rightState());
		return current != null && current.deepEquals(expected) ?
				new ShuttleGrowthWitness(schema, start, current, List.copyOf(steps)) :
				null;
	}

	/** Applies and records one required rewrite step. */
	private static Term addStep(
			List<RewriteStep> steps,
			Term source,
			NumberedRule numberedRule,
			Position position) {

		if (source == null)
			return null;
		Term redex = source.get(position);
		Substitution substitution = new Substitution();
		RuleTrs rule = numberedRule.rule();
		if (redex == null || !rule.getLeft().isMoreGeneralThan(redex, substitution))
			return null;
		Term target = source.replace(position, rule.getRight().apply(substitution));
		steps.add(new RewriteStep(
				source, target, numberedRule.number(), position));
		return target;
	}

	/** Returns whether the term lacks the specified function symbol at its root. */
	private static boolean lacksRoot(Term term, FunctionSymbol root) {
		return term.isVariable() || term.getRootSymbol() != root;
	}

	/** Returns whether the term is a constant. */
	private static boolean isConstant(Term term) {
		return !term.isVariable() && term.getRootSymbol().getArity() == 0;
	}

	/** Builds one unary successor term. */
	private static Term successor(Term argument, FunctionSymbol successor) {
		return new Function(successor, List.of(argument));
	}

	/** Builds one binary state term. */
	private static Term state(Term first, Term second, FunctionSymbol state) {
		return new Function(state, List.of(first, second));
	}

	/** One input rule together with its one-based number. */
	private record NumberedRule(int number, RuleTrs rule) {}

	/** Symbols extracted from the first transfer rule. */
	private record FirstRuleShape(
			FunctionSymbol rightState,
			FunctionSymbol successor) {}

	/** Symbols extracted from the switch to the left state. */
	private record SecondRuleShape(
			FunctionSymbol leftState,
			Term zero) {}

	/** A complete matched rule schema. */
	private record ShuttleSchema(
			NumberedRule transferRightRule,
			NumberedRule switchToLeftRule,
			NumberedRule transferLeftRule,
			NumberedRule switchToRightRule,
			FunctionSymbol rightState,
			FunctionSymbol leftState,
			FunctionSymbol successor,
			Term zero) {}

	/** One replayed rewrite step. */
	private record RewriteStep(
			Term source,
			Term target,
			int ruleNumber,
			Position position) {}

	/** The matched schema and its concrete first growth phase. */
	private record ShuttleGrowthWitness(
			ShuttleSchema schema,
			Term start,
			Term result,
			List<RewriteStep> steps) {}

	/** Proof argument for a certified unary-shuttle growth schema. */
	private record UnaryShuttleGrowthArgument(
			ShuttleGrowthWitness witness) implements Argument {

		@Override
		public String getDetails(int indentation) {
			String spaces = " ".repeat(Math.max(0, indentation));
			List<RewriteStep> steps = this.witness.steps();
			String[] lines = new String[steps.size()];
			int stepNumber = 1;
			for (RewriteStep step : steps)
				lines[stepNumber - 1] = spaces + stepNumber++ + ". " +
						step.source() + " -> " + step.target() + " (rule " +
						step.ruleNumber() + ", position " + step.position() + ")";
			return String.join("\n", lines);
		}

		@Override
		public String getWitnessKind() {
			return WITNESS_KIND;
		}

		@Override
		public String toString() {
			ShuttleSchema schema = this.witness.schema();
			String rightState = schema.rightState().toString();
			String leftState = schema.leftState().toString();
			String successor = schema.successor().toString();
			String zero = schema.zero().toString();
			return TECHNIQUE_HEADER +
					CERTIFICATE_PREFIX + this.witness.start() +
					" is non-terminating\n" +
					"* Description:\n" +
					"Write n-bar for " + successor + "^n(" + zero + "). " +
					"For every n >= 0, the matched rules imply\n" +
					rightState + "(1-bar,n-bar) ->^n " + rightState +
					"((n+1)-bar,0-bar) -> " + leftState +
					"((n+1)-bar,1-bar)\n" +
					"->^(n+1) " + leftState + "(0-bar,(n+2)-bar) -> " +
					rightState + "(1-bar,(n+2)-bar).\n" +
					"Thus " + rightState + "(1-bar,n-bar) rewrites in 2n+3 " +
					"steps to " + rightState + "(1-bar,(n+2)-bar). " +
					"Starting with n = 0 yields an infinite rewrite sequence.\n" +
					"The first growth phase rewrites in " +
					this.witness.steps().size() + STEPS_TO_RESULT +
					this.witness.result() + ".\n" + getDetails(0);
		}
	}

}
