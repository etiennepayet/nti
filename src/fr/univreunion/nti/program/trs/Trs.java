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

package fr.univreunion.nti.program.trs;

import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.Callable;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

import fr.univreunion.nti.Options;
import fr.univreunion.nti.program.Path;
import fr.univreunion.nti.program.Program;
import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.argfiltering.PairOfTerms;
import fr.univreunion.nti.program.trs.family.Family;
import fr.univreunion.nti.program.trs.family.FdGraph;
import fr.univreunion.nti.program.trs.loop.trans.UnfoldedRuleTrsLoopTrans;
import fr.univreunion.nti.program.trs.nonloop.Eeg12Rule;
import fr.univreunion.nti.program.trs.nonloop.ParentTrsNonLoop;
import fr.univreunion.nti.program.trs.nonloop.PatternRule;
import fr.univreunion.nti.program.trs.prooftech.TechDpFramework;
import fr.univreunion.nti.program.trs.prooftech.TechGeneralizedRule;
import fr.univreunion.nti.program.trs.prooftech.dpproc.ProcHomeoEmbed;
import fr.univreunion.nti.program.trs.prooftech.dpproc.ProcKbo;
import fr.univreunion.nti.program.trs.prooftech.dpproc.ProcLpo;
import fr.univreunion.nti.program.trs.prooftech.dpproc.ProcPolyInterpretation;
import fr.univreunion.nti.program.trs.prooftech.dpproc.ProcUnfoldEeg12;
import fr.univreunion.nti.program.trs.prooftech.dpproc.ProcUnfoldPayet;
import fr.univreunion.nti.program.trs.prooftech.dpproc.Processor;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;

/**
 * A term rewrite system (TRS).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Trs extends Program implements Iterable<RuleTrs> {

	/**
	 * The rules of this TRS.
	 */
	protected final LinkedList<RuleTrs> rules = new LinkedList<RuleTrs>();

	/**
	 * The rewriting strategy (standard, innermost, ...) 
	 * considered for this TRS.
	 */
	private final String strategy;

	/**
	 * The set of defined symbols of this TRS =
	 * {root(l) | l -> r in this TRS}.
	 */
	private final Set<FunctionSymbol> definedSymbols = new HashSet<FunctionSymbol>();

	/**
	 * The graph for computing descendants.
	 * Used for forward unfoldings in non-termination proofs.
	 */
	private FdGraph graphForward;

	/**
	 * The graph for computing ascendants.
	 * Used for backward unfoldings in non-termination proofs.
	 */
	private FdGraph graphBackward;

	/**
	 * The set of dependency pairs of this TRS.
	 */
	private final Dpairs dpairs;

	/**
	 * The estimated dependency graph of this TRS.
	 */
	private final DependencyGraph dependencyGraph;

	/**
	 * The simple cycles that have been discovered while
	 * unfolding this TRS. Used for finding loops.
	 */
	private final Deque<Set<RuleTrs>> simpleCycles = new LinkedList<Set<RuleTrs>>();

	/**
	 * The pattern rules obtained from applying (I), (II) and (III)
	 * of [Emmes, Enger, Giesl, IJCAR'12] to the rules of this TRS.
	 * Used for proving non-looping non-termination.
	 */
	private Collection<PatternRule> rules_as_PatternRules;

	/**
	 * Builds a term rewrite system (TRS).
	 * 
	 * @param name the name of this TRS
	 * @param rules the rules of this TRS
	 * @param strategy the rewriting strategy considered for this TRS
	 * (only FULL i.e., standard rewriting, is supported for the moment)
	 * @throws IllegalArgumentException if a given rule is <tt>null</tt>
	 * or the provided strategy is not FULL
	 */
	public Trs(String name, Collection<RuleTrs> rules, String strategy) {

		super(name);

		// First, we build the rules of this TRS.
		for (RuleTrs R : rules)
			if (R != null) {
				// Add this rule to this TRS.
				this.rules.add(R);
				// Complete the set D of defined symbols of this TRS.
				this.definedSymbols.add(R.getLeft().getRootSymbol());
			}
			else
				throw new IllegalArgumentException("construction of a TRS with a null rule");

		// Then, we set the strategy.
		if (!"FULL".equals(strategy))
			throw new IllegalArgumentException(
					"unsupported strategy: only FULL (standard rewriting) is supported for the moment");
		this.strategy = strategy;

		// Finally, we build the dependency pairs and
		// the estimated dependency graph of this TRS.
		this.dpairs = this.buildDependencyPairs();
		this.dependencyGraph = new DependencyGraph(this);		
	}

	/**
	 * Deep copy constructor.
	 * 
	 * If the specified <code>dpairsCopy</code>
	 * is not <code>null</code>, then it is
	 * filled so that each dependency pair of
	 * <code>IR</code> is mapped to its copy.
	 * 
	 * @param IR the TRS to copy
	 * @param dpairsCopy a structure mapping each
	 * dependency pair of <code>IR</code> to its
	 * copy
	 */
	private Trs(Trs IR, Map<RuleTrs, RuleTrs> dpairsCopy) {

		super(IR.getName());

		// We copy the rules of IR.
		for (RuleTrs R : IR)
			this.rules.add(R.deepCopy());

		// We copy the strategy and the defined
		// symbols of IR.
		this.strategy = IR.strategy;
		this.definedSymbols.addAll(IR.definedSymbols);

		// We copy the dependency pairs of IR and
		// we add the copies to the provided map
		// (if not null).
		LinkedList<RuleTrs> dpairs = new LinkedList<RuleTrs>();
		for (RuleTrs R : IR.dpairs) {
			RuleTrs Rcopy = R.deepCopy();
			if (dpairsCopy != null) dpairsCopy.put(R, Rcopy);
			dpairs.add(Rcopy);
		}
		this.dpairs = new Dpairs(dpairs);

		// Finally, we build the estimated dependency
		// graph of this new object.
		this.dependencyGraph = new DependencyGraph(this);
	}
	
	/**
	 * Shallow copy constructor, i.e., the rules
	 * are deeply copied but the dependency pairs
	 * and the estimated dependency graph are set
	 * to <code>null</code>.
	 * 
	 * @param IR the TRS to copy
	 */
	private Trs(Trs IR) {

		super(IR.getName());

		// We copy the rules of IR.
		for (RuleTrs R : IR)
			this.rules.add(R.deepCopy());

		// We copy the strategy and the defined
		// symbols of IR.
		this.strategy = IR.strategy;
		this.definedSymbols.addAll(IR.definedSymbols);

		// We do not copy and do not compute the dependency
		// pairs and the estimated dependency graph.
		this.dpairs = null;
		this.dependencyGraph = null;
	}


	/**
	 * Returns a deep copy of this TRS.
	 * 
	 * If the specified <code>dpairsCopy</code>
	 * is not <code>null</code>, then it is
	 * filled so that each dependency pair of
	 * this TRS is mapped to its copy.
	 * 
	 * @param dpairsCopy a structure mapping each
	 * dependency pair to its copy
	 * @return a deep copy of this TRS
	 */
	public Trs copy(Map<RuleTrs, RuleTrs> dpairsCopy) {
		return new Trs(this, dpairsCopy);
	}
	
	/**
	 * Returns a shallow copy of this TRS, i.e., the
	 * rules are deeply copied but the dependency pairs
	 * and the estimated dependency graph are not
	 * (the resulting TRS has undefined dependency pairs
	 * and estimated dependency graph).
	 * 
	 * @return a shallow copy of this TRS
	 */
	public Trs shallowCopy() {
		return new Trs(this);
	}

	/**
	 * Returns the rewriting strategy
	 * (standard, innermost, ...) 
	 * considered for this TRS.
	 * 
	 * @return the rewriting strategy
	 * considered for this TRS
	 */
	public String getStrategy() {
		return this.strategy;
	}

	/**
	 * Returns the size of this TRS.
	 * 
	 * @return the size of this TRS
	 */
	@Override
	public int size() {
		return this.rules.size();
	}

	/**
	 * Returns the depth of this TRS i.e., the
	 * maximal depth of the rules of this TRS.
	 *  
	 * @return the depth of this TRS
	 */
	public int depth() {
		int max = -1;

		for (RuleTrs R : this.rules) {
			int d = R.depth();
			if (d > max) max = d;
		}

		return max;
	}

	/**
	 * Returns an iterator over the rules of this TRS.
	 * 
	 * @return an <code>Iterator</code>
	 */
	@Override
	public Iterator<RuleTrs> iterator() {
		return this.rules.iterator();	
	}

	/**
	 * Return an iterator over the pattern rules obtained
	 * from applying (I), (II) and (III) of [Emmes, Enger,
	 * Giesl, IJCAR'12] to the rules of this TRS.
	 * 
	 * @return an iterator over the pattern rules of this
	 * TRS
	 */
	public Iterator<PatternRule> iteratorPatternRules() {
		// We create the initial pattern rules if needed.
		this.initForUnfoldingNL();

		return this.rules_as_PatternRules.iterator();
	}

	/**
	 * Returns <tt>true</tt> iff the provided symbol
	 * is defined in this TRS.
	 * 
	 * @param f a function symbol
	 * @return <tt>true</tt> iff the provided symbol
	 * is defined in this TRS
	 */
	public boolean isDefined(FunctionSymbol f) {
		return this.definedSymbols.contains(f);
	}

	/**
	 * Returns <tt>true</tt> iff the root symbol of
	 * the provided term is defined in this TRS.
	 * 
	 * @param t a term
	 * @return <tt>true</tt> iff the root symbol of the 
	 * provided term is defined in this TRS
	 */
	public boolean isRootDefined(Term t) {		
		return this.isDefined(t.getRootSymbol());
	}

	/**
	 * Computes the set of descendants of the given term
	 * w.r.t. this TRS.
	 * 
	 * @param t the term whose descendants have
	 * to be computed
	 * @return the set of descendants of <code>t</code>
	 * w.r.t. this TRS
	 * 
	 */
	public Family descendants(Term t) {
		if (this.graphForward == null)
			this.createGraphForward();

		return this.graphForward.getFamily(t);
	}

	/**
	 * Computes the set of ascendants of the given term
	 * w.r.t. this TRS.
	 * 
	 * @param t the term whose ascendants have
	 * to be computed
	 * @return the set of ascendants of <code>t</code>
	 * w.r.t. this TRS
	 * 
	 */
	public Family ascendants(Term t) {
		if (this.graphBackward == null)
			this.createGraphBackward();

		return this.graphBackward.getFamily(t);
	}

	/**
	 * Builds the graph for forward analysis.
	 */
	private void createGraphForward() {
		// We add edges of the form l -> r where
		// l -> r is a rule of IR.
		this.graphForward = new FdGraph(this);

		for (RuleTrs R : this)
			this.graphForward.addEdge(R.getLeft(), R.getRight());

		this.graphForward.closeTransitively();
	}

	/**
	 * Builds the graph for backward analysis.
	 */
	private void createGraphBackward() {
		// We add edges of the form r -> l where
		// l -> r is a rule of IR^-1.
		this.graphBackward = new FdGraph(this);

		for (RuleTrs R : this)
			this.graphBackward.addEdge(R.getRight(), R.getLeft());

		this.graphBackward.closeTransitively();
	}

	/**
	 * Returns a String representation of the graph used
	 * for computing descendants with this TRS.
	 * 
	 * @return a String representation of the forward graph
	 * of this TRS
	 */
	public String getGraphForward() {
		if (this.graphForward == null)
			this.createGraphForward();

		return this.graphForward.toString();
	}

	/**
	 * Returns a String representation of the graph used
	 * for computing ascendants with this TRS.
	 * 
	 * @return a String representation of the backward graph
	 * of this TRS
	 */
	public String getGraphBackward() {
		if (this.graphBackward == null)
			this.createGraphBackward();

		return this.graphBackward.toString();
	}

	/**
	 * Adds the specified simple cycle to this TRS.
	 * 
	 * @param simpleCycle a simple cycle to be added to this TRS
	 * @return <code>true</code> iff this TRS changed as a result
	 * of the call
	 */
	public boolean addSimpleCycle(Set<RuleTrs> simpleCycle) {
		return this.simpleCycles.add(simpleCycle);
	}

	/**
	 * Returns <code>true</code> iff this TRS contains the specified
	 * simple cycle.
	 *  
	 * @param simpleCycle simple cycle whose presence in this set is
	 * to be tested
	 * @return <code>true</code> iff this TRS contains the specified
	 * simple cycle
	 */
	public boolean containsSimpleCycle(Set<RuleTrs> simpleCycle) {
		return this.simpleCycles.contains(simpleCycle);
	}

	/**
	 * Returns the dependency pairs of this TRS.
	 * 
	 * @return the dependency pairs of this TRS
	 */
	public Dpairs dependencyPairs() {
		return this.dpairs;
	}

	/**
	 * Builds and returns the dependency pairs of this TRS.
	 */
	private Dpairs buildDependencyPairs() {
		LinkedList<RuleTrs> dpairs = new LinkedList<RuleTrs>();

		for (RuleTrs R : this.rules) {
			Term right = R.getRight();
			for (Position p : right)  {
				Term subterm_p = right.get(p);
				if (this.isRootDefined(subterm_p))
					dpairs.add(new RuleTrs(
							(Function) R.getLeft().toTuple(),
							subterm_p.toTuple(),
							R.getNumberInFile()));
			}
		}

		return new Dpairs(dpairs);
	}

	/**
	 * Returns the estimated dependency graph of this TRS.
	 * 
	 * @return the estimated dependency graph of this TRS
	 */
	public DependencyGraph getDependencyGraph() {
		return this.dependencyGraph;
	}

	/**
	 * Returns the collection of initial DP problems for
	 * this TRS.
	 * 
	 * This collection consists of the pairs
	 * <code>(IR, S)</code> where <code>IR</code> is this
	 * TRS and <code>S</code> is an SCC of the estimated
	 * dependency graph of <code>IR</code>.
	 */
	public DpProbCollection getInitialDPProblems() {
		// The collection to return at the end.
		DpProbCollection problems = new DpProbCollection();

		// We compute the SCCs of the estimated dependency
		// graph of this TRS.
		Deque<Dpairs> SCCs = this.getDependencyGraph().getSCCs();

		// The initial problems are the pairs (IR, S)
		// where IR is this TRS and S is an SCC of the
		// estimated dependency graph of IR.
		for (Dpairs S : SCCs)
			problems.add(new DpProblem(this, S));

		return problems;
	}

	/**
	 * Returns a collection consisting of syntactic loops
	 * that occur in the provided set of dependency pairs
	 * of this TRS.
	 * 
	 * @param dpairs the set of dependency pairs where
	 * syntactic loops have to be searched for
	 * @return a collection of syntactic loops
	 */
	public Collection<? extends UnfoldedRuleTrs> getSyntacticLoops(Dpairs dpairs) {
		// The collection that will be returned.
		Collection<UnfoldedRuleTrs> Loops = new LinkedList<UnfoldedRuleTrs>();

		Deque<RuleTrs> Scopy = dpairs.toDeque();
		int n = Scopy.size();
		for (int i = 0; i < n; i++) {
			RuleTrs R = Scopy.removeFirst();
			Collection<RuleTrs> simpleCycle = new LinkedList<RuleTrs>();
			simpleCycle.add(R);
			Loops.addAll(UnfoldedRuleTrsLoopTrans.getUnfoldedInstances(
					R.getLeft(), R.getRight(), 0, null, new Path(R), Scopy, simpleCycle));
			Scopy.addLast(R);
		}

		return Loops;
	}

	/**
	 * Returns a collection consisting of syntactic loops
	 * that occur in the provided sets of dependency pairs
	 * of this TRS.
	 * 
	 * @param C the sets of dependency pairs where
	 * syntactic loops have to be searched for
	 * @return a collection of syntactic loops
	 */
	private Collection<? extends UnfoldedRuleTrs> getSyntacticLoops(Collection<Dpairs> C) {
		// The collection that will be returned.
		Collection<UnfoldedRuleTrs> Loops = new LinkedList<UnfoldedRuleTrs>();

		for (Dpairs dpairs : C)
			Loops.addAll(this.getSyntacticLoops(dpairs));

		return Loops;
	}

	/**
	 * Returns a collection consisting of syntactic loops that
	 * occur in the SCCs of the estimated dependency graph of
	 * this TRS.
	 *
	 * @return a collection of syntactic loops
	 */
	public Collection<? extends UnfoldedRuleTrs> getSyntacticLoops() {
		return this.getSyntacticLoops(this.getDependencyGraph().getSCCs());
	}

	/**
	 * Returns the pattern rules that can be built from the
	 * rules provided by the specified iterator, using (I),
	 * (II) and (III) in [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * @param it an iterator over a collection of rewrite rules
	 * @return the pattern rules that can be built from the
	 * rules provided by the specified iterator
	 */
	public Collection<PatternRule> getPatternRules(Iterator<RuleTrs> it) {
		// The collection to return at the end.
		Collection<PatternRule> result = new LinkedList<PatternRule>();

		// First, we apply (I) of [Emmes, Enger, Giesl, IJCAR'12].
		Collection<PatternRule> I = new LinkedList<PatternRule>();
		while (it.hasNext()) {
			RuleTrs R = it.next();
			I.add(new PatternRule(
					R, 0,
					new ParentTrsNonLoop(null, R, null, false, Eeg12Rule.I),
					null));
		}
		result.addAll(I);

		// Then, we apply (II) of [Emmes, Enger, Giesl, IJCAR'12].
		for (PatternRule R : I) {
			Map<Term, Term> copies = new HashMap<Term, Term>();
			Function s = R.getLeft();
			Term sRenamed = s.deepCopy(copies);

			Term t = R.getRight();

			Substitution tau = new Substitution();
			boolean unify = sRenamed.isUnifiableWith(t, tau);

			if (unify) {
				Substitution rho = new Substitution();
				Substitution invrho = new Substitution();
				for (Map.Entry<Term, Term> e : copies.entrySet())
					if (e.getKey() instanceof Variable && e.getValue() instanceof Variable) {
						Variable v1 = (Variable) e.getKey();
						Variable v2 = (Variable) e.getValue();
						rho.add(v1, v2);
						invrho.add(v2, v1);
					}

				// As in [Emmes, Enger, Giesl, IJCAR'12],
				// we set theta = (rho.tau.rho^-1)|V(s).
				Substitution theta = rho.composeWith(tau).composeWith(invrho).restrictTo(s.getVariables());
				// As in [Emmes, Enger, Giesl, IJCAR'12],
				// we set sigma = (tau.rho^-1)|V(t).
				Substitution sigma = tau.composeWith(invrho).restrictTo(t.getVariables());
				if (theta.commutesWith(sigma) && s.apply(theta).deepEquals(t.apply(sigma))) {
					PatternRule RR = new PatternRule(
							s, sigma, new Substitution(),
							t, theta, new Substitution(),
							0, new ParentTrsNonLoop(R, null, null, false, Eeg12Rule.II),
							null);
					RR.normalizeStrongly();
					result.add(RR);
				}
			}
		}

		// Finally, we apply (III) of [Emmes, Enger, Giesl, IJCAR'12].
		for (PatternRule R : I) {
			Function s = R.getLeft();
			Term t = R.getRight();
			for (Position p : t)
				if (!p.isEmpty()) {
					// We only consider positions below the root
					// because the root position generates a rule
					// whose right-hand side's base term is a variable.
					Term t_p = t.get(p);
					if (!t_p.isVariable()) {
						// As indicated in [Emmes, Enger, Giesl, IJCAR'12],
						// footnote (3), we do not consider non-variable
						// subterms of t.
						Substitution sigma = new Substitution();
						if (t_p.isMoreGeneralThan(s.toFunction(), sigma)) {
							Variable z = new Variable();
							Term u = t.replace(p, z);
							Substitution sigmaExtended = new Substitution(sigma);
							if (sigmaExtended.add(z, u)) {
								Substitution mu = new Substitution();
								mu.add(z, t_p);
								PatternRule RR = new PatternRule(
										s, sigma, new Substitution(),
										u, sigmaExtended, mu,
										0,
										new ParentTrsNonLoop(R, null, p, false, Eeg12Rule.III),
										null);
								RR.normalizeStrongly();
								result.add(RR);
							}
						}
					}
				}
		}

		return result;
	}

	/**
	 * Returns the pattern rules that can be built from the
	 * SCCs of the estimated dependency graph of this TRS
	 * using (I), (II) and (III) in [Emmes, Enger, Giesl, IJCAR'12].
	 * 
	 * @return a collection of pattern rules
	 */
	public Collection<? extends UnfoldedRuleTrs> getPatternRules() {
		// The collection that will be returned.
		Collection<UnfoldedRuleTrs> result = new LinkedList<UnfoldedRuleTrs>();

		for (Dpairs dpairs : this.getDependencyGraph().getSCCs())
			result.addAll(this.getPatternRules(dpairs.iterator()));

		return result;
	}

	/**
	 * Performs some initialization operations
	 * before unfolding this TRS in loop mode.
	 */
	public void initForUnfolding() {
		this.simpleCycles.clear();
	}

	/**
	 * Performs some initialization operations
	 * before unfolding this TRS in non-loop mode.
	 */
	public void initForUnfoldingNL() {
		// We create the initial pattern rules if needed.
		if (this.rules_as_PatternRules == null)
			this.rules_as_PatternRules = this.getPatternRules(this.rules.iterator());
	}
	
	/**
	 * Runs a termination proof for this program.
	 * 
	 * @return the computed proof
	 */
	@Override
	public Proof proveTermination() {

		// We first check whether this TRS includes a
		// "generalized" rewrite rule.
		Proof proof = (new TechGeneralizedRule()).run(this);

		// If no "generalized" rewrite rule was detected, then
		// we try with the dependency pair framework.
		if (!proof.isSuccess()) {
			proof.printlnIfVerbose();
			
			// Only one instance of a processor checking
			// for homeomorphic embedding is necessary.
			ProcHomeoEmbed homeo = new ProcHomeoEmbed();

			// The number of threads that we are going to create.
			int nbThreads = 2;

			ExecutorService executor = Executors.newFixedThreadPool(nbThreads);
			CompletionService<Proof> ecs =
					new ExecutorCompletionService<Proof>(executor);

			List<Future<Proof>> futures = new LinkedList<Future<Proof>>();

			// The prover that does not use filters.
			// It runs a termination analysis, followed
			// by a nontermination analysis if necessary.
			futures.add(ecs.submit(new Callable<Proof>() {
				@Override
				public Proof call() throws Exception {
					// The maximum number of polynomial coefficients that is allowed.
					int maxNbCoef = 14;
					// The list of processors to apply for proving termination.
					List<Processor> procForTerm = new LinkedList<Processor>();
					procForTerm.add(homeo); // Homeomorphic embedding
					procForTerm.add(new ProcLpo(false)); // Lexicographic Path Order
					procForTerm.add(new ProcPolyInterpretation(false, maxNbCoef)); // Polynomial interpretation
					procForTerm.add(new ProcKbo(false, maxNbCoef)); // Knuth-Bendix Order
					
					// The list of processors to apply for proving nontermination.
					// We create parameters for some processors.
					List<Processor> procForNonTerm = new LinkedList<Processor>();
					Parameters param1 = new Parameters();
					param1.setMaxDepth(20);
					Parameters param2 = new Parameters();
					param2.disableBackwardUnfolding();
					// We add the processors to the list.
					procForNonTerm.add(new ProcUnfoldPayet(param1)); // Find a loop by unfolding
					procForNonTerm.add(new ProcUnfoldPayet(param2)); // Find a loop by unfolding
					procForNonTerm.add(new ProcUnfoldEeg12(new Parameters())); // Non-looping nontermination
					
					return (new TechDpFramework(procForTerm, procForNonTerm)).run(Trs.this);
				}
			}));
			// The prover that uses filters. It only performs a
			// termination analysis. We invoke it on a deep copy
			// of this TRS in order to avoid race conditions with
			// the other prover.
			futures.add(ecs.submit(new Callable<Proof>() {
				@Override
				public Proof call() throws Exception {
					// The maximum number of polynomial coefficients that is allowed.
					int maxNbCoef = 25; // 25 seems to be the best value to get the maximum number of successes in TermComp
					// The list of processors to apply for proving termination.
					List<Processor> procForTerm = new LinkedList<Processor>();
					procForTerm.add(homeo); // Homeomorphic embedding
					procForTerm.add(new ProcLpo(true)); // Lexicographic Path Order
					procForTerm.add(new ProcPolyInterpretation(true, maxNbCoef)); // Polynomial interpretation
					procForTerm.add(new ProcKbo(true, maxNbCoef)); // Knuth-Bendix Order
					
					return (new TechDpFramework(procForTerm, null)).run(Trs.this.copy(null));
				}
			}));

			executor.shutdown();

			Proof proofDP = null;
			
			try {
				long seconds = Options.getInstance().getTotalTimeLimit();
				for (int i = 0; i < nbThreads; i++) {
					try {
						Future<Proof> f = ecs.poll(seconds, TimeUnit.SECONDS);
						if (f == null) {
							// The specified time has elapsed.
							proof.printlnIfVerbose("\n** INTERRUPTED! **");
							break;
						}
						else if ((proofDP = f.get()).isSuccess())
							break;
					} catch (Exception e) {
						proof.printlnIfVerbose(e.getMessage());
						break;
					}
				}
			} finally {
				for (Future<Proof> f : futures)
					f.cancel(true);
			}
			
			if (proofDP != null) proof.merge(proofDP);
		}

		return proof;
	}

	/**
	 * Returns the rules of this TRS as a collection
	 * of pairs of terms.
	 * 
	 * @return the rules of this TRS as a collection
	 * of pairs of terms
	 */
	public Collection<PairOfTerms> toPairsOfTerms() {

		// The collection to return at the end.
		Collection<PairOfTerms> L = new LinkedList<PairOfTerms>();

		for (RuleTrs R : this.rules)
			L.add(new PairOfTerms(R, R.getLeft(), R.getRight()));

		return L;
	}

	/**
	 * Returns a String representation of this TRS.
	 * 
	 * @return a String representation of this TRS
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer("** BEGIN rewrite system: ");
		s.append(this.getName());

		// The rewriting strategy considered for this TRS.
		s.append("\n* Strategy = ");		
		s.append(this.strategy);
		s.append("\n");

		// The rules of the TRS.
		int nbRules = this.rules.size();
		s.append("* ");
		s.append(nbRules);
		s.append(" rule(s)");
		if (0 < nbRules) s.append(":");
		s.append('\n');
		for (RuleTrs R : this.rules) {
			s.append(R);
			s.append("\n");
		}

		// The simple cycles of the TRS.
		s.append("* Simple cycles = ");
		s.append(this.simpleCycles);

		// Ending message.
		s.append("\n** END rewrite system: ");
		s.append(this.getName());

		return s.toString();
	}

	/**
	 * Returns a String representation of some statistics
	 * about this program.
	 * 
	 * @return a String representation of some statistics
	 * about this program
	 */
	@Override
	public String toStringStat() {
		// Introductory message.
		StringBuffer s = new StringBuffer("** BEGIN STATS for program: ");
		s.append(this.getName());

		// The number of rules of this program.
		s.append("\n* ");
		s.append(this.rules.size());
		s.append(" rule(s)");

		// The SCCs of the dependency graph of this TRS.
		Deque<Dpairs> SCCs = this.getDependencyGraph().getSCCs();
		int minRulesSCC = -1, maxRulesSCC = -1, nbRulesSCCs = 0;
		for (Dpairs S : SCCs) {
			int nb = S.size();
			nbRulesSCCs += nb;
			if (minRulesSCC < 0 || nb < minRulesSCC)
				minRulesSCC = nb;
			if (maxRulesSCC < nb)
				maxRulesSCC = nb;
		}
		int nbSCC = SCCs.size();
		s.append("\n* " + nbSCC + " SCC(s)");
		if (nbSCC > 0) {
			s.append(" -- nb rules: min=");
			s.append(minRulesSCC);
			s.append(" max=" + maxRulesSCC);
			s.append(" avg=" + (((float)nbRulesSCCs) / nbSCC));
		}

		// The initial loops in each SCC.
		s.append("\n* " +
				this.getSyntacticLoops(this.getDependencyGraph().getSCCs()).size() +
				" initial dependency pair(s)");

		// Function symbols.
		s.append("\n* " + FunctionSymbol.toStringStat());

		// Ending message.
		s.append("\n** END STATS for program: ");
		s.append(this.getName());

		return s.toString();
	}
}
