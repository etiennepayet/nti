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

package fr.univreunion.nti.program.lp.nonloop;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.lp.RuleLp;
import fr.univreunion.nti.term.Function;
import fr.univreunion.nti.term.FunctionSymbol;
import fr.univreunion.nti.term.HatFunction;
import fr.univreunion.nti.term.Position;
import fr.univreunion.nti.term.Substitution;
import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.HatFunctionSymbol;
import fr.univreunion.nti.term.pattern.PatternUtils;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternTerm;

/**
 * A set of methods for inferring correct pattern rules
 * in logic programming. 
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class CorrectPatternRuleLpProducer {
	
	/**
	 * Checks whether <code>sigma</code> is
	 * suitable.
	 * 
	 * @param sigma a substitution
	 * @return <code>true</code> iff
	 * <code>sigma</code> is suitable
	 */
	private static boolean isSuitable(Substitution sigma) {

		Set<Variable> dom = sigma.getDomain();

		for (Map.Entry<Variable, Term> e : sigma) {
			Variable x = e.getKey();

			// We check whether x is the only
			// variable of Dom(sigma) that occurs in
			// sigma(x).

			Set<Variable> vars = e.getValue().getVariables();
			vars.retainAll(dom);

			if (vars.size() != 1)
				// Here, no variable of dom occurs in s or
				// at least two variables of dom occur in s.
				return false;
			// Here, exactly one variable of dom occurs in s.
			// We check whether it is x.
			if (vars.iterator().next() != x) return false;
		}

		return true;
	}
	
	/**
	 * Attempts to produce a pattern rule by
	 * applying Prop. 2 of [Payet, ICLP'25]
	 * to the provided binary rule.
	 * 
	 * @param r a binary rule
	 * @return a pattern rule, or <code>null</code>
	 * if no pattern rule could be inferred from
	 * <code>r</code> 
	 */
	public static PatternRuleLp getCorrectBinary(RuleLp r) {
		// r is supposed to be binary, i.e.,
		// of the form left :- right.
		Function left  = r.getHead();
		Function right = r.getBody(0);

		// The pumping substitution of
		// the left-hand side of the
		// returned pattern rule.
		Substitution sigma_left  = new Substitution();
		// The pumping substitution of
		// the right-hand side of the
		// returned pattern rule.
		Substitution sigma_right = new Substitution();

		// First, we complete sigma_left
		// and sigma_right.
		for (Position p : left.dpos(right, true)) {
			Term left_p  = left.get(p);
			Term right_p = right.get(p);

			if (left_p instanceof Variable) {
				Variable x = (Variable) left_p;
				Term t_x = sigma_right.get(x);
				if (t_x == null)
					// Here, x \not\in Dom(sigma_right).
					// We add x -> right_p to sigma_right.
					// We note that x != right_p necessarily
					// because (left_p, right_p) is a
					// disagreement pair.
					sigma_right.add(x, right_p);
				else if (!t_x.deepEquals(right_p))
					// Here, x \in Dom(sigma_right) and
					// sigma_right(x) != right_p.
					return null;
			}
			else if (right_p instanceof Variable) {
				Variable x = (Variable) right_p;
				Term t_x = sigma_left.get(x);
				if (t_x == null)
					// Here, x \not\in Dom(sigma_left).
					// We add x -> left_p to sigma_left.
					// We note that x != left_p necessarily
					// because (left_p, right_p) is a
					// disagreement pair.
					sigma_left.add(x, left_p);
				else if (!t_x.deepEquals(left_p))
					// Here, x \in Dom(sigma_left) and
					// sigma_left(x) != left_p.
					return null;
			}
			else
				return null;
		}

		// Then, we check whether sigma_left
		// and sigma_right are suitable.
		Set<Variable> dom = sigma_left.getDomain();
		dom.addAll(sigma_right.getDomain()); // dom = Dom(sigma_left) U Dom(sigma_right)
		if (!isSuitable(sigma_left) || !isSuitable(sigma_right))
			return null;

		Map<Term, Term> copies = new HashMap<>();
		return PatternRuleLp.getInstance(
				SimplePatternTerm.getInstance(left.deepCopy(copies),
						sigma_left.deepCopy(copies), new Substitution()),
				SimplePatternTerm.getInstance(right.deepCopy(copies),
						sigma_right.deepCopy(copies), new Substitution()),
				0);
	}


	/**
	 * Attempts to produce a pattern fact by
	 * applying Prop. 2 of [Payet, ICLP'25]
	 * to the provided binary rules.
	 * 
	 * @param r1 a fact to be checked
	 * @param r2 a binary rule to be checked
	 * @return the pattern rule <code>(p,e*)</code>
	 * of Prop. 2, or <code>null</code> if nothing
	 * could be produced from <code>(r1,r2)</code>
	 */
	public static PatternRuleLp getCorrectFact(
			RuleLp r1, RuleLp r2) {

		// It is supposed that r1 is a fact and
		// r2 is binary.

		Function u1 = r1.getHead();
		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);

		// The pumping and closing substitutions
		// of the returned pattern fact.
		Substitution sigma = new Substitution();
		Substitution mu = new Substitution();

		// The context c of Prop. 2 (we check
		// at the end if u1_c = u2_c = v2).
		Term u1_c = u1.shallowCopy();
		Term u2_c = u2.shallowCopy();

		// The variables that sigma maps to
		// themselves (we do not add mappings
		// x -> x to sigma).
		Set<Variable> id = new HashSet<>();

		// First, we complete sigma and mu.
		for (Position p : v2) {

			Term u1_p = u1.get(p);
			// We only consider positions of v2
			// that are also positions of u1.
			if (u1_p == null) return null;

			Term u2_p = u2.get(p);
			// We only consider positions of v2
			// that are also positions of u2.
			if (u2_p == null) return null;

			Term v2_p = v2.get(p);

			if (v2_p instanceof Variable) {
				Variable x = (Variable) v2_p;

				// We complete sigma.
				if (!id.contains(x)) {
					Term t_x = sigma.get(x);
					if (t_x == null) {
						// Here, x \not\in Dom(sigma) and
						// x has not been met before.
						if (x == u2_p) id.add(x);
						else {
							// We add x -> u2_p to sigma, but
							// only if x occurs in u2_p and is
							// its only variable.
							Set<Variable> vars_u2_p = u2_p.getVariables();
							if (vars_u2_p.size() != 1 || !vars_u2_p.contains(x))
								return null;
							sigma.add(x, u2_p);
						}
					}
					else if (!t_x.deepEquals(u2_p))
						// Here, x \in Dom(sigma).
						return null;
				}
				else if (u2_p != x)
					// Here, sigma maps x to itself.
					return null;

				// We complete mu.
				Term mu_x = mu.get(x);
				if (mu_x == null) {
					// Here, x \not\in Dom(mu).
					// We add x -> u1_p to mu.
					if (x != u1_p) mu.add(x, u1_p);
				}
				else if (!mu_x.deepEquals(u1_p))
					// Here, x \in Dom(mu).
					return null;

				// We complete c.
				if (u1_p != x) u1_c = u1_c.replace(p, x);
				if (u2_p != x) u2_c = u2_c.replace(p, x);
			}
		}

		// Then, we check whether sigma is suitable
		// and u1 corresponds to the same context c
		// as u2 and v2.
		if (!isSuitable(sigma) || !u1_c.deepEquals(u2_c) || !u1_c.deepEquals(v2))
			return null;

		// Here, the pair (r1,r2) satisfies the conditions
		// of Prop. 2 of [Payet, ICLP'25]. Hence, we can
		// produce a pattern fact from it.

		Map<Term, Term> copies = new HashMap<>();
		return PatternRuleLp.getInstance(
				SimplePatternTerm.getInstance(v2.deepCopy(copies),
						sigma.deepCopy(copies), mu.deepCopy(copies)),
				0);
	}
	
	/**
	 * Checks whether the pair <code>(r1, r2)</code> satisfies
	 * a particular case of Prop. 2 of [Payet, ICLP'25].
	 * 
	 * More precisely, checks whether <code>r1</code> is a fact
	 * of the form <code>q(t_1,...,t_m)</code> and <code>r2</code>
	 * has the form
	 * <code>q(c'_1[c_1[x_1]],...,c'_m[c_m[x_m]]) :- q(c'_1[x_1],...,c'_m[x_m])</code>,
	 * where <code>x_1,...,x_m</code> are distinct variables and
	 * <code>c_1,c'_1,...,c_m,c'_m</code> are ground 1-contexts.
	 * 
	 * Upon success, the fact <code>r1</code> is added to
	 * the provided set <code>facts</code>.
	 * 
	 * @param r1 a fact to be checked
	 * @param r2 a binary rule to be checked
	 * @return <code>null</code> if <code>(r1, r2)</code> does
	 * not have the form indicated above, or the pattern rule
	 * <code>(p, e*)</code> of Prop. 2 otherwise
	 */
	/*
	private PatternRuleLp getCorrectFact(
			RuleLp r1, RuleLp r2) {

		// It is supposed that r1 is a fact and
		// r2 is binary.

		Function u1 = r1.getHead();
		FunctionSymbol q = u1.getRootSymbol();

		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);

		// We check whether u2 and v2 have the form q(...).
		if (u2.getRootSymbol() != q || v2.getRootSymbol() != q)
			return null;

		// From here, r2 has the form q(...) :- q(...).
		int n = q.getArity();

		// The pumping and closing substitutions
		// of the returned pattern rule.
		Substitution sigma = new Substitution();
		Substitution mu = new Substitution();

		// We check whether u2 has the form
		// q(c'_1[c_1[x_1]],...,c'_m[c_m[x_m]]) and
		// v2 has the form q(c'_1[x_1],...,c'_m[x_m]).
		// Then, the context c of Prop. 2 [Payet, ICLP'25]
		// is q(c'_1(square),...,c'_m(square)).
		HashSet<Variable> vars = new HashSet<>();
		Substitution theta_i = new Substitution();
		for (int i = 0; i < n; i++) {
			Term u2_i = u2.getChild(i);
			Term v2_i = v2.getChild(i);

			// The variables of v2_i:
			Set<Variable> vars_i = v2_i.getVariables();

			// We check whether there is only
			// one variable in v2_i.
			if (vars_i.size() != 1) return null;

			// From here, v2_i = c'_i[x_i] where
			// c'_i is a ground 1-context.
			// In particular, vars_i contains 
			// exactly one element.

			// We verify that the only variable x_i
			// of v2_i is the only variable of u2_i and
			// that x_i does not occur in {x_1,...,x_{i-1}}.
			Variable x_i = vars_i.iterator().next();
			if (!vars_i.equals(u2_i.getVariables()) || !vars.add(x_i)) return null;

			// We verify that v2_i is more general
			// than u2_i.
			if (!v2_i.isMoreGeneralThan(u2_i, theta_i)) return null;

			Term t_i = theta_i.getOrDefault(x_i, x_i);
			if (x_i != t_i) sigma.add(x_i, t_i);
			Term u_1_i = u1.getChild(i);
			if (x_i != u_1_i) mu.add(x_i, u_1_i);

			theta_i.clear();
		}

		// Here, the pair (r1,r2) satisfies the conditions
		// of Prop. 2 of [Payet, ICLP'25]. Hence, we can
		// produce a pattern rule from it.

		// The path to the generated pattern rule. 
		Path path = new Path(r1);
		path.addLast​(r2);

		Map<Term, Term> copies = new HashMap<>();
		return PatternRuleLp.getInstance(
				SimplePatternTerm.getInstance(v2.deepCopy(copies),
						sigma.deepCopy(copies), mu.deepCopy(copies)),
				0,
				path);
	}
	 */

	/**
	 * Considers the following situations:
	 * <ol>
	 * <li>
	 * <code>r1 = c(s, x')</code> and
	 * <code>r2 = c(c1^a(x), y) :- c(x, c1^b(y))</code>
	 * </li>
	 * <li>
	 * <code>r1 = c(s, x', x')</code> and
	 * <code>r2 = c(c1^a(x), y, z) :- c(x, c1^b(y), z)</code>
	 * </li>
	 * </ol>
	 * where
	 * <code>x',x,y,z</code> are variables,
	 * <code>x,y,z</code> are distinct,
	 * <code>s</code> is a ground term,
	 * <code>c,c1</code> are ground 1-contexts and
	 * <code>a,b</code> are non-zero naturals.
	 * 
	 * @param r1 a fact
	 * @param r2 a binary rule
	 * @return the pattern rule 
	 * <code>c(c1^{a,0}(s), y) :- e^*</code> or
	 * <code>c(c1^{a,0}(s), y, c1^{b,0}(y)) :- e^*</code>
	 * depending on the situation, or <code>null</code>
	 * if no pattern rule could be produced from the
	 * provided fact and binary rule
	 */	
	public static PatternRuleLp getCorrectFact2(
			RuleLp r1, RuleLp r2) {

		// It is supposed that r1 is a fact
		// and r2 is binary.

		Function u1 = r1.getHead();
		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);

		// The context c we are looking
		// for (we check at the end if
		// c_u1 = c_u2 = c_v2).
		Term c_u1 = u1.shallowCopy();
		Term c_u2 = u2.shallowCopy();
		Term c_v2 = v2.shallowCopy();

		// The variables x, y, z, x'
		// we are looking for.
		Variable x = null;
		Variable y = null;
		Variable z = null;
		Variable xx = null;
		// The term s we are looking for.
		Term s = null;
		// The context c1 we are looking for.
		Term c1 = null;
		// The exponents a,b we are looking for.
		int a = -1;
		int b = -1;

		// First, we look for x and z in v2.
		for (Position p : v2) {
			Term v2_p = v2.get(p);
			if (v2_p instanceof Variable) {
				// Here, v2_p should be x or z.

				Term u1_p = u1.get(p);
				// We only consider positions of v2
				// that are also positions of u1.
				if (u1_p == null) continue;

				Term u2_p = u2.get(p);
				// We only consider positions of v2
				// that are also positions of u2.
				if (u2_p == null) continue;
				
				if (u2_p instanceof Variable) {
					// Here, v2_p should be z.
					if (u2_p == v2_p) {
						if (z == null) {
							if (u1_p instanceof Variable) {
								z = (Variable) v2_p;
								xx = (Variable) u1_p;
							}
							else return null;
						}
						else if (v2_p != z || u1_p != xx) return null;
					}
					else return null;
					// We complete c.
					if (u1_p != z) c_u1 = c_u1.replace(p, z);
				}
				else {
					// Here, v2_p should be x.
					Variable x_p = (Variable) v2_p;
					int[] a_p = new int[1];
					Term c1_p = PatternUtils.getContext(u2_p, x_p, a_p);
					if (c1_p != null) {
						if (x == null) {
							// Here, x had not been found already.
							if (u1_p.isGround()) {
								x = x_p;
								c1 = c1_p;
								a = a_p[0];
								s = u1_p;
							}
							else return null;
						}
						else if (x_p != x || !c1_p.deepEquals(c1) ||
								a_p[0] != a || !u1_p.deepEquals(s))
							return null;
					}
					else return null;
					// We complete c.
					if (u1_p != x) c_u1 = c_u1.replace(p, x);
					if (u2_p != x) c_u2 = c_u2.replace(p, x);
				}
			}
		}

		// Here, at least x should be determined.
		if (x == null) return null;

		// Then, we look for y.
		for (Position p : u2) {
			Term u2_p = u2.get(p);
			if (u2_p instanceof Variable && u2_p != x && u2_p != z) {
				// Here, u2_p should be y.

				Term u1_p = u1.get(p);
				// We only consider positions of u2 that
				// are also positions of u1.
				// Moreover, u1_p should be a variable.
				if (!(u1_p instanceof Variable)) return null;
				
				Term v2_p = v2.get(p);
				// We only consider positions of u2
				// that are also positions of v2.
				if (v2_p == null) return null;
				
				Variable y_p = (Variable) u2_p;
				int[] b_p = new int[1];
				Term c1_p = PatternUtils.getContext(v2_p, y_p, b_p);
				if (c1_p != null && c1_p.isVariantOf(c1)) {
					if (y == null) {
						// Here, y had not been found already.
						y = y_p;
						b = b_p[0];
						if (xx == null) xx = (Variable) u1_p;
						else if (u1_p != xx) return null;
					}
					else if (y_p != y || b_p[0] != b || u1_p != xx)
						return null;
				}
				else return null;
				// We complete c.
				if (u1_p != y) c_u1 = c_u1.replace(p, y);
				if (v2_p != y) c_v2 = c_v2.replace(p, y);
			}
		}

		// Finally, we check if we have found x and y
		// and if u1 corresponds to the same context
		// c as u2 and v2.
		if (x == null || y == null ||
				!c_u1.deepEquals(c_u2) || !c_u1.deepEquals(c_v2))
			return null;

		HatFunctionSymbol symb = HatFunctionSymbol.getInstance(c1, x);
		Substitution theta = new Substitution();
		theta.add(x, new HatFunction(symb, s, a, 0));		
		if (z != null)
			theta.add(z, new HatFunction(symb, y, b, 0));

		Map<Term, Term> copies = new HashMap<>();
		SimplePatternSubstitution eta = SimplePatternSubstitution.getInstance(theta.deepCopy(copies));
		if (eta != null)
			return PatternRuleLp.getInstance(
					SimplePatternTerm.getInstance(c_u2.deepCopy(copies), eta),
					0);
		
		return null;
	}

	/**
	 * Considers the following situations:
	 * <ol>
	 * <li>
	 * <code>r1 = p(s, x')</code> and
	 * <code>r2 = p(c^a(x), y) :- p(x, c^b(y))</code>
	 * </li>
	 * <li>
	 * <code>r1 = p(s, x', x')</code> and
	 * <code>r2 = p(c^a(x), y, z) :- p(x, c^b(y), z)</code>
	 * </li>
	 * </ol>
	 * where
	 * <code>x',x,y,z</code> are variables,
	 * <code>x,y,z</code> are distinct,
	 * <code>s</code> is a term that does not
	 * contain <code>x'</code>,
	 * <code>c</code> is a ground 1-context and
	 * <code>a,b</code> are naturals.
	 * 
	 * @param r1 a fact
	 * @param r2 a binary rule
	 * @return the pattern rule 
	 * <code>p(c^{a,0}(s), y) :- e^*</code> or
	 * <code>p(c^{a,0}(s), y, c^{b,0}(y)) :- e^*</code>
	 * depending on the situation
	 */
	/*
	public static PatternRuleLp getCorrectFact2(
			RuleLp r1, RuleLp r2) {

		// It is supposed that r1 is a fact and
		// r2 is binary.

		Function u1 = r1.getHead();
		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);

		FunctionSymbol p = u1.getRootSymbol();
		if (u2.getRootSymbol() != p || v2.getRootSymbol() != p)
			return null;

		// From here, u1 has the form p(...) and 
		// u2 :- v2 has the form p(...) :- p(...).

		int m = p.getArity();
		if (2 <= m && m <= 3) {
			Term u1_0 = u1.getChild(0);
			Term u2_0 = u2.getChild(0);
			Term v2_0 = v2.getChild(0);
			Term u1_1 = u1.getChild(1);
			Term u2_1 = u2.getChild(1);
			Term v2_1 = v2.getChild(1);
			if (!(u2_0 instanceof Variable) && v2_0 instanceof Variable && 
					u2_1 instanceof Variable && !(v2_1 instanceof Variable) &&
					u2_1 != v2_0 && u1_1 instanceof Variable) {

				if (u1_0.getVariables().contains(u1_1)) return null;

				Variable x = (Variable) v2_0;
				int[] a_u2 = new int[1];
				Term c_u2 = PatternUtils.getContext(u2_0, x, a_u2);

				Variable y = (Variable) u2_1;
				int[] a_v2 = new int[1];
				Term c_v2 = PatternUtils.getContext(v2_1, y, a_v2);

				if (c_u2 != null && c_v2 != null && c_u2.isVariantOf(c_v2)) {

					HatFunctionSymbol symb = HatFunctionSymbol.getInstance(c_u2, x);
					Substitution theta = new Substitution();
					theta.add(x, new HatFunction(symb, u1_0, a_u2[0], 0));

					Map<Term, Term> copies = new HashMap<>();
					List<Term> args = new LinkedList<>();
					args.add(x.deepCopy(copies));
					args.add(y.deepCopy(copies));

					if (m == 3) {
						Term u1_2 = u1.getChild(2);
						Term u2_2 = u2.getChild(2);
						Term v2_2 = v2.getChild(2);
						if (u2_2 instanceof Variable && u2_2 == v2_2 &&
								u2_2 != u2_1 && u2_2 != v2_0 && u1_1 == u1_2) {

							Variable z = (Variable) u2_2;
							theta.add(z, new HatFunction(symb, y, a_v2[0], 0));
							args.add(z.deepCopy(copies));
						}
						else return null;
					}

					// The path to the generated pattern rule. 
					Path path = new Path(r1);
					path.addLast​(r2);

					SimplePatternSubstitution eta = SimplePatternSubstitution.getInstance(theta.deepCopy(copies));
					if (eta != null)
						return PatternRuleLp.getInstance(
								SimplePatternTerm.getInstance(new Function(p, args), eta),
								0,
								path);
				}
			}
		}

		return null;
	}
	 */

	/**
	 * Considers the following situation:
	 * <code>r1 = p(s1, s2)</code> and
	 * <code>r2 = p(c^a(x), y) :- p(x, y)</code>
	 * <code>r3 = p(x, c^b(y)) :- p(x, y)</code>
	 * where <code>s1, s2</code> are variable
	 * disjoint terms, <code>c</code> is a ground
	 * 1-context, <code>x, y</code> are distinct
	 * variables and <code>a, b</code> are naturals.
	 * 
	 * @param r1 a fact
	 * @param r2 a binary rule
	 * @param r3 a binary rule
	 * @return the pattern rule 
	 * <code>p(c^{a,0}(s1), c^{b,0}(s2)) :- e^*</code>,
	 * or <code>null</code> if no pattern rule could
	 * be produced from the provided  fact and binary
	 * rules
	 */
	public static PatternRuleLp getCorrectFact3(
			RuleLp r1, RuleLp r2, RuleLp r3) {

		// It is supposed that r1 is a fact and
		// r2,r3 are binary.

		Function u1 = r1.getHead();
		Function u2 = r2.getHead();
		Function v2 = r2.getBody(0);
		Function u3 = r3.getHead();
		Function v3 = r3.getBody(0);

		FunctionSymbol p = u1.getRootSymbol();
		if (u2.getRootSymbol() != p || v2.getRootSymbol() != p
				|| u3.getRootSymbol() != p || v3.getRootSymbol() != p)
			return null;

		// From here, u1 has the form p(...), 
		// u2 :- v2 has the form p(...) :- p(...) and
		// u3 :- v3 has the form p(...) :- p(...).

		int m = p.getArity();
		if (2 == m) {
			Term u1_0 = u1.getChild(0);
			Term u2_0 = u2.getChild(0);
			Term v2_0 = v2.getChild(0);
			Term u3_0 = u3.getChild(0);
			Term v3_0 = v3.getChild(0);
			Term u1_1 = u1.getChild(1);
			Term u2_1 = u2.getChild(1);
			Term v2_1 = v2.getChild(1);
			Term u3_1 = u3.getChild(1);
			Term v3_1 = v3.getChild(1);
			if (v2_0 instanceof Variable && v2_1 instanceof Variable && 
					v2_0 != v2_1 &&
					v3_0 instanceof Variable && v3_1 instanceof Variable &&
					v3_0 != v3_1 &&
					u2_1 instanceof Variable && u2_1 == v2_1 &&
					u3_0 instanceof Variable && u3_0 == v3_0) {

				// We check if vars(s1) is disjoint from vars(s2).
				if (u1_0.getVariables().removeAll(u1_1.getVariables()))
					return null;

				Variable x = (Variable) v2_0;
				int[] a_u2 = new int[1];
				Term c_u2 = PatternUtils.getContext(u2_0, x, a_u2);

				Variable y = (Variable) v3_1;
				int[] a_u3 = new int[1];
				Term c_u3 = PatternUtils.getContext(u3_1, y, a_u3);

				if (c_u2 != null && c_u3 != null && c_u2.isVariantOf(c_u3)) {

					HatFunctionSymbol symb = HatFunctionSymbol.getInstance(c_u2, x);
					Substitution theta = new Substitution();
					theta.add(x, new HatFunction(symb, u1_0, a_u2[0], 0));
					theta.add(y, new HatFunction(symb, u1_1, a_u3[0], 0));

					Map<Term, Term> copies = new HashMap<>();
					List<Term> args = new LinkedList<>();
					args.add(x.deepCopy(copies));
					args.add(y.deepCopy(copies));

					SimplePatternSubstitution eta = SimplePatternSubstitution.getInstance(theta.deepCopy(copies));
					if (eta != null)
						return PatternRuleLp.getInstance(
								SimplePatternTerm.getInstance(new Function(p, args), eta),
								0);
				}
			}
		}

		return null;
	}
}
