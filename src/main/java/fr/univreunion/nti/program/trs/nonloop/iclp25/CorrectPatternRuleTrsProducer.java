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

package fr.univreunion.nti.program.trs.nonloop.iclp25;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import fr.univreunion.nti.program.trs.RuleTrs;
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
 * in term rewriting. 
 *  
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class CorrectPatternRuleTrsProducer {

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
	 * Attempts to produce correct pattern rules
	 * by applying Prop. 9 of [Payet, WST'25] to
	 * the provided rules, which are supposed to
	 * be variable disjoint.
	 * 
	 * @param r1 a TRS rule to be checked
	 * (it corresponds to the rule <code>r</code>
	 * of Prop. 9)
	 * @param r2 a TRS rule to be checked
	 * (it corresponds to the rule <code>r'</code>
	 * of Prop. 9 and is supposed to be variable
	 * disjoint from <code>r1</code>)
	 * @return a collection consisting of the
	 * pattern rules produced by Prop. 9
	 * (empty if nothing could be produced)
	 */
	public static Collection<PatternRuleTrsIclp25> getCorrectPatternRules(
			RuleTrs r1, RuleTrs r2) {
		// It is supposed that r1 is the rule r
		// of Prop. 9 and r2 is the rule r' of
		// Prop. 9.
		// It is supposed that r1 and r2 are
		// variable disjoint.

		// The collection to be returned at the end.
		LinkedList<PatternRuleTrsIclp25> result = new LinkedList<>();

		FunctionSymbol f = r1.getLeft().getRootSymbol();
		Term v1 = r1.getRight();

		// We want the context c of Prop. 9
		// to be non empty. Hence, we forbid
		// the case where v1 is a variable.
		if (v1 instanceof Variable) return result;

		// We consider all possible candidates for the
		// subterm c(x_1,...,x_m) of v in Prop. 9.
		for (Position p : v1) {
			Term v1_p = v1.get(p);
			if (!(v1_p instanceof Variable) && v1_p.getRootSymbol() == f) {
				// We want the context c of Prop. 9
				// to be non empty. Hence, we forbid
				// the case where v1_p is a variable.
				PatternRuleTrsIclp25 r = getCorrectPatternRulesAux(r1, r2, p, v1_p);
				if (r != null) result.add(r);
			}
		}

		return result;
	}

	/**
	 * Attempts to produce a correct pattern rule
	 * by applying Prop. 9 of [Payet, WST'25] to
	 * the provided rules, which are supposed to
	 * be variable disjoint.
	 * 
	 * The provided term <code>v1_p</code> is a
	 * non-variable subterm of the right-hand side of
	 * <code>r1</code>. It corresponds to a candidate
	 * for the subterm <code>c(x_1,...,x_m)</code> of
	 * <code>v</code> in Prop. 9.
	 * 
	 * @param r1 a TRS rule to be checked
	 * (it corresponds to the rule <code>r</code>
	 * of Prop. 9)
	 * @param r2 a TRS rule to be checked
	 * (it corresponds to the rule <code>r'</code>
	 * of Prop. 9 and is supposed to be variable
	 * disjoint from <code>r1</code>)
	 * @param p a non-variable position in the
	 * right-hand side of <code>r1</code>
	 * @param v1_p the subterm of the right-hand
	 * of <code>r1</code> at position <code>p</code>
	 * @return the pattern rule produced by Prop. 9
	 * from the provided elements, or <code>null</code>
	 * if no pattern rule could be produced
	 */
	private static PatternRuleTrsIclp25 getCorrectPatternRulesAux(
			RuleTrs r1, RuleTrs r2, Position p, Term v1_p) {
		// It is supposed that r1 is the rule r
		// of Prop. 9 and r2 is the rule r' of
		// Prop. 9.
		// It is supposed that r1 and r2 are
		// variable disjoint.
		// It is supposed that v1_p is a non-variable
		// subterm of the right-hand side of r1.

		Function u1 = r1.getLeft();
		Function u2 = r2.getLeft();

		// The pumping and closing substitutions
		// of the left-hand side of the returned
		// pattern rule.
		Substitution sigma = new Substitution();
		Substitution mu    = new Substitution();

		// The context c of Prop. 2 (we check
		// at the end if u1_c = u2_c = v1).
		Term u1_c = u1.shallowCopy();
		Term u2_c = u2.shallowCopy();

		// The variables that sigma maps to
		// themselves (we do not add mappings
		// x -> x to sigma).
		Set<Variable> id = new HashSet<>();

		// First, we complete sigma and mu.
		for (Position q : v1_p) {

			Term u1_q = u1.get(q);
			// We only consider positions of v1_p
			// that are also positions of u1.
			if (u1_q == null) return null;

			Term u2_q = u2.get(q);
			// We only consider positions of v1_p
			// that are also positions of u2.
			if (u2_q == null) return null;

			Term v1_p_q = v1_p.get(q);

			if (v1_p_q instanceof Variable) {
				Variable x = (Variable) v1_p_q;

				// We complete sigma.
				if (!id.contains(x)) {
					Term t_x = sigma.get(x);
					if (t_x == null) {
						// Here, x \not\in Dom(sigma) and
						// x has not been met before.
						if (x == u1_q) id.add(x);
						else {
							// We add x -> u1_q to sigma, but
							// only if x occurs in u1_q and is
							// its only variable.
							Set<Variable> vars_u1_q = u1_q.getVariables();
							if (vars_u1_q.size() != 1 || !vars_u1_q.contains(x))
								return null;
							sigma.add(x, u1_q);
						}
					}
					else if (!t_x.deepEquals(u1_q))
						// Here, x \in Dom(sigma).
						return null;
				}
				else if (u1_q != x)
					// Here, sigma maps x to itself.
					return null;

				// We complete mu.
				Term mu_x = mu.get(x);
				if (mu_x == null) {
					// Here, x \not\in Dom(mu).
					// We add x -> u2_q to mu.
					if (x != u2_q) mu.add(x, u2_q);
					// Note: in principle, the test above
					// is always true because r1 and r2 are
					// variable disjoint.
					// If r1 and r2 are not variable disjoint,
					// then we should also have an id set for
					// mu (as for sigma above), in order to
					// keep track of mappings of the form
					// x -> x met before.
				}
				else if (!mu_x.deepEquals(u2_q))
					// Here, x \in Dom(mu).
					return null;

				// We complete c.
				if (u1_q != x) u1_c = u1_c.replace(q, x);
				if (u2_q != x) u2_c = u2_c.replace(q, x);
			}
		}

		// Then, we check whether sigma is suitable
		// and u1 corresponds to the same context c
		// as u2 and v1.
		if (!isSuitable(sigma) || !u1_c.deepEquals(u2_c) || !u1_c.deepEquals(v1_p))
			return null;

		// Finally, we consider the context c' of Prop. 9.
		Variable x1 = new Variable();
		Term c_prime = r1.getRight().replace(p, x1);
		// We check whether c' is ground.
		if (1 < c_prime.getVariables().size()) return null;

		// Here, the pair (r1,r2) satisfies the conditions
		// of Prop. 9 of [Payet, WST'25]. Hence, we can
		// produce a pattern rule from it.

		// The pumping and closing substitutions
		// of the right-hand side of the produced
		// pattern rule.
		Substitution rho = new Substitution();
		rho.add(x1, c_prime);
		Substitution nu = new Substitution();
		Map<Term, Term> copies = new HashMap<>();
		nu.add(x1, r2.getRight().deepCopy(copies));

		return PatternRuleTrsIclp25.getInstance(
				SimplePatternTerm.getInstance(v1_p.deepCopy(copies),
						sigma.deepCopy(copies), mu.deepCopy(copies)),
				SimplePatternTerm.getInstance(x1, rho, nu),
				0);
	}

	/**
	 * Produces the pattern rule
	 * <code>left^* -> right^*</code>,
	 * where <code>left -> right</code> is
	 * the provided TRS rule <code>r</code>.
	 * 
	 * The produced pattern rule is correct
	 * w.r.t. <code>r</code>.
	 * 
	 * @param r a TRS rule from which a correct
	 * pattern rule is produced
	 * @return a pattern rule which is correct
	 * w.r.t. <code>r</code>
	 */
	public static PatternRuleTrsIclp25 getCorrectPatternRules2(RuleTrs r) {
		// If r = (left -> right) then we produce
		// the pattern rule (left^* -> right^*).
		SimplePatternTerm left  = SimplePatternTerm.getInstance(r.getLeft());
		SimplePatternTerm right = SimplePatternTerm.getInstance(r.getRight());

		return PatternRuleTrsIclp25.getInstance(left, right, 0);
	}

	/**
	 * Considers the following situations:
	 * <ol>
	 * <li>
	 * <code>r1 = c'(c(s, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2) -> c(x2, c1^b(y2))</code>
	 * </li>
	 * <li>
	 * <code>r1 = c'(c(s, x1, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2, z2) -> c(x2, c1^b(y2), z2)</code>
	 * </li>
	 * </ol>
	 * where
	 * <code>x1, x2, y2, z2</code> are variables,
	 * <code>x2, y2, z2</code> are distinct and 
	 * do not occur in <code>c', c, c1</code>,
	 * <code>x1</code> does not occur in
	 * <code>c', c, c1, s</code>,
	 * <code>a, b</code> are non-zero naturals.
	 * 
	 * @param r1 a TRS rule to be checked
	 * @param r2 a TRS rule to be checked
	 * @return a collection consisting of the
	 * pattern rules
	 * <code>c'(c(c1^{a,0}(s), y2)) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * or
	 * <code>c'(c(c1^{a,0}(s), y2, c1^{b,0}(y2))) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * for all possible contexts c'
	 * (empty if nothing could be produced)
	 */
	public static Collection<PatternRuleTrsIclp25> getCorrectPatternRules3(
			RuleTrs r1, RuleTrs r2) {

		// We only consider the following particular case:
		// - c and c1 are ground
		// - c' consists of only one occurrence of \square_1.

		// The collection to be returned at the end.
		LinkedList<PatternRuleTrsIclp25> result = new LinkedList<>();

		Function u1 = r1.getLeft();

		// We consider all possible candidates for
		// the subterm c(s,x_1) or c(s,x_1,x_1) of
		// the left-hand side of r1.
		for (Position q : u1) {
			Term u1_q = u1.get(q);
			if (!(u1_q instanceof Variable)) {
				// We want the context c to be non empty.
				// Hence, we forbid the case where u1_q
				// is a variable.
				PatternRuleTrsIclp25 r = getCorrectPatternRules3Aux(r1, r2, q, u1_q);
				if (r != null) result.add(r);
			}
		}

		return result;
	}

	/**
	 * Considers the following situations:
	 * <ol>
	 * <li>
	 * <code>r1 = c'(c(s, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2) -> c(x2, c1^b(y2))</code>
	 * </li>
	 * <li>
	 * <code>r1 = c'(c(s, x1, x1)) -> t</code> and
	 * <code>r2 = c(c1^a(x2), y2, z2) -> c(x2, c1^b(y2), z2)</code>
	 * </li>
	 * </ol>
	 * where
	 * <code>x1, x2, y2, z2</code> are variables,
	 * <code>x2, y2, z2</code> are distinct and 
	 * do not occur in <code>c', c, c1</code>,
	 * <code>x1</code> does not occur in
	 * <code>c', c, c1, s</code>,
	 * <code>a, b</code> are non-zero naturals.
	 * 
	 * The provided term <code>u1_q</code> is a
	 * non-variable subterm of the left-hand side of
	 * <code>r1</code>. It corresponds to a candidate
	 * for the subterm <code>c(s,x_1)</code> or
	 * <code>c(s,x_1,x_1)</code>.
	 * 
	 * @param r1 a TRS rule to be checked
	 * @param r2 a TRS rule to be checked
	 * @param q a non-variable position in the
	 * left-hand side of <code>r1</code>
	 * @param u1_q the subterm of the left-hand
	 * of <code>r1</code> at position <code>q</code>
	 * @return the pattern rule 
	 * <code>c'(c(c1^{a,0}(s), y2)) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * or
	 * <code>c'(c(c1^{a,0}(s), y2, c1^{b,0}(y2))) -> t*{x1 -> c1^{b,0}(y2)}</code>
	 * depending on the situation, or <code>null</code>
	 * if no pattern rule could be produced
	 */
	private static PatternRuleTrsIclp25 getCorrectPatternRules3Aux(
			RuleTrs r1, RuleTrs r2, Position q, Term u1_q) {

		// We only consider the following particular case:
		// - c and c1 are ground
		// - c' consists of only one occurrence of \square_1.

		// It is supposed that u1_q is a non-variable
		// subterm of the left-hand side of r1.

		Function u2   = r2.getLeft();
		Term     v2   = r2.getRight();

		FunctionSymbol f = u1_q.getRootSymbol();
		if (u2.getRootSymbol() != f || v2.getRootSymbol() != f)
			return null;

		// The context c we are looking
		// for (we check at the end if
		// c_u1 = c_u2 = c_v2).
		Term c_u1 = u1_q.shallowCopy();
		Term c_u2 = u2.shallowCopy();
		Term c_v2 = v2.shallowCopy();

		// The variables x1, x2, y2, z2
		// we are looking for.
		Variable x1 = null;
		Variable x2 = null;
		Variable y2 = null;
		Variable z2 = null;
		// The term s we are looking for.
		Term s = null;
		// The context c1 we are looking for.
		Term c1 = null;
		// The exponents a,b we are looking for.
		int a = -1;
		int b = -1;

		// First, we look for x2 and z2 in v2.
		for (Position p : v2) {
			Term v2_p = v2.get(p);
			if (v2_p instanceof Variable) {
				// Here, v2_p should be x2 or z2.

				Term u1_q_p = u1_q.get(p);
				// We only consider positions of v2
				// that are also positions of u1.
				if (u1_q_p == null) continue;

				Term u2_p = u2.get(p);
				// We only consider positions of v2
				// that are also positions of u2.
				if (u2_p == null) continue;

				if (u2_p instanceof Variable) {
					// Here, v2_p should be z2.
					if (u2_p == v2_p) {
						if (z2 == null) {
							// Here, z2 had not been found already.
							// It must be distinct from x2.
							if ((x2 == null || x2 != v2_p) && u1_q_p instanceof Variable) {
								z2 = (Variable) v2_p;
								x1 = (Variable) u1_q_p;
							}
							else return null;
						}
						else if (v2_p != z2 || u1_q_p != x2) return null;
					}
					else return null;
					// We complete c.
					if (u1_q_p != z2) c_u1 = c_u1.replace(p, z2);
				}
				else {
					// Here, v2_p should be x2.
					Variable x_p = (Variable) v2_p;
					int[] a_p = new int[1];
					Term c1_p = PatternUtils.getContext(u2_p, x_p, a_p);
					if (c1_p != null) {
						if (x2 == null ) {
							// Here, x2 had not been found already.
							// It must be distinct from z2.
							if (z2 == null || z2 != x_p) {
								// We only consider the case where s is ground.
								x2 = x_p;
								c1 = c1_p;
								a = a_p[0];
								s = u1_q_p;
							}
							else return null;
						}
						else if (x_p != x2 || !c1_p.deepEquals(c1) ||
								a_p[0] != a || !u1_q_p.deepEquals(s))
							return null;
					}
					else return null;
					// We complete c.
					if (u1_q_p != x2) c_u1 = c_u1.replace(p, x2);
					if (u2_p != x2) c_u2 = c_u2.replace(p, x2);
				}
			}
		}

		// Here, we are sure that if z2 has been determined
		// then it is distinct from x2.
		// However, we must ensure that s and x2 have been
		// determined.
		if (s == null || x2 == null) return null;

		// Then, we look for y2.
		for (Position p : u2) {
			Term u2_p = u2.get(p);
			if (u2_p instanceof Variable && u2_p != x2 && u2_p != z2) {
				// Here, u2_p should be y2.
				// Moreover, y2 must be distinct from x2 and z2.

				Term u1_q_p = u1_q.get(p);
				// We only consider positions of u2 that
				// are also positions of u1.
				// Moreover, u1_p should be a variable.
				if (!(u1_q_p instanceof Variable)) return null;

				Term v2_p = v2.get(p);
				// We only consider positions of u2
				// that are also positions of v2.
				if (v2_p == null) return null;

				Variable y_p = (Variable) u2_p;
				int[] b_p = new int[1];
				Term c1_p = PatternUtils.getContext(v2_p, y_p, b_p);
				if (c1_p != null && c1_p.isVariantOf(c1)) {
					if (y2 == null) {
						// Here, y2 had not been found already.
						y2 = y_p;
						b = b_p[0];
						if (x1 == null) x1 = (Variable) u1_q_p;
						else if (u1_q_p != x1) return null;
					}
					else if (y_p != y2 || b_p[0] != b || u1_q_p != x1)
						return null;
				}
				else return null;
				// We complete c.
				if (u1_q_p != y2) c_u1 = c_u1.replace(p, y2);
				if (v2_p != y2) c_v2 = c_v2.replace(p, y2);
			}
		}

		// Finally, we check if we have found x1 and y2.
		// We also check if x1 occurs in s and if u1
		// corresponds to the same context c as u2 and v2.
		if (x1 == null || y2 == null ||
				s.contains(x1) ||
				!c_u1.deepEquals(c_u2) || !c_u1.deepEquals(c_v2))
			return null;
		// We know here that x2, y2 and z2 are distinct variables.

		// We also compute c_prime.
		Variable hole = new Variable();
		Term c_prime = r1.getLeft().replace(q, hole);
		// We check if c_prime contains x1, x2, y2 or z2.
		Set<Variable> vars = new HashSet<>();
		vars.add(x1); vars.add(x2); vars.add(y2);
		if (z2 != null) vars.add(z2);
		vars.retainAll(c_prime.getVariables());
		if (!vars.isEmpty()) return null;

		HatFunctionSymbol symb = HatFunctionSymbol.getInstance(c1, x2);
		// The pattern substitution on the left-hand side
		// of the produced pattern rule:
		Substitution theta_l = new Substitution();
		theta_l.add(x2, new HatFunction(symb, s, a, 0));		
		if (z2 != null)
			theta_l.add(z2, new HatFunction(symb, y2, b, 0));
		// The pattern substitution on the right-hand side
		// of the produced pattern rule:
		Substitution theta_r = new Substitution();
		theta_r.add(x1, new HatFunction(symb, y2, b, 0));

		Map<Term, Term> copies = new HashMap<>();
		SimplePatternSubstitution eta_l = SimplePatternSubstitution.getInstance(theta_l.deepCopy(copies));
		SimplePatternSubstitution eta_r = SimplePatternSubstitution.getInstance(theta_r.deepCopy(copies));
		if (eta_l != null)
			return PatternRuleTrsIclp25.getInstance(
					SimplePatternTerm.getInstance(c_prime.replace(q, c_u2).deepCopy(copies), eta_l),
					SimplePatternTerm.getInstance(r1.getRight().deepCopy(copies), eta_r),
					0);

		return null;
	}

	/**
	 * Considers the following situation:
	 * <ol>
	 * <li>
	 * <code>r1 = (c(s1, s2) -> t)</code>
	 * </li>
	 * <li>
	 * <code>r2 = (c(c1^a(x2), y2) -> c(x2, y2))</code>
	 * </li>
	 * <li>
	 * <code>r3 = (c(x3, c1^b(y3)) -> c(x3, y3))</code>
	 * </li>
	 * </ol>
	 * where <code>s1, s2, t</code> are terms,
	 * <code>c</code> is a 2-context,
	 * <code>c1</code> is a 1-context,
	 * <code>x2, y2</code> are distinct variables
	 * that do not occur in <code>c, c1</code>,
	 * <code>x3, y3</code> are distinct variables
	 * that do not occur in <code>c, c1</code>,
	 * and <code>a, b</code> are naturals.
	 * 
	 * @param r1 a TRS rule to be checked
	 * @param r2 a TRS rule to be checked
	 * @param r3 a TRS rule to be checked
	 * @return the pattern rule
	 * <code>c(c1^{a,0}(s1), c1^{b,0}(s2)) -> t^*</code>,
	 * or <code>null</code> if no pattern rule could be
	 * produced
	 */
	public static PatternRuleTrsIclp25 getCorrectPatternRules4(
			RuleTrs r1, RuleTrs r2, RuleTrs r3) {

		// We only consider the particular case
		// where c is a context of the form
		// f(square_1,square_2) where f is 
		// a function symbol.

		Function u1 = r1.getLeft();
		Function u2 = r2.getLeft();
		Function u3 = r3.getLeft();
		Term v2     = r2.getRight();
		Term v3     = r3.getRight();

		FunctionSymbol f = u1.getRootSymbol();
		if (u2.getRootSymbol() != f || v2.getRootSymbol() != f
				|| u3.getRootSymbol() != f || v3.getRootSymbol() != f)
			return null;

		// From here, u1 has the form f(...), 
		// r2 = (u2 -> v2) has the form f(...) -> f(...) and
		// r3 = (u3 -> v3) has the form f(...) -> f(...).
		// In particular, v2 and v3 are functions,
		// but we check anyway.
		if (!(v2 instanceof Function) || !(v3 instanceof Function))
			return null;

		int m = f.getArity();
		if (2 == m) {
			Term u1_0 = u1.getChild(0); // s1
			Term u1_1 = u1.getChild(1); // s2
			Term u2_0 = u2.getChild(0); // c1^a(x2)
			Term u2_1 = u2.getChild(1); // y2
			Term v2_0 = ((Function) v2).getChild(0); // x2
			Term v2_1 = ((Function) v2).getChild(1); // y2
			Term u3_0 = u3.getChild(0); // x3
			Term u3_1 = u3.getChild(1); // c1^b(y3)
			Term v3_0 = ((Function) v3).getChild(0); // x3
			Term v3_1 = ((Function) v3).getChild(1); // y3
			if (v2_0 instanceof Variable && v2_1 instanceof Variable && 
					v2_0 != v2_1 &&
					v3_0 instanceof Variable && v3_1 instanceof Variable &&
					v3_0 != v3_1 &&
					u2_1 instanceof Variable && u2_1 == v2_1 &&
					u3_0 instanceof Variable && u3_0 == v3_0) {

				Variable x2 = (Variable) v2_0;
				int[] a_u2 = new int[1];
				Term c1_u2 = PatternUtils.getContext(u2_0, x2, a_u2);
				if (c1_u2 == null) return null;

				Variable y3 = (Variable) v3_1;
				int[] a_u3 = new int[1];
				Term c1_u3 = PatternUtils.getContext(u3_1, y3, a_u3);
				if (c1_u3 == null) return null;

				if (!c1_u2.isVariantOf(c1_u3)) return null;

				HatFunctionSymbol symb = HatFunctionSymbol.getInstance(c1_u2, x2);
				Substitution theta = new Substitution();
				theta.add(x2, new HatFunction(symb, u1_0, a_u2[0], 0));
				theta.add(y3, new HatFunction(symb, u1_1, a_u3[0], 0));

				Map<Term, Term> copies = new HashMap<>();
				List<Term> args = new LinkedList<>();
				args.add(x2.deepCopy(copies));
				args.add(y3.deepCopy(copies));

				SimplePatternSubstitution eta = SimplePatternSubstitution.getInstance(theta.deepCopy(copies));
				if (eta != null)
					return PatternRuleTrsIclp25.getInstance(
							SimplePatternTerm.getInstance(new Function(f, args), eta),
							SimplePatternTerm.getInstance(r1.getRight().deepCopy(copies)),
							0);
			}
		}

		return null;
	}
}
