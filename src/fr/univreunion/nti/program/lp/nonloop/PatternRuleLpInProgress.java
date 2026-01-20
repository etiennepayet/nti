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
import java.util.Map;

import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;

/**
 * An intermediate structure used for applying the
 * operator T^{\pi}_{P,B} of [Payet, ICLP'25].
 * 
 * It is used in the method RuleLp.unfoldPattern(...).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PatternRuleLpInProgress {

	/**
	 * The pattern substitution computed so far
	 * during the unfolding.
	 */
	private final PatternSubstitution theta;
	
	/**
	 * The iteration of the unfolding operator at
	 * which this rule in progress is generated.
	 */
	private final int iteration;
		
	/**
	 * Builds a pattern rule in progress from
	 * the provided elements.
	 * 
	 * @param theta the pattern substitution
	 * computed so far during the unfolding
	 * @param iteration the iteration of the
	 * unfolding operator at which this rule
	 * in progress is generated
	 * @throws IllegalArgumentException if the
	 * given iteration is negative
	 */
	public PatternRuleLpInProgress(
			PatternSubstitution theta,
			int iteration) {
		
		if (iteration < 0)
			throw new IllegalArgumentException(
					"construction of a LP pattern rule in progress with a negative iteration");
		
		this.theta = theta;
		this.iteration = iteration;
	}
	
	/**
	 * Builds an empty pattern rule in progress
	 * from the provided elements.
	 * 
	 * @param iteration the iteration of the
	 * unfolding operator at which this rule
	 * in progress is generated
	 * @throws IllegalArgumentException if the
	 * given iteration is negative
	 */
	public PatternRuleLpInProgress(int iteration) {
		this(SimplePatternSubstitution.getInstance(), iteration);
	}
	
	/**
	 * Returns a deep copy of this rule in progress
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this rule in progress
	 */
	public PatternRuleLpInProgress deepCopy() {
		return this.deepCopy(new HashMap<>());
	}
	
	/**
	 * Returns a deep copy of this rule in progress
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * 
	 * The specified map is used to store subterm
	 * copies and is constructed incrementally.
	 * 
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @param copies a set of pairs <code>(s,t)</code>
	 * where the term <code>t</code> is a deep copy of
	 * <code>s</code>
	 * @return a deep copy of this rule in progress
	 */
	public PatternRuleLpInProgress deepCopy(Map<Term, Term> copies) {
		return new PatternRuleLpInProgress(
				this.theta.deepCopy(copies),
				this.iteration);
	}
	
	/**
	 * Returns the pattern substitution of
	 * this rule in progress.
	 * 
	 * @return the pattern substitution of
	 * this rule in progress
	 */
	public PatternSubstitution getPatternSubs() {
		return this.theta;
	}
	
	/**
	 * Returns the iteration of the unfolding operator
	 * at which this rule in progress is generated.
	 * 
	 * @return the iteration of the unfolding operator
	 * at which this rule in progress is generated
	 */
	public int getIteration() {
		return this.iteration;
	}
	
	/**
	 * Returns a string representation of this
	 * object relatively to the given set
	 * of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(V,s)</code>
	 * where <code>s</code> is the string associated to
	 * variable <code>V</code>
	 */
	public String toString(Map<Variable,String> variables) {
		return this.theta.toString(variables) +
				" -- iteration = " + this.iteration;
	}
	
	/**
	 * Returns a string representation of this object.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
