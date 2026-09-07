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

package fr.univreunion.nti.program.lp.patternunfolding;

import java.util.HashMap;
import java.util.Map;

import fr.univreunion.nti.term.Term;
import fr.univreunion.nti.term.Variable;
import fr.univreunion.nti.term.pattern.PatternSubstitution;
import fr.univreunion.nti.term.pattern.simple.SimplePatternSubstitution;

/**
 * An intermediate structure used for applying the operator T^{\pi}_{P,B} of
 * E. Payet,
 * <a href="https://doi.org/10.1017/S1471068425100100"><i>Non-Termination of
 * Logic Programs Using Patterns</i></a>, Theory and Practice of Logic
 * Programming 25(4), pp. 739--755, 2025.
 * <p>
 * It is used in the method RuleLp.unfoldPattern(...).
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class PatternRuleLpInProgress {

	/**
	 * The pattern substitution computed so far
	 * during the unfolding.
	 */
	private final PatternSubstitution patternSubstitution;
	
	/**
	 * The iteration of the unfolding operator at
	 * which this rule in progress is generated.
	 */
	private final int iteration;
		
	/**
	 * Builds a pattern rule in progress from
	 * the provided elements.
	 * 
	 * @param patternSubstitution the pattern substitution
	 * computed so far during the unfolding
	 * @param iteration the iteration of the
	 * unfolding operator at which this rule
	 * in progress is generated
	 * @throws IllegalArgumentException if the
	 * given iteration is negative
	 */
	public PatternRuleLpInProgress(
			PatternSubstitution patternSubstitution,
			int iteration) {
		
		if (iteration < 0)
			throw new IllegalArgumentException(
					"construction of a LP pattern rule in progress with a negative iteration");
		
		this.patternSubstitution = patternSubstitution;
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
		this(SimplePatternSubstitution.empty(), iteration);
	}
	
	/**
	 * Returns a deep copy of this rule in progress
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * <p>
	 * The returned copy is "flattened" i.e., each of
	 * its subterms is the only element of its class
	 * and is its own schema.
	 * 
	 * @return a deep copy of this rule in progress
	 */
	public PatternRuleLpInProgress deepCopy() {
		return PatternRuleLpInProgressCopier.deepCopy(this);
	}
	
	/**
	 * Returns a deep copy of this rule in progress
	 * i.e., a copy where each subterm is also copied,
	 * even variable subterms.
	 * <p>
	 * The specified map is used to store subterm
	 * copies and is constructed incrementally.
	 * <p>
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
		return PatternRuleLpInProgressCopier.deepCopy(this, copies);
	}
	
	/**
	 * Returns the pattern substitution of
	 * this rule in progress.
	 * 
	 * @return the pattern substitution of
	 * this rule in progress
	 */
	public PatternSubstitution getPatternSubstitution() {
		return this.patternSubstitution;
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
		return PatternRuleLpInProgressFormatter.format(this, variables);
	}
	
	/**
	 * Returns a string representation of this object.
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
