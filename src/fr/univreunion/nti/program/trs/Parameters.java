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

/**
 * Parameters for non-termination analysis of a TRS.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class Parameters {

	/**
	 * The default behavior w.r.t. forward unfolding.
	 * Used while searching for loops.
	 */
	private final static boolean DEFAULT_UNFOLD_FORWARDS = true;

	/**
	 * The default behavior w.r.t. backward unfolding.
	 * Used while searching for loops.
	 */
	private final static boolean DEFAULT_UNFOLD_BACKWARDS = true;

	/**
	 * The default behavior w.r.t. variable unfolding.
	 * Used while searching for loops.
	 */
	private final static boolean DEFAULT_UNFOLD_VAR = false;

	/**
	 * The default maximum depth allowed for an unfolded rule.
	 * Used while searching for loops.
	 * Negative means unlimited.
	 */
	private final static int DEFAULT_MAX_DEPTH = -1;

	/**
	 * The default strategy for selecting disagreement pair positions.
	 */
	private final static StrategyLoop DEFAULT_STRATEGY = StrategyLoop.LEFTMOST_NE;

	/**
	 * True if and only if forward unfolding is enabled.
	 * Used while searching for loops.
	 */
	private final boolean unfoldForwards;

	/**
	 * True if and only if backward unfolding is enabled.
	 * Used while searching for loops.
	 * 
	 * Not final because we need to be able to modify its
	 * value in the "Loop by unfolding" technique.
	 */
	private boolean unfoldBackwards;

	/**
	 * True if and only if unfolding of variable positions
	 * is enabled. Used while searching for loops.
	 * 
	 * Not final because we need to be able to modify its
	 * value in the "Loop by unfolding" technique.
	 */
	private boolean unfoldVar;

	/**
	 * The maximum depth allowed for an unfolded rule.
	 * Negative means unlimited. Used while searching
	 * for loops.
	 * 
	 * Not final because we need to be able to modify its
	 * value in the "Loop by unfolding" technique.
	 */
	private int maxDepth;

	/**
	 * The strategy for selecting disagreement pair
	 * positions. Used while searching for loops.
	 */
	private StrategyLoop strategy;

	/**
	 * Builds a set of default parameters for analyzing
	 * a program.
	 */
	public Parameters() {
		// We use the default value of each parameter.
		this.unfoldForwards = DEFAULT_UNFOLD_FORWARDS;
		this.unfoldBackwards = DEFAULT_UNFOLD_BACKWARDS;
		this.unfoldVar = DEFAULT_UNFOLD_VAR;
		this.maxDepth = DEFAULT_MAX_DEPTH;
		this.strategy = DEFAULT_STRATEGY;
	}

	/**
	 * Copy constructor.
	 * 
	 * @param parameters the set of parameters to
	 *                   copy
	 */
	private Parameters(Parameters parameters) {
		this.unfoldForwards = parameters.unfoldForwards;
		this.unfoldBackwards = parameters.unfoldBackwards;
		this.unfoldVar = parameters.unfoldVar;
		this.maxDepth = parameters.maxDepth;
		this.strategy = parameters.strategy;
	}

	/**
	 * Returns a copy of this set of parameters.
	 * 
	 * @return a copy of this set of parameters
	 */
	public Parameters copy() {
		return new Parameters(this);
	}

	/**
	 * Returns <tt>true</tt> if and only if forward unfolding
	 * is enabled.
	 * 
	 * @return <tt>true</tt> if and only if forward unfolding
	 *         is enabled
	 */
	public synchronized boolean isForwardUnfoldingEnabled() {
		return this.unfoldForwards;
	}

	/**
	 * Returns <tt>true</tt> if and only if backward unfolding
	 * is enabled.
	 * 
	 * @return <tt>true</tt> if and only if backward unfolding
	 *         is enabled
	 */
	public synchronized boolean isBackwardUnfoldingEnabled() {
		return this.unfoldBackwards;
	}

	/**
	 * Disable backward unfolding.
	 */
	public synchronized void disableBackwardUnfolding() {
		this.unfoldBackwards = false;
	}

	/**
	 * Returns <tt>true</tt> if and only if unfolding of variable
	 * positions is enabled.
	 * 
	 * @return <tt>true</tt> if and only if unfolding of variable
	 *         positions is enabled
	 */
	public synchronized boolean isVariableUnfoldingEnabled() {
		return this.unfoldVar;
	}

	/**
	 * Enables/disables unfolding of variable positions.
	 * 
	 * @param enabled <code>true</code> iff unfolding of
	 *                variable positions is enabled
	 */
	public synchronized void setVariableUnfolding(boolean enabled) {
		this.unfoldVar = enabled;
	}

	/**
	 * Returns the maximum depth allowed for an unfolded rule.
	 * 
	 * @return the maximum depth allowed for an unfolded rule
	 */
	public synchronized int getMaxDepth() {
		return this.maxDepth;
	}

	/**
	 * Sets the maximum depth of an unfolded rule to
	 * the specified integer.
	 * 
	 * @param maxDepth the maximum depth of an
	 *                 unfolded rule
	 */
	public synchronized void setMaxDepth(int maxDepth) {
		this.maxDepth = maxDepth;
	}

	/**
	 * Returns the strategy for selecting disagreement
	 * pair positions.
	 * 
	 * @return the strategy for selecting disagreement
	 *         pair positions
	 */
	public synchronized StrategyLoop getStrategy() {
		return this.strategy;
	}

	/**
	 * Sets the strategy for selecting disagreement
	 * pair positions.
	 * 
	 * @param strategy the strategy for selecting
	 *                 disagreement pair positions
	 */
	public synchronized void setStrategy(StrategyLoop strategy) {
		this.strategy = strategy;
	}

	/**
	 * Returns a String representation of this
	 * set of parameters.
	 */
	@Override
	public String toString() {
		StringBuffer s = new StringBuffer();

		s.append("forward=");
		s.append(this.unfoldForwards);
		s.append(", backward=");
		s.append(this.unfoldBackwards);
		s.append(", max=");
		s.append(this.maxDepth);

		return s.toString();
	}
}
