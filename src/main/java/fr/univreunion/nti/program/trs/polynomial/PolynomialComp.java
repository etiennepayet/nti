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

package fr.univreunion.nti.program.trs.polynomial;

import java.util.Arrays;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater;

import fr.univreunion.nti.term.Variable;

/**
 * A composed polynomial i.e., a polynomial
 * which results from adding of multiplying
 * two polynomials.
 * <p>
 * Its polynomial structure is immutable. Repeated evaluation may populate an
 * internal execution-plan cache without changing the represented polynomial.
 *
 * <p>The constraint-solving operations support the method of J. Giesl,
 * <a href="https://doi.org/10.1007/3-540-59200-8_77">Generating Polynomial
 * Orderings for Termination Proofs</a>, RTA 1995, LNCS 914, 426--431.
 * 
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public class PolynomialComp implements Polynomial {

	/**
	 * Encoded value used when a polynomial has no integer value under the
	 * provided interpretation. It lies outside the range of {@code int}.
	 */
	private static final long UNDEFINED_VALUE = Long.MIN_VALUE;

	/**
	 * A reusable evaluation stack for each thread evaluating compiled native
	 * polynomials.
	 */
	private static final ThreadLocal<int[]> EVALUATION_STACK =
			ThreadLocal.withInitial(() -> new int[16]);

	/**
	 * The largest evaluation stack retained by a worker thread. Larger,
	 * exceptional trees use a temporary stack which is removed after evaluation.
	 */
	private static final int MAX_RETAINED_EVALUATION_STACK_SIZE = 4096;

	/**
	 * The number of null-interpretation evaluations required before compiling a
	 * postfix plan.
	 */
	private static final int EVALUATION_PLAN_COMPILATION_THRESHOLD = 64;

	/**
	 * Atomically advances the evaluation count without allocating a counter for
	 * every composed polynomial.
	 */
	private static final AtomicIntegerFieldUpdater<PolynomialComp>
			EVALUATION_COUNT_UPDATER = AtomicIntegerFieldUpdater.newUpdater(
					PolynomialComp.class, "evaluationsWithoutInterpretation");

	/**
	 * The root arithmetic operator of this polynomial.
	 * <p>
	 * As the arity of every arithmetic operator is equal
	 * to 2, this polynomial has a left operand and a right
	 * operand.  
	 */
	private final ArithOperator rootOperator;

	/**
	 * The left operand of this polynomial.
	 */
	private final Polynomial left;

	/**
	 * The right operand of this polynomial.
	 */
	private final Polynomial right;

	/**
	 * Whether this polynomial and all its operands use NTI's built-in
	 * polynomial implementations.
	 */
	private final boolean containsOnlyBuiltInPolynomials;

	/**
	 * Whether this polynomial contains a built-in polynomial variable.
	 */
	private final boolean containsPolynomialVariable;

	/**
	 * The compiled evaluator of this polynomial, once repeated evaluation has
	 * justified building it.
	 */
	@SuppressWarnings("java:S3077") // EvaluationPlan is immutable and safely published.
	private volatile EvaluationPlan evaluationPlan;

	/**
	 * The number of times this polynomial has been evaluated without an
	 * interpretation, up to {@link #EVALUATION_PLAN_COMPILATION_THRESHOLD}.
	 * Delaying compilation prevents short-lived compositions from paying for a
	 * plan that they would barely reuse.
	 */
	private volatile int evaluationsWithoutInterpretation;

	/**
	 * Builds and simplifies a polynomial from the specified
	 * operator and operands.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * the polynomial
	 * @param left the left operand of the root operator
	 * of the polynomial
	 * @param right the right operand of the root operator
	 * of the polynomial
	 * @return a simplified polynomial constructed from the
	 * specified operator and operands; the returned polynomial
	 * is not necessarily a <code>PolynomialComp</code>
	 */
	public static synchronized Polynomial simplified(
			ArithOperator rootOperator, Polynomial left, Polynomial right) {

		return new PolynomialComp(rootOperator, left, right).simplify();
	}

	/**
	 * Builds and simplifies a polynomial from the specified
	 * operator and operands.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * the polynomial
	 * @param operands the operands of the root operator
	 * of the polynomial
	 * @return a simplified polynomial constructed from the
	 * specified operator and operands; the returned polynomial
	 * is not necessarily a <code>PolynomialComp</code>
	 */
	public static synchronized Polynomial simplified(
			ArithOperator rootOperator, List<Polynomial> operands) {

		if (operands == null || operands.isEmpty())
			throw new IllegalArgumentException();

		return simplifiedFrom(rootOperator, operands.iterator());
	}

	/**
	 * Builds and simplifies a polynomial from the specified
	 * operator and operands, starting from the next operand
	 * returned by the specified iterator.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * the polynomial
	 * @param it an iterator over a collection of operands
	 * @return a simplified polynomial constructed from the
	 * specified operator and operands
	 */
	private static synchronized Polynomial simplifiedFrom(
			ArithOperator rootOperator, Iterator<Polynomial> it) {

		// Here, we know that 'it' has a next element because
		// it is the case when this method is called for the
		// first time in 'simplified' and it is also the case
		// when this method is recursively called below.

		Polynomial firstPolynomial = it.next();

		if (it.hasNext())
			return simplified(rootOperator, firstPolynomial, simplifiedFrom(rootOperator, it));

		return firstPolynomial;
	}

	/**
	 * Builds a polynomial.
	 * 
	 * @param rootOperator the root arithmetic operator of
	 * this polynomial
	 * @param left the left operand of this polynomial
	 * @param right the right operand of this polynomial
	 */
	private PolynomialComp(ArithOperator rootOperator, Polynomial left, Polynomial right) {
		this.rootOperator = rootOperator;
		this.left = left;
		this.right = right;
		this.containsOnlyBuiltInPolynomials =
				containsOnlyBuiltInPolynomials(left) &&
				containsOnlyBuiltInPolynomials(right);
		this.containsPolynomialVariable =
				containsPolynomialVariable(left) ||
				containsPolynomialVariable(right);
	}

	/**
	 * Returns whether the specified polynomial and all its operands use NTI's
	 * built-in polynomial implementations.
	 *
	 * @param polynomial the polynomial to inspect
	 * @return {@code true} iff the polynomial contains built-in implementations
	 * only
	 */
	private static boolean containsOnlyBuiltInPolynomials(Polynomial polynomial) {
		Class<?> polynomialClass = polynomial.getClass();
		return polynomialClass == PolynomialConst.class ||
				polynomialClass == PolynomialVar.class ||
				polynomialClass == PolynomialComp.class &&
				((PolynomialComp) polynomial).containsOnlyBuiltInPolynomials;
	}

	/**
	 * Returns whether the specified polynomial contains a built-in polynomial
	 * variable.
	 *
	 * @param polynomial the polynomial to inspect
	 * @return {@code true} iff the polynomial contains a built-in variable
	 */
	private static boolean containsPolynomialVariable(Polynomial polynomial) {
		Class<?> polynomialClass = polynomial.getClass();
		return polynomialClass == PolynomialVar.class ||
				polynomialClass == PolynomialComp.class &&
				((PolynomialComp) polynomial).containsPolynomialVariable;
	}

	/**
	 * Computes the partial derivative of this polynomial
	 * with respect to the given variable.
	 * 
	 * @param v a variable for computing the partial derivative
	 * of this polynomial
	 * @return the partial derivative of this polynomial
	 * with respect to the given variable
	 */
	@Override
	public Polynomial partialDerivative(Variable v) {
		if (this.containsOnlyBuiltInPolynomials)
			return this.partialDerivativeOfBuiltInPolynomial(v);

		return this.partialDerivativeOfGenericPolynomial(v);
	}

	/**
	 * Computes the partial derivative of a tree containing built-in polynomial
	 * implementations only. Recursive derivative results are already simplified,
	 * so a parent operation only refreshes an unchanged original operand.
	 *
	 * @param variable the variable for computing the partial derivative
	 * @return the simplified partial derivative
	 */
	private Polynomial partialDerivativeOfBuiltInPolynomial(Variable variable) {
		if (this.left instanceof PolynomialConst && this.right instanceof PolynomialConst)
			return PolynomialConst.ZERO;

		if (this.rootOperator == ArithOperator.TIMES) {
			if (this.left instanceof PolynomialConst)
				return simplifiedDerivative(
						ArithOperator.TIMES,
						this.left,
						true,
						partialDerivativeOfBuiltInPolynomial(this.right, variable),
						true);
			if (this.right instanceof PolynomialConst)
				return simplifiedDerivative(
						ArithOperator.TIMES,
						partialDerivativeOfBuiltInPolynomial(this.left, variable),
						true,
						this.right,
						true);

			Polynomial leftDerivative =
					partialDerivativeOfBuiltInPolynomial(this.left, variable);
			Polynomial rightDerivative =
					partialDerivativeOfBuiltInPolynomial(this.right, variable);
			Polynomial leftProduct = simplifiedDerivative(
					ArithOperator.TIMES,
					leftDerivative,
					true,
					this.right,
					false);
			Polynomial rightProduct = simplifiedDerivative(
					ArithOperator.TIMES,
					this.left,
					false,
					rightDerivative,
					true);
			return simplifiedDerivative(
					ArithOperator.PLUS,
					leftProduct,
					true,
					rightProduct,
					true);
		}

		if (this.rootOperator == ArithOperator.PLUS && this.left instanceof PolynomialConst)
			return partialDerivativeOfBuiltInPolynomial(this.right, variable);
		if (this.right instanceof PolynomialConst)
			return partialDerivativeOfBuiltInPolynomial(this.left, variable);
		return simplifiedDerivative(
				this.rootOperator,
				partialDerivativeOfBuiltInPolynomial(this.left, variable),
				true,
				partialDerivativeOfBuiltInPolynomial(this.right, variable),
				true);
	}

	/**
	 * Computes a built-in operand's already simplified partial derivative.
	 *
	 * @param polynomial the operand
	 * @param variable the differentiation variable
	 * @return the simplified partial derivative
	 */
	private static Polynomial partialDerivativeOfBuiltInPolynomial(
			Polynomial polynomial, Variable variable) {

		if (polynomial instanceof PolynomialComp composition)
			return composition.partialDerivativeOfBuiltInPolynomial(variable);

		return polynomial.partialDerivative(variable);
	}

	/**
	 * Combines operands while preserving the simplification performed by the
	 * generic construction path. An operand freshly returned by a recursive
	 * derivative need not be traversed again.
	 *
	 * @param operator the root arithmetic operator
	 * @param left the left operand
	 * @param leftIsSimplified whether the left operand is already simplified
	 * @param right the right operand
	 * @param rightIsSimplified whether the right operand is already simplified
	 * @return the simplified combination
	 */
	private static Polynomial simplifiedDerivative(
			ArithOperator operator,
			Polynomial left,
			boolean leftIsSimplified,
			Polynomial right,
			boolean rightIsSimplified) {

		Polynomial simplifiedLeft = leftIsSimplified ? left : left.simplify();
		Polynomial simplifiedRight = rightIsSimplified ? right : right.simplify();
		Integer leftValue = simplifiedLeft instanceof PolynomialConst constant
				? constant.getValue() : null;
		Integer rightValue = simplifiedRight instanceof PolynomialConst constant
				? constant.getValue() : null;

		if (leftValue != null && rightValue != null)
			return new PolynomialConst(
					evaluate(operator, leftValue, rightValue));

		return switch (operator) {
			case MINUS -> simplifyDerivativeDifference(
					simplifiedLeft, simplifiedRight, rightValue);
			case PLUS -> simplifyDerivativeSum(
					simplifiedLeft, leftValue, simplifiedRight, rightValue);
			case TIMES -> simplifyDerivativeProduct(
					simplifiedLeft, leftValue, simplifiedRight, rightValue);
		};
	}

	/**
	 * Applies an arithmetic operator with Java {@code int} overflow semantics.
	 *
	 * @param operator the arithmetic operator
	 * @param left the left integer operand
	 * @param right the right integer operand
	 * @return the operation result
	 */
	private static int evaluate(ArithOperator operator, int left, int right) {
		return switch (operator) {
			case MINUS -> left - right;
			case PLUS -> left + right;
			case TIMES -> left * right;
		};
	}

	/**
	 * Simplifies a derivative product whose operands are already simplified.
	 *
	 * @param left the simplified left operand
	 * @param leftValue the left constant value, if defined
	 * @param right the simplified right operand
	 * @param rightValue the right constant value, if defined
	 * @return the simplified product
	 */
	private static Polynomial simplifyDerivativeProduct(
			Polynomial left,
			Integer leftValue,
			Polynomial right,
			Integer rightValue) {

		if (leftValue != null) {
			if (leftValue == 0)
				return PolynomialConst.ZERO;
			if (leftValue == 1)
				return right;
		}
		if (rightValue != null) {
			if (rightValue == 0)
				return PolynomialConst.ZERO;
			if (rightValue == 1)
				return left;
		}
		return new PolynomialComp(ArithOperator.TIMES, left, right);
	}

	/**
	 * Simplifies a derivative sum whose operands are already simplified.
	 *
	 * @param left the simplified left operand
	 * @param leftValue the left constant value, if defined
	 * @param right the simplified right operand
	 * @param rightValue the right constant value, if defined
	 * @return the simplified sum
	 */
	private static Polynomial simplifyDerivativeSum(
			Polynomial left,
			Integer leftValue,
			Polynomial right,
			Integer rightValue) {

		if (leftValue != null && leftValue == 0)
			return right;
		if (rightValue != null && rightValue == 0)
			return left;
		return new PolynomialComp(ArithOperator.PLUS, left, right);
	}

	/**
	 * Simplifies a derivative difference whose operands are already simplified.
	 *
	 * @param left the simplified left operand
	 * @param right the simplified right operand
	 * @param rightValue the right constant value, if defined
	 * @return the simplified difference
	 */
	private static Polynomial simplifyDerivativeDifference(
			Polynomial left, Polynomial right, Integer rightValue) {

		if (rightValue != null && rightValue == 0)
			return left;
		return new PolynomialComp(ArithOperator.MINUS, left, right);
	}

	/**
	 * Computes the partial derivative through the generic polynomial contract.
	 *
	 * @param v the variable for computing the partial derivative
	 * @return the simplified partial derivative
	 */
	private Polynomial partialDerivativeOfGenericPolynomial(Variable v) {

		// If both operands of this polynomial are constant polynomials,
		// then this polynomial is a constant polynomial and its partial
		// derivative is 0.
		if (this.left instanceof PolynomialConst && this.right instanceof PolynomialConst)
			return PolynomialConst.ZERO;

		// From here, at least one of the operands of this polynomial
		// is not a constant polynomial.

		if (this.rootOperator == ArithOperator.TIMES) {
			if (this.left instanceof PolynomialConst)
				return PolynomialComp.simplified(ArithOperator.TIMES,
						this.left, this.right.partialDerivative(v));
			if (this.right instanceof PolynomialConst)
				return PolynomialComp.simplified(ArithOperator.TIMES,
						this.left.partialDerivative(v), this.right);
			return PolynomialComp.simplified(ArithOperator.PLUS,
					PolynomialComp.simplified(ArithOperator.TIMES, this.left.partialDerivative(v), this.right),
					PolynomialComp.simplified(ArithOperator.TIMES, this.left, this.right.partialDerivative(v)));
		}

		// Here, the root operator of this polynomial is + or -.
		if (this.rootOperator == ArithOperator.PLUS && this.left instanceof PolynomialConst)
			return this.right.partialDerivative(v);
		if (this.right instanceof PolynomialConst)
			return this.left.partialDerivative(v);
		return PolynomialComp.simplified(this.rootOperator,
				this.left.partialDerivative(v),
				this.right.partialDerivative(v));
	}

	/**
	 * Returns the polynomial resulting from replacing, in this 
	 * polynomial, all the specified variables with
	 * <code>mu</code>.
	 * 
	 * @param variables the variables to be replaced with
	 * <code>mu</code>
	 * @param mu the variable used in [Giesl, RTA'95] for
	 * solving polynomial constraints
	 * @return the polynomial resulting from replacing all
	 * the specified variables with <code>mu</code>
	 */
	@Override
	public Polynomial replaceWithMu(Deque<Variable> variables, PolynomialConst mu) {
		return new PolynomialComp(this.rootOperator,
				this.left.replaceWithMu(variables, mu),
				this.right.replaceWithMu(variables, mu));
	}

	/**
	 * Returns the value of this <code>polynomial</code> as
	 * an <code>Integer</code>.
	 * 
	 * @param interpretation an interpretation of the variables of
	 * this polynomial
	 * @return the value of this <code>polynomial</code> as
	 * an <code>Integer</code>
	 */
	@Override
	public Integer integerValue(Map<Variable,Integer> interpretation) {
		if (interpretation == null && this.containsOnlyBuiltInPolynomials) {
			if (this.containsPolynomialVariable)
				return null;

			EvaluationPlan plan = this.evaluationPlan;
			if (plan == null)
				plan = this.compileEvaluationPlanIfReady();
			if (plan != null) {
				long value = plan.encodedIntegerValue();
				return value == UNDEFINED_VALUE ? null : (int) value;
			}
		}

		long value = this.encodedIntegerValue(interpretation);
		return value == UNDEFINED_VALUE ? null : (int) value;
	}

	/**
	 * Compiles and publishes this polynomial's evaluation plan once its reuse
	 * threshold has been reached.
	 *
	 * @return the compiled plan, or {@code null} while recursive evaluation is
	 * still preferred
	 */
	private EvaluationPlan compileEvaluationPlanIfReady() {
		if (EVALUATION_COUNT_UPDATER.getAndIncrement(this)
				< EVALUATION_PLAN_COMPILATION_THRESHOLD)
			return null;

		EvaluationPlan compiledPlan = EvaluationPlan.compile(this);
		this.evaluationPlan = compiledPlan;
		return compiledPlan;
	}

	/**
	 * Computes this polynomial's integer value without boxing intermediate
	 * composed-polynomial results.
	 *
	 * @param interpretation an interpretation of the polynomial variables
	 * @return the integer value, or {@link #UNDEFINED_VALUE} if undefined
	 */
	private long encodedIntegerValue(Map<Variable, Integer> interpretation) {
		long leftValue = encodedIntegerValue(this.left, interpretation);
		if (leftValue == UNDEFINED_VALUE)
			return UNDEFINED_VALUE;

		long rightValue = encodedIntegerValue(this.right, interpretation);
		if (rightValue == UNDEFINED_VALUE)
			return UNDEFINED_VALUE;

		int leftInteger = (int) leftValue;
		int rightInteger = (int) rightValue;
		if (this.rootOperator == ArithOperator.MINUS)
			return (int) ((long) leftInteger - rightInteger);
		if (this.rootOperator == ArithOperator.PLUS)
			return (int) ((long) leftInteger + rightInteger);
		return (int) ((long) leftInteger * rightInteger);
	}

	/**
	 * Computes the encoded value of the specified polynomial.
	 *
	 * @param polynomial the polynomial to evaluate
	 * @param interpretation an interpretation of the polynomial variables
	 * @return the integer value, or {@link #UNDEFINED_VALUE} if undefined
	 */
	private static long encodedIntegerValue(
			Polynomial polynomial,
			Map<Variable, Integer> interpretation) {

		if (polynomial instanceof PolynomialComp composition)
			return composition.encodedIntegerValue(interpretation);

		Integer value = polynomial.integerValue(interpretation);
		return value == null ? UNDEFINED_VALUE : value;
	}

	/**
	 * A postfix evaluation plan for a variable-free tree consisting only of
	 * NTI's built-in polynomial implementations.
	 */
	private static final class EvaluationPlan {

		private static final byte CONSTANT = 0;
		private static final byte MINUS = 1;
		private static final byte PLUS = 2;
		private static final byte TIMES = 3;

		private final byte[] instructions;
		private final PolynomialConst[] constants;

		private EvaluationPlan(byte[] instructions, PolynomialConst[] constants) {
			this.instructions = instructions;
			this.constants = constants;
		}

		private static EvaluationPlan compile(PolynomialComp polynomial) {
			PlanBuilder builder = new PlanBuilder();
			builder.append(polynomial);
			return builder.build();
		}

		@SuppressWarnings("java:S6880") // The equivalent switch regresses this hot path.
		private long encodedIntegerValue() {
			int[] stack = EVALUATION_STACK.get();
			if (stack.length < this.instructions.length) {
				stack = new int[this.instructions.length];
				if (stack.length <= MAX_RETAINED_EVALUATION_STACK_SIZE)
					EVALUATION_STACK.set(stack);
				else
					EVALUATION_STACK.remove();
			}

			int top = 0;
			int constantIndex = 0;
			for (byte instruction : this.instructions) {
				if (instruction == CONSTANT) {
					Integer value = this.constants[constantIndex++].getValue();
					if (value == null)
						return UNDEFINED_VALUE;
					stack[top++] = value;
				}
				else {
					int rightValue = stack[--top];
					int leftValue = stack[top - 1];
					if (instruction == MINUS)
						stack[top - 1] = (int) ((long) leftValue - rightValue);
					else if (instruction == PLUS)
						stack[top - 1] = (int) ((long) leftValue + rightValue);
					else
						stack[top - 1] = (int) ((long) leftValue * rightValue);
				}
			}

			return stack[0];
		}

		private static final class PlanBuilder {
			private byte[] instructions = new byte[16];
			private PolynomialConst[] constants = new PolynomialConst[8];
			private int instructionCount;
			private int constantCount;

			private void append(Polynomial polynomial) {
				if (polynomial instanceof PolynomialComp composition) {
					this.append(composition.left);
					this.append(composition.right);
					this.appendInstruction(switch (composition.rootOperator) {
						case MINUS -> MINUS;
						case PLUS -> PLUS;
						case TIMES -> TIMES;
					});
				}
				else {
					this.appendInstruction(CONSTANT);
					if (this.constantCount == this.constants.length)
						this.constants = Arrays.copyOf(
								this.constants, this.constants.length * 2);
					this.constants[this.constantCount++] =
							(PolynomialConst) polynomial;
				}
			}

			private void appendInstruction(byte instruction) {
				if (this.instructionCount == this.instructions.length)
					this.instructions = Arrays.copyOf(
							this.instructions, this.instructions.length * 2);
				this.instructions[this.instructionCount++] = instruction;
			}

			private EvaluationPlan build() {
				return new EvaluationPlan(
						Arrays.copyOf(this.instructions, this.instructionCount),
						Arrays.copyOf(this.constants, this.constantCount));
			}
		}
	}

	/**
	 * Simplifies this polynomial using the current
	 * values of its coefficients.
	 * 
	 * @return a simplified version of this polynomial,
	 * which takes into account the current value of
	 * its coefficients
	 */
	@Override
	public Polynomial simplify() {
		// If this polynomial has an integer value
		// then we return this value.
		Integer value = this.integerValue(null);
		if (value != null)
			return new PolynomialConst(value);

		// Otherwise, we simplify its left and right operands.
		Polynomial simplifiedLeft  = this.left.simplify();
		Polynomial simplifiedRight = this.right.simplify();

		if (this.rootOperator == ArithOperator.TIMES)
			return simplifyProduct(simplifiedLeft, simplifiedRight);
		if (this.rootOperator == ArithOperator.PLUS)
			return simplifySum(simplifiedLeft, simplifiedRight);
		return simplifyDifference(simplifiedLeft, simplifiedRight);
	}

	/**
	 * Simplifies a product whose operands have already been simplified.
	 *
	 * @param left the simplified left operand
	 * @param right the simplified right operand
	 * @return the simplified product
	 */
	private static Polynomial simplifyProduct(Polynomial left, Polynomial right) {
		Integer leftValue = left.integerValue(null);
		if (leftValue != null) {
			if (leftValue == 0)
				return PolynomialConst.ZERO;
			if (leftValue == 1)
				return right;
		}

		Integer rightValue = right.integerValue(null);
		if (rightValue != null) {
			if (rightValue == 0)
				return PolynomialConst.ZERO;
			if (rightValue == 1)
				return left;
		}

		return new PolynomialComp(ArithOperator.TIMES, left, right);
	}

	/**
	 * Simplifies a sum whose operands have already been simplified.
	 *
	 * @param left the simplified left operand
	 * @param right the simplified right operand
	 * @return the simplified sum
	 */
	private static Polynomial simplifySum(Polynomial left, Polynomial right) {
		Integer leftValue = left.integerValue(null);
		if (leftValue != null && leftValue == 0)
			return right;

		Integer rightValue = right.integerValue(null);
		if (rightValue != null && rightValue == 0)
			return left;

		return new PolynomialComp(ArithOperator.PLUS, left, right);
	}

	/**
	 * Simplifies a difference whose operands have already been simplified.
	 *
	 * @param left the simplified left operand
	 * @param right the simplified right operand
	 * @return the simplified difference
	 */
	private static Polynomial simplifyDifference(Polynomial left, Polynomial right) {
		Integer rightValue = right.integerValue(null);
		if (rightValue != null && rightValue == 0)
			return left;

		return new PolynomialComp(ArithOperator.MINUS, left, right);
	}

	/**
	 * Checks whether this polynomial contains the given
	 * variable.
	 * 
	 * @param variable a variable
	 * @return <code>true</code> iff this polynomial
	 * contains <code>variable</code>
	 */
	@Override
	public boolean contains(Variable variable) {
		return this.left.contains(variable) || this.right.contains(variable);
	}

	/**
	 * Returns a collection consisting of the monomials
	 * of this polynomial.
	 * 
	 * @return a collection consisting of the monomials
	 * of this polynomial
	 */
	@Override
	public Collection<Polynomial> getMonomials() {
		// The list to return at the end
		LinkedList<Polynomial> monomials = new LinkedList<>();

		if (this.rootOperator == ArithOperator.PLUS || this.rootOperator == ArithOperator.MINUS) {
			monomials.addAll(this.left.getMonomials());
			monomials.addAll(this.right.getMonomials());
		}
		else
			monomials.add(this);

		return monomials;
	}

	/**
	 * Tries to check whether <code>P &ge; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &ge; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &ge; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean gez() {
		// Given the way we build constraints, this polynomial
		// has the form P1 op P2 where op is its root operator
		// and the minus operator does not occur in P1 and P2.
		// Hence, as constant polynomials are instantiated with
		// non-negative integers, we necessarily have P1 >= 0 and
		// P2 >= 0.

		// We check whether this polynomial has the form
		// P1 + P2 or P1 - P1 or P1 x P2.
		return (this.left == this.right) ||
				(this.rootOperator != ArithOperator.MINUS);
	}

	/**
	 * Tries to check whether <code>P &gt; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &gt; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &gt; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean gtz() {
		// We do not know.
		return false;
	}

	/**
	 * Tries to check whether <code>P &le; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &le; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &le; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean lez() {
		// Given the way we build constraints, this polynomial
		// has the form P1 op P2 where op is its root operator
		// and the minus operator does not occur in P1 and P2.
		// Hence, as constant polynomials are instantiated with
		// non-negative integers, we necessarily have P1 >= 0 and
		// P2 >= 0.

		if (this.rootOperator == ArithOperator.MINUS)
			// If op is the minus operator, then we check whether
			// P1 = P2 (i.e., this polynomial has the form P1 - P1)
			// or whether P1 = 0 (i.e., this polynomial has the form
			// 0 - P2).
			return (this.left == this.right) ||
					(this.left == PolynomialConst.ZERO);

		// From here, op is not the minus operator, i.e., this
		// polynomial has the form P1 + P2 or P1 x P2 with
		// P1 >= 0 and P2 >= 0. Hence, we do not know.

		return false;
	}

	/**
	 * Tries to check whether <code>P &lt; 0</code>
	 * holds, where <code>P</code> is this polynomial.
	 * <p>
	 * If <code>true</code> is returned, then it is certain
	 * that <code>P &lt; 0</code> holds. Otherwise, i.e.,
	 * if <code>false</code> is returned, then we do not
	 * know.
	 * 
	 * @return <code>true</code> if it is certain that
	 * <code>P &lt; 0</code> holds, or <code>false</code>
	 * if we do not know
	 */
	@Override
	public boolean ltz() {
		// We do not know.
		return false;
	}

	/**
	 * If this polynomial is the subtraction of two
	 * constant polynomials, then returns an array
	 * containing these two constant polynomials.
	 * Otherwise, returns <code>null</code>.
	 * 
	 * @return an array containing two constant
	 * polynomials, or <code>null</code>
	 */
	@Override
	public PolynomialConst[] subOperands() {

		if (this.rootOperator == ArithOperator.MINUS &&
				this.left instanceof PolynomialConst leftConstant &&
				this.right instanceof PolynomialConst rightConstant)

			return new PolynomialConst[] {
					leftConstant,
					rightConstant };

		return null;
	}

	/**
	 * Returns a string representation of this polynomial
	 * relatively to the given set of variable symbols.
	 * 
	 * @param variables a set of pairs <code>(variable,s)</code>
	 * where <code>s</code> is the string associated to
	 * <code>variable</code>
	 * @return a string representation of this polynomial
	 */
	@Override
	public String toString(Map<Variable,String> variables) {
		// Parentheses around the left operand.
		String par1 = "";
		String par2 = "";
		// Parentheses around the right operand.
		String par3 = "";
		String par4 = "";

		if (this.rootOperator == ArithOperator.TIMES &&
				this.left instanceof PolynomialComp leftComp &&
				leftComp.rootOperator != ArithOperator.TIMES) {
			par1 = "(";
			par2 = ")";
		}
		if (this.rootOperator == ArithOperator.TIMES &&
				this.right instanceof PolynomialComp rightComp &&
				rightComp.rootOperator != ArithOperator.TIMES) {
			par3 = "(";
			par4 = ")";
		}

		if (this.rootOperator == ArithOperator.MINUS &&
				this.right instanceof PolynomialComp rightComp &&
				rightComp.rootOperator != ArithOperator.TIMES) {
			par3 = "(";
			par4 = ")";
		}

		return par1 + this.left.toString(variables) + par2 +
				" " + this.rootOperator + " " +
				par3 + this.right.toString(variables) + par4;	
	}

	/**
	 * Returns a string representation of this polynomial.
	 * 
	 * @return a string representation of this polynomial
	 */
	@Override
	public String toString() {
		return this.toString(new HashMap<>());
	}
}
