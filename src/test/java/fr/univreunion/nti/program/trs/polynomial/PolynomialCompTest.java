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

package fr.univreunion.nti.program.trs.polynomial;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Deque;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import fr.univreunion.nti.term.Variable;

class PolynomialCompTest {

	@Test
	@DisplayName("evaluate nested compositions and preserve int overflow")
	void evaluateNestedCompositionsAndPreserveIntOverflow() {
		Variable variable = new Variable();
		Polynomial variablePolynomial = new PolynomialVar(variable);
		Polynomial sum = PolynomialComp.simplified(
				ArithOperator.PLUS,
				variablePolynomial,
				new PolynomialConst(2));
		Polynomial product = PolynomialComp.simplified(
				ArithOperator.TIMES,
				sum,
				new PolynomialConst(2));
		Polynomial difference = PolynomialComp.simplified(
				ArithOperator.MINUS,
				product,
				new PolynomialConst(3));

		assertEquals(10, product.integerValue(Map.of(variable, 3)));
		assertEquals(2, product.integerValue(
				Map.of(variable, Integer.MAX_VALUE)));
		assertEquals(7, difference.integerValue(Map.of(variable, 3)));
		assertEquals(-1, difference.integerValue(
				Map.of(variable, Integer.MAX_VALUE)));
		assertNull(difference.integerValue(null));
		assertNull(difference.integerValue(Map.of()));
	}

	@Test
	@DisplayName("preserve evaluation of a mutable generic polynomial leaf")
	void preserveEvaluationOfMutableGenericPolynomialLeaf() {
		MutablePolynomial leaf = new MutablePolynomial();
		Polynomial sum = PolynomialComp.simplified(
				ArithOperator.PLUS, leaf, new PolynomialConst(2));

		leaf.setValue(5);
		assertEquals(7, sum.integerValue(null));
		leaf.setValue(null);
		assertNull(sum.integerValue(null));

		Polynomial sumWithVariable = PolynomialComp.simplified(
				ArithOperator.PLUS, leaf, new PolynomialVar(new Variable()));
		leaf.setValue(5);
		leaf.resetEvaluationCount();
		assertNull(sumWithVariable.integerValue(null));
		assertEquals(1, leaf.getEvaluationCount());

		MutablePolynomialConst constantSubclass = new MutablePolynomialConst();
		Polynomial sumWithSubclass = PolynomialComp.simplified(
				ArithOperator.PLUS, constantSubclass, new PolynomialConst(2));
		constantSubclass.setCustomValue(5);
		constantSubclass.resetEvaluationCount();
		for (int i = 0; i < 70; i++)
			assertEquals(7, sumWithSubclass.integerValue(null));
		assertEquals(70, constantSubclass.getEvaluationCount());
	}

	@Test
	@DisplayName("repeatedly evaluate mutable native coefficient leaves")
	void repeatedlyEvaluateMutableNativeCoefficientLeaves() {
		PolynomialConst left = new PolynomialConst();
		PolynomialConst right = new PolynomialConst();
		PolynomialConst factor = new PolynomialConst();
		Polynomial sum = PolynomialComp.simplified(
				ArithOperator.PLUS, left, right);
		Polynomial product = PolynomialComp.simplified(
				ArithOperator.TIMES, sum, factor);

		left.setValue(Integer.MAX_VALUE);
		right.setValue(1);
		factor.setValue(2);
		for (int i = 0; i < 70; i++)
			assertEquals(0, product.integerValue(null));

		left.setValue(1);
		right.setValue(2);
		factor.setValue(3);
		assertEquals(9, product.integerValue(null));
		right.setValue(null);
		assertNull(product.integerValue(null));
		right.setValue(-2);
		assertEquals(-3, product.integerValue(null));
	}

	@Test
	@DisplayName("share a compiled evaluation plan across threads")
	void shareCompiledEvaluationPlanAcrossThreads() throws Exception {
		PolynomialConst left = new PolynomialConst();
		PolynomialConst right = new PolynomialConst();
		Polynomial sum = PolynomialComp.simplified(
				ArithOperator.PLUS, left, right);
		left.setValue(2);
		right.setValue(3);
		for (int i = 0; i < 70; i++)
			assertEquals(5, sum.integerValue(null));

		List<Future<Integer>> evaluations = new ArrayList<>();
		try (ExecutorService executor = Executors.newFixedThreadPool(4)) {
			for (int i = 0; i < 100; i++)
				evaluations.add(executor.submit(() -> sum.integerValue(null)));
		}

		for (Future<Integer> evaluation : evaluations)
			assertEquals(5, evaluation.get());
	}

	@Test
	@DisplayName("simplify native derivative operands once with current coefficients")
	void simplifyNativeDerivativeOperandsOnceWithCurrentCoefficients() {
		Variable variable = new Variable();
		Polynomial variablePolynomial = new PolynomialVar(variable);
		PolynomialConst quadraticCoefficient = new PolynomialConst();
		PolynomialConst linearCoefficient = new PolynomialConst();
		Polynomial square = PolynomialComp.simplified(
				ArithOperator.TIMES, variablePolynomial, variablePolynomial);
		Polynomial quadratic = PolynomialComp.simplified(
				ArithOperator.TIMES, quadraticCoefficient, square);
		Polynomial linear = PolynomialComp.simplified(
				ArithOperator.TIMES, linearCoefficient, variablePolynomial);
		Polynomial polynomial = PolynomialComp.simplified(
				ArithOperator.PLUS, quadratic, linear);

		quadraticCoefficient.setValue(2);
		linearCoefficient.setValue(3);
		Polynomial derivative = polynomial.partialDerivative(variable);
		assertEquals(19, derivative.integerValue(Map.of(variable, 4)));

		quadraticCoefficient.setValue(0);
		linearCoefficient.setValue(5);
		assertEquals(3, derivative.integerValue(Map.of(variable, 4)));
		assertEquals(
				5,
				polynomial.partialDerivative(variable)
						.integerValue(Map.of(variable, 4)));
	}

	@Test
	@DisplayName("retain generic derivative simplification")
	void retainGenericDerivativeSimplification() {
		Variable variable = new Variable();
		MutablePolynomial custom = new MutablePolynomial();
		MutablePolynomial customDerivative = new MutablePolynomial();
		customDerivative.setSimplificationResult(PolynomialConst.ONE);
		custom.setDerivative(customDerivative);
		Polynomial polynomial = PolynomialComp.simplified(
				ArithOperator.PLUS, custom, new PolynomialVar(variable));

		customDerivative.resetSimplificationCount();
		Polynomial derivative = polynomial.partialDerivative(variable);

		assertEquals(2, derivative.integerValue(null));
		assertEquals(1, customDerivative.getSimplificationCount());
	}

	private static final class MutablePolynomial implements Polynomial {
		private Integer value;
		private int evaluationCount;
		private Polynomial derivative = PolynomialConst.ZERO;
		private Polynomial simplificationResult = this;
		private int simplificationCount;

		void setValue(Integer value) {
			this.value = value;
		}

		void resetEvaluationCount() {
			this.evaluationCount = 0;
		}

		int getEvaluationCount() {
			return this.evaluationCount;
		}

		void setDerivative(Polynomial derivative) {
			this.derivative = derivative;
		}

		void setSimplificationResult(Polynomial simplificationResult) {
			this.simplificationResult = simplificationResult;
		}

		void resetSimplificationCount() {
			this.simplificationCount = 0;
		}

		int getSimplificationCount() {
			return this.simplificationCount;
		}

		@Override
		public Polynomial partialDerivative(Variable variable) {
			return this.derivative;
		}

		@Override
		public Polynomial replaceWithMu(
				Deque<Variable> variables, PolynomialConst mu) {
			return this;
		}

		@Override
		public Integer integerValue(Map<Variable, Integer> interpretation) {
			this.evaluationCount++;
			return this.value;
		}

		@Override
		public Polynomial simplify() {
			this.simplificationCount++;
			return this.simplificationResult;
		}

		@Override
		public boolean contains(Variable variable) {
			return false;
		}

		@Override
		public Collection<Polynomial> getMonomials() {
			return List.of(this);
		}

		@Override
		public boolean gez() {
			return false;
		}

		@Override
		public boolean gtz() {
			return false;
		}

		@Override
		public boolean lez() {
			return false;
		}

		@Override
		public boolean ltz() {
			return false;
		}

		@Override
		public PolynomialConst[] subOperands() {
			return null;
		}

		@Override
		public String toString(Map<Variable, String> variables) {
			return "mutable";
		}
	}

	private static final class MutablePolynomialConst extends PolynomialConst {
		private Integer customValue;
		private int evaluationCount;

		void setCustomValue(Integer customValue) {
			this.customValue = customValue;
		}

		void resetEvaluationCount() {
			this.evaluationCount = 0;
		}

		int getEvaluationCount() {
			return this.evaluationCount;
		}

		@Override
		public Integer integerValue(Map<Variable, Integer> interpretation) {
			this.evaluationCount++;
			return this.customValue;
		}
	}
}
