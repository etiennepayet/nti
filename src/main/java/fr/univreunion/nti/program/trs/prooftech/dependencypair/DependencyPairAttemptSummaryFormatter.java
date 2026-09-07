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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with NTI. If not, see <https://www.gnu.org/licenses/>.
 */

package fr.univreunion.nti.program.trs.prooftech.dependencypair;

import java.util.List;

import fr.univreunion.nti.program.Proof;
import fr.univreunion.nti.program.trs.prooftech.dependencypair.processor.DependencyPairProcessorResult;

/**
 * Formats a concise report of concurrent dependency-pair proof attempts.
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */
final class DependencyPairAttemptSummaryFormatter {

	/** This class cannot be instantiated. */
	private DependencyPairAttemptSummaryFormatter() {
		throw new IllegalStateException("Utility class");
	}

	/**
	 * Appends the attempt report to a proof when verbose output is enabled.
	 *
	 * @param proof the proof receiving the report
	 * @param attempts the framework attempts in display order
	 */
	static void appendTo(
			Proof proof, List<DependencyPairFrameworkAttempt> attempts) {

		String detailedReport = proof.isInVeryVerboseMode()
				? formatDetailed(attempts) : null;
		proof.printlnIfVerbose(format(attempts));
		proof.printlnIfVerbose();
		if (detailedReport != null) {
			proof.println(detailedReport);
			proof.println();
		}
	}

	/**
	 * Formats the framework attempts and their retained infiniteness attempts.
	 *
	 * @param attempts the framework attempts in display order
	 * @return the concise attempt report
	 */
	static String format(List<DependencyPairFrameworkAttempt> attempts) {
		StringBuilder summary = new StringBuilder(
				"* Concurrent TRS proof attempts:");
		for (DependencyPairFrameworkAttempt attempt : attempts) {
			summary.append("\n  - ")
					.append(attempt.name())
					.append(": ")
					.append(frameworkState(attempt));
			for (DependencyPairInfinitenessAttempt innerAttempt
					: attempt.infinitenessAttempts()) {
				summary.append("\n    - problem ")
						.append(innerAttempt.problemPosition())
						.append(" / processor ")
						.append(innerAttempt.processorPosition())
						.append(" (")
						.append(innerAttempt.processorIdentity())
						.append("): ")
						.append(infinitenessState(innerAttempt));
			}
		}
		return summary.toString();
	}

	/**
	 * Formats all retained framework and processor traces. The caller invokes
	 * this only after every worker has terminated and before appending anything
	 * to a selected attempt proof, so that the decisive trace remains distinct.
	 *
	 * @param attempts the framework attempts in display order
	 * @return the detailed attempt report
	 */
	static String formatDetailed(
			List<DependencyPairFrameworkAttempt> attempts) {

		StringBuilder details = new StringBuilder(
				"* Detailed concurrent TRS proof attempts:");
		for (DependencyPairFrameworkAttempt attempt : attempts) {
			details.append("\n  ** ")
					.append(attempt.name())
					.append(": ")
					.append(frameworkState(attempt))
					.append(" **");
			appendProofTrace(
					details,
					attempt.proof(),
					attempt.failure(),
					attempt.status()
							== DependencyPairFrameworkAttempt.Status.CANCELLED,
					4);

			for (DependencyPairInfinitenessAttempt innerAttempt
					: attempt.infinitenessAttempts()) {
				details.append("\n    ** problem ")
						.append(innerAttempt.problemPosition())
						.append(" / processor ")
						.append(innerAttempt.processorPosition())
						.append(" (")
						.append(innerAttempt.processorIdentity())
						.append("): ")
						.append(infinitenessState(innerAttempt))
						.append(" **");
				DependencyPairProcessorResult result = innerAttempt.result();
				appendProofTrace(
						details,
						result == null ? null : result.getProof(),
						innerAttempt.failure(),
						innerAttempt.status()
								== DependencyPairInfinitenessAttempt.Status.CANCELLED,
						6);
			}
		}
		return details.toString();
	}

	/** Appends a retained proof or an explicit availability marker. */
	private static void appendProofTrace(
			StringBuilder target,
			Proof proof,
			Throwable failure,
			boolean partial,
			int indentation) {

		String prefix = " ".repeat(Math.max(0, indentation));
		if (failure != null)
			target.append('\n').append(prefix).append("[cause: ")
					.append(conciseFailure(failure)).append(']');
		if (proof == null || (!proof.hasDescription() && !proof.isSuccess())) {
			target.append('\n').append(prefix).append("[trace unavailable]");
			return;
		}

		target.append('\n').append(prefix).append(partial
				? "[partial trace retained]" : "[retained trace]");
		target.append('\n').append(prefix)
				.append(proof.toString().replace("\n", "\n" + prefix));
	}

	/** Returns a one-line description of an exceptional worker failure. */
	private static String conciseFailure(Throwable failure) {
		String message = failure.getMessage();
		String description = failure.getClass().getSimpleName();
		if (message != null && !message.isBlank())
			description += ": " + message;
		return description.replace('\n', ' ').replace('\r', ' ');
	}

	/**
	 * Returns the display state of an outer framework attempt.
	 *
	 * @param attempt the framework attempt to describe
	 * @return its state and optional logical result
	 */
	private static String frameworkState(
			DependencyPairFrameworkAttempt attempt) {

		return switch (attempt.status()) {
			case PENDING -> "pending";
			case RUNNING -> "running";
			case SUCCESSFUL -> "successful" + proofResult(attempt.proof());
			case UNSUCCESSFUL -> "unsuccessful" + proofResult(attempt.proof());
			case ERROR -> "error";
			case CANCELLED -> "cancelled";
		};
	}

	/**
	 * Returns the display state of an inner infiniteness attempt.
	 *
	 * @param attempt the infiniteness attempt to describe
	 * @return its state and optional processor result
	 */
	private static String infinitenessState(
			DependencyPairInfinitenessAttempt attempt) {

		return switch (attempt.status()) {
			case PENDING -> "pending";
			case RUNNING -> "running";
			case SUCCESSFUL -> "successful" + processorResult(attempt.result());
			case UNSUCCESSFUL ->
					"unsuccessful" + processorResult(attempt.result());
			case ERROR -> "error";
			case CANCELLED -> "cancelled";
		};
	}

	/**
	 * Returns a retained proof's logical-result suffix.
	 *
	 * @param proof the retained proof, possibly {@code null}
	 * @return the parenthesized result, or an empty string
	 */
	private static String proofResult(Proof proof) {
		return proof == null ? "" : " (" + proof.getResult() + ")";
	}

	/**
	 * Returns a retained processor-result suffix.
	 *
	 * @param result the retained processor result, possibly {@code null}
	 * @return the parenthesized result, or an empty string
	 */
	private static String processorResult(
			DependencyPairProcessorResult result) {

		return result == null ? "" : " (" + result + ")";
	}
}
