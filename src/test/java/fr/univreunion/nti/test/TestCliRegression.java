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

package fr.univreunion.nti.test;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import static java.nio.charset.StandardCharsets.UTF_8;
import static org.junit.jupiter.api.Assertions.*;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.TimeUnit;

public class TestCliRegression {
    private static final Duration CLI_TIMEOUT = Duration.ofSeconds(10);

    @TempDir
    Path tempDir;

    @Test
    void helpPrintsUsage() throws Exception {
        CliResult result = runCli("-h");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("Usage: java -jar nti.jar"));
        assertTrue(result.stdout().contains("-prove"));
        assertTrue(result.stdout().contains("direct nontermination techniques"));
        assertTrue(result.stdout().contains("dependency pair (DP) framework"));
        assertTrue(result.stdout().contains("-vv: very verbose mode"));
        assertTrue(result.stdout().contains("-cti=path"));
        assertFalse(result.stdout().contains("-cTI="));
        assertFalse(result.stdout().contains("-t="));
        assertTrue(result.stdout().contains("GNU timeout"));
        assertNoCrash(result);
    }

    @Test
    void versionPrintsCurrentVersion() throws Exception {
        CliResult result = runCli("--version");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("NTI (May 2026)"));
        assertNoCrash(result);
    }

    @Test
    void regularTreeLanguageProvesTheSRule() throws Exception {
        CliResult result = runCli(Path.of(
                "src", "test", "resources", "regular-language", "s.ari")
                .toString());

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().startsWith("NO"));
        assertTrue(result.stdout().contains(
                "finite-tree-automaton regular language"));
        assertTrue(result.stdout().contains(
                "All three obligations were checked independently"));
        assertNoCrash(result);
    }

    @Test
    void noArgumentPrintsMissingFileMessage() throws Exception {
        CliResult result = runCli();

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("No suitable file to analyze"));
        assertNoCrash(result);
    }

    @Test
    void printLogicProgram() throws Exception {
        Path program = writeLogicProgram();

        CliResult result = runCli(program.toString(), "-print");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("while("));
        assertTrue(result.stdout().contains("gt("));
        assertTrue(result.stdout().contains("add("));
        assertNoCrash(result);
    }

    @Test
    void printLargeAriWithoutBuildingDependencyGraph() throws Exception {
        Path program = writeLargeAriProgram();

        CliResult result = runCli(program.toString(), "-print");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("* 2000 rule(s):"));
        assertNoCrash(result);
    }

    @Test
    void printStatsForLogicProgram() throws Exception {
        Path program = writeLogicProgram();

        CliResult result = runCli(program.toString(), "-stat");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("** BEGIN STATS for program:"));
        assertTrue(result.stdout().contains("* 5 rule(s)"));
        assertTrue(result.stdout().contains("** END STATS for program:"));
        assertNoCrash(result);
    }

    @Test
    void patternUnfoldLogicProgramOnce() throws Exception {
        Path program = writeLogicProgram();

        CliResult result = runCli(program.toString(), "-patunf=1");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("not implemented yet for logic programs"));
        assertNoCrash(result);
    }

    @Test
    void patternUnfoldTermRewriteSystemOnce() throws Exception {
        Path program = writeTermRewriteSystem();

        CliResult result = runCli(program.toString(), "-patunf=1");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("while("));
        assertTrue(result.stdout().contains("hat["));
        assertNoCrash(result);
    }

    @Test
    void actionCanAppearBeforeFile() throws Exception {
        Path program = writeLogicProgram();

        CliResult result = runCli("-print", program.toString());

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("while("));
        assertNoCrash(result);
    }

    @Test
    void verboseReverseProofDoesNotContainInternalException() throws Exception {
        Path program = writeReverseProgram();

        CliResult result = runCli(program.toString(), "-v");

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().contains("** BEGIN proof description **"));
        assertStableLpAttemptSummary(result.stdout());
        assertFalse(result.stdout().contains(
                "* Detailed concurrent LP proof attempts:"));
        assertNoCrash(result);
    }

    @Test
    void nonVerboseProofOmitsConcurrentAttemptSummary() throws Exception {
        Path program = writePermuteProgram();

        CliResult result = runCli(program.toString());

        assertEquals(0, result.exitCode());
        assertFalse(result.stdout().contains("* Concurrent LP proof attempts:"));
        assertNoCrash(result);
    }

    @Test
    void verboseTrsProofContainsStableAttemptSummaryAfterDecisiveProof()
            throws Exception {
        Path program = writeDependencyPairTermRewriteSystem();

        for (int run = 0; run < 5; run++) {
            CliResult result = runCli(program.toString(), "-v");

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"));
            assertStableTrsAttemptSummary(result.stdout());
            assertFalse(result.stdout().contains(
                    "* Detailed concurrent TRS proof attempts:"));
            assertNoCrash(result);
        }
    }

    @Test
    void nonVerboseTrsProofOmitsConcurrentAttemptSummary() throws Exception {
        Path program = writeDependencyPairTermRewriteSystem();

        CliResult result = runCli(program.toString());

        assertEquals(0, result.exitCode());
        assertTrue(result.stdout().startsWith("NO"));
        assertFalse(result.stdout().contains("* Concurrent TRS proof attempts:"));
        assertNoCrash(result);
    }

    @Test
    void rootClosingLookaheadRetainsHistoricalHydraProofs() throws Exception {
        Path hydras = Path.of("src", "test", "resources", "examples", "Hydras");

        for (int index : List.of(4, 5, 6, 8, 9, 10)) {
            CliResult result = runCli(
                    hydras.resolve("lepper_" + index + ".ari").toString());

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"),
                    () -> "lepper_" + index + ": " + result.stdout());
            assertTrue(result.stdout().contains(
                    "J2(S(l(_0)),l(_1),_2) is non-terminating"));
            assertNoCrash(result);
        }
    }

    @Test
    void unaryMarkerShuttleProvesFourZantemaExamples() throws Exception {
        for (int index : List.of(1, 4, 8, 9)) {
            Path program = Path.of("src", "test", "resources", "examples", "Zantema_15",
                    "ex%02d.ari".formatted(index));

            CliResult result = runCli(program.toString());

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"),
                    () -> "ex%02d: %s".formatted(index, result.stdout()));
            assertTrue(result.stdout().contains(
                    "bounded unary-shuttle growth recognition"));
            assertNoCrash(result);
        }
    }

    @Test
    void modularBlockShuttleProvesBothZantemaExamples() throws Exception {
        for (int index : List.of(2, 3)) {
            Path program = Path.of("src", "test", "resources", "examples", "Zantema_15",
                    "ex%02d.ari".formatted(index));

            CliResult result = runCli(program.toString());

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"),
                    () -> "ex%02d: %s".formatted(index, result.stdout()));
            assertTrue(result.stdout().contains(
                    "bounded unary-shuttle growth recognition"));
            assertTrue(result.stdout().contains("Selected residue table"));
            assertNoCrash(result);
        }
    }

    @Test
    void arithmeticCounterGrowthProvesBothEmmesEx2Examples() throws Exception {
        Path examples = Path.of(
                "src", "test", "resources", "examples", "EEG_IJCAR_12");

        for (String name : List.of(
                "emmes-nonloop-ex2_4.ari",
                "emmes-nonloop-ex2_5.ari")) {
            CliResult result = runCli(examples.resolve(name).toString());

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"),
                    () -> name + ": " + result.stdout());
            assertTrue(result.stdout().contains(
                    "bounded unary-counter growth recognition"));
            assertTrue(result.stdout().contains(
                    "Starting with (p0,q0) = (2,1)"));
            assertNoCrash(result);
        }
    }

    @Test
    void guardedListGrowthProvesThreeAddExamples() throws Exception {
        for (Path program : List.of(
                Path.of("src", "test", "resources", "examples", "EEG_IJCAR_12",
                        "enger-nonloop-add.ari"),
                Path.of("src", "test", "resources", "examples", "EEG_IJCAR_12",
                        "enger-nonloop-addTrue.ari"),
                Path.of("src", "test", "resources", "examples", "AProVE_10",
                        "ex4.ari"))) {
            CliResult result = runCli(program.toString());

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"),
                    () -> program + ": " + result.stdout());
            assertTrue(result.stdout().contains(
                    "bounded list-growth recognition"));
            assertNoCrash(result);
        }
    }

	@Test
	void guardedEvaluatorGrowthProvesThreeCrossFamilyExamples() throws Exception {
		for (Path program : List.of(
				Path.of("src", "test", "resources", "examples", "AProVE_10",
						"challenge_fab.ari"),
				Path.of("src", "test", "resources", "examples", "AProVE_10",
						"downfrom.ari"),
				Path.of("src", "test", "resources", "examples", "Zantema_15",
						"ex05.ari"))) {
			CliResult result = runCli(program.toString());

			assertEquals(0, result.exitCode());
			assertTrue(result.stdout().startsWith("NO"),
					() -> program + ": " + result.stdout());
			assertTrue(result.stdout().contains(
					"bounded guarded evaluator-growth recognition"));
			assertTrue(result.stdout().contains("W(n+1)"));
			assertTrue(result.stdout().contains(
					"Total number of generated unfolded rules = 0"));
			assertNoCrash(result);
		}
	}

    @Test
    void symbolicEvaluatorProvesBothEmmesEx6Examples() throws Exception {
        Path examples = Path.of(
                "src", "test", "resources", "examples", "EEG_IJCAR_12");

        for (String name : List.of(
                "emmes-nonloop-ex6_1.ari",
                "emmes-nonloop-ex6_2.ari")) {
            CliResult result = runCli(examples.resolve(name).toString());

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"),
                    () -> name + ": " + result.stdout());
            assertTrue(result.stdout().contains(
                    "bounded list-growth recognition"));
            assertTrue(result.stdout().contains("symbolic evaluator path"));
            assertNoCrash(result);
        }
    }

    @Test
    void lengthGuardedGrowthProvesFiveEmmesEx7Examples() throws Exception {
        for (int index : List.of(1, 2, 4, 7, 9)) {
            String name = "emmes-nonloop-ex7_" + index + ".ari";
            Path program = Path.of(
                    "src", "test", "resources", "examples", "EEG_IJCAR_12", name);
            CliResult result = runCli(program.toString());

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"),
                    () -> name + ": " + result.stdout());
            assertTrue(result.stdout().contains(
                    "bounded list-growth recognition"));
            assertTrue(result.stdout().contains(
                    "guard reduces to true in 3n+5 steps"));
            assertNoCrash(result);
        }
    }

    @Test
    void verbosePermuteProofAlwaysContainsContributingDescription() throws Exception {
        Path program = writePermuteProgram();

        for (int run = 0; run < 5; run++) {
            CliResult result = runCli(program.toString(), "-v");

            assertEquals(0, result.exitCode());
            assertTrue(result.stdout().startsWith("NO"));
            assertTrue(result.stdout().contains("* [Binary unfolding]"));
            assertTrue(result.stdout().contains(
                    "The mode permute(o,i) is nonterminating."));
            assertTrue(result.stdout().contains(
                    "; contributed an accepted witness"));
            assertEquals(1, countOccurrences(
                    result.stdout(),
                    "The mode permute(o,i) is nonterminating."));
            assertStableLpAttemptSummary(result.stdout());
            assertNoCrash(result);
        }
    }

    @Test
    void veryVerboseLpProofDisplaysEveryRetainedAttemptInStableOrder()
            throws Exception {
        Path program = writePermuteProgram();

        for (int run = 0; run < 3; run++) {
            CliResult result = runCli(program.toString(), "-vv");

            assertEquals(0, result.exitCode());
            int summaryIndex = result.stdout().indexOf(
                    "* Concurrent LP proof attempts:");
            int detailsIndex = result.stdout().indexOf(
                    "* Detailed concurrent LP proof attempts:");
            int binaryIndex = result.stdout().indexOf(
                    "  ** Binary unfolding:", detailsIndex);
            int patternIndex = result.stdout().indexOf(
                    "  ** Pattern unfolding:", detailsIndex);
            assertTrue(summaryIndex >= 0);
            assertTrue(detailsIndex > summaryIndex);
            assertTrue(binaryIndex > detailsIndex);
            assertTrue(patternIndex > binaryIndex);
            assertEquals(detailsIndex, result.stdout().lastIndexOf(
                    "* Detailed concurrent LP proof attempts:"));
            assertTrue(result.stdout().contains("[retained trace]")
                    || result.stdout().contains("[partial trace retained]"));
            assertNoCrash(result);
        }
    }

    @Test
    void veryVerboseTrsProofDisplaysOuterAndInnerWorkInStableOrder()
            throws Exception {
        Path program = writeDependencyPairTermRewriteSystem();

        for (int run = 0; run < 3; run++) {
            CliResult result = runCli(program.toString(), "-vv");

            assertEquals(0, result.exitCode());
            int summaryIndex = result.stdout().indexOf(
                    "* Concurrent TRS proof attempts:");
            int detailsIndex = result.stdout().indexOf(
                    "* Detailed concurrent TRS proof attempts:");
            int unfilteredIndex = result.stdout().indexOf(
                    "  ** Unfiltered:", detailsIndex);
            int firstProcessorIndex = result.stdout().indexOf(
                    "    ** problem 1 / processor 1 (", unfilteredIndex);
            int filteredIndex = result.stdout().indexOf(
                    "  ** Argument-filtered:", unfilteredIndex);
            assertTrue(summaryIndex >= 0);
            assertTrue(detailsIndex > summaryIndex);
            assertTrue(unfilteredIndex > detailsIndex);
            assertTrue(firstProcessorIndex > unfilteredIndex);
            assertTrue(filteredIndex > firstProcessorIndex);
            assertEquals(detailsIndex, result.stdout().lastIndexOf(
                    "* Detailed concurrent TRS proof attempts:"));
            assertNoCrash(result);
        }
    }

    private static void assertStableLpAttemptSummary(String output) {
        int headingIndex = output.indexOf("* Concurrent LP proof attempts:");
        int binaryIndex = output.indexOf("  - Binary unfolding:", headingIndex);
        int patternIndex = output.indexOf("  - Pattern unfolding:", headingIndex);

        assertTrue(headingIndex >= 0);
        assertTrue(binaryIndex > headingIndex);
        assertTrue(patternIndex > binaryIndex);
        assertEquals(headingIndex,
                output.lastIndexOf("* Concurrent LP proof attempts:"));
    }

    private static void assertStableTrsAttemptSummary(String output) {
        int decisiveProofIndex = output.indexOf("This DP problem is infinite.");
        int headingIndex = output.indexOf("* Concurrent TRS proof attempts:");
        int unfilteredIndex = output.indexOf("  - Unfiltered:", headingIndex);
        int firstProcessorIndex = output.indexOf(
                "    - problem 1 / processor 1 (", unfilteredIndex);
        int secondProcessorIndex = output.indexOf(
                "    - problem 1 / processor 2 (", firstProcessorIndex);
        int thirdProcessorIndex = output.indexOf(
                "    - problem 1 / processor 3 (", secondProcessorIndex);
        int fourthProcessorIndex = output.indexOf(
                "    - problem 1 / processor 4 (", thirdProcessorIndex);
        int filteredIndex = output.indexOf(
                "  - Argument-filtered:", unfilteredIndex);
        int descriptionEndIndex = output.indexOf(
                "** END proof description **", headingIndex);

        assertTrue(decisiveProofIndex >= 0);
        assertTrue(headingIndex > decisiveProofIndex);
        assertTrue(unfilteredIndex > headingIndex);
        assertTrue(firstProcessorIndex > unfilteredIndex);
        assertTrue(secondProcessorIndex > firstProcessorIndex);
        assertTrue(thirdProcessorIndex > secondProcessorIndex);
        assertTrue(fourthProcessorIndex > thirdProcessorIndex);
        assertTrue(filteredIndex > fourthProcessorIndex);
        assertTrue(descriptionEndIndex > filteredIndex);
        assertEquals(headingIndex,
                output.lastIndexOf("* Concurrent TRS proof attempts:"));
    }

    private static int countOccurrences(String text, String fragment) {
        int count = 0;
        int fromIndex = 0;
        while ((fromIndex = text.indexOf(fragment, fromIndex)) >= 0) {
            count++;
            fromIndex += fragment.length();
        }
        return count;
    }

    private Path writeLogicProgram() throws IOException {
        Path file = this.tempDir.resolve("while-add.pl");
        Files.writeString(file, """
				%query: while(i,i).
				while(X,Y) :- gt(X,Y), add(X,Y,Z), while(Z,s(Y)).
				gt(s(X),0).
				gt(s(X),s(Y)) :- gt(X,Y).
				add(X,0,X).
				add(X,s(Y),s(Z)) :- add(X,Y,Z).
				""", UTF_8);
        return file;
    }

    private Path writeTermRewriteSystem() throws IOException {
        Path file = this.tempDir.resolve("while-add.trs");
        Files.writeString(file, """
				(VAR X)
				(VAR Y)
				(VAR Z)
				(RULES
				while(true, X, Y) -> while(gt(X, Y), add(X, Y), s(Y))
				gt(s(X), 0) -> true
				gt(0, Y) -> false
				gt(s(X), s(Y)) -> gt(X, Y)
				add(X, 0) -> X
				add(X, s(Y)) -> s(add(X, Y))
				)
				""", UTF_8);
        return file;
    }

    private Path writeLargeAriProgram() throws IOException {
        Path file = this.tempDir.resolve("large.ari");
        StringBuilder program = new StringBuilder("""
                (format TRS)
                (fun f 1)
                """);
        program.repeat("(rule (f x) (f (f (f (f (f x))))))\n", 2000);
        Files.writeString(file, program, UTF_8);
        return file;
    }

    private Path writeDependencyPairTermRewriteSystem() throws IOException {
        Path file = this.tempDir.resolve("dependency-pair-loop.trs");
        Files.writeString(file, """
                (VAR X)
                (RULES
                f(X) -> f(f(X))
                )
                """, UTF_8);
        return file;
    }

    private Path writeReverseProgram() throws IOException {
        Path file = this.tempDir.resolve("reverse.pl");
        Files.writeString(file, """
				%query: reverse(o,i).
				rev([],R,R).
				rev([X|Xs],R0,R) :- rev(Xs,[X|R0],R).
				reverse(L,R) :- rev(L,[],R).
				""", UTF_8);
        return file;
    }

    private Path writePermuteProgram() throws IOException {
        Path file = this.tempDir.resolve("permute.pl");
        Files.writeString(file, """
				%query: permute(o,i).
				delete(X,[X|Xs],Xs).
				delete(Y,[X|Xs],[X|Ys]) :- delete(Y,Xs,Ys).
				permute([],[]).
				permute([X|Xs],[Y|Ys]) :-
				    delete(Y,[X|Xs],Zs), permute(Zs,Ys).
				""", UTF_8);
        return file;
    }

    private static CliResult runCli(String... args) throws Exception {
        List<String> command = new ArrayList<>();
        command.add(javaExecutable().toString());
        command.add("-cp");
        command.add(System.getProperty("java.class.path"));
        command.add("fr.univreunion.nti.Nti");
        command.addAll(List.of(args));

        ProcessBuilder builder = new ProcessBuilder(command);
        builder.directory(Path.of(System.getProperty("user.dir")).toFile());

        Process process = builder.start();

        CompletableFuture<String> stdout =
                CompletableFuture.supplyAsync(() -> readAll(process.getInputStream()));
        CompletableFuture<String> stderr =
                CompletableFuture.supplyAsync(() -> readAll(process.getErrorStream()));

        boolean finished = process.waitFor(CLI_TIMEOUT.toMillis(), TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
            fail("CLI command timed out: " + String.join(" ", command));
        }

        return new CliResult(
                process.exitValue(),
                stdout.get(1, TimeUnit.SECONDS),
                stderr.get(1, TimeUnit.SECONDS));
    }

    private static String readAll(java.io.InputStream input) {
        try (input) {
            return new String(input.readAllBytes(), UTF_8);
        }
        catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static Path javaExecutable() {
        String executable = System.getProperty("os.name").toLowerCase().contains("win")
                ? "java.exe"
                : "java";

        return Path.of(System.getProperty("java.home"), "bin", executable);
    }

    private static void assertNoCrash(CliResult result) {
        assertFalse(result.stdout().contains("Exception"), result.stdout());
        assertFalse(result.stderr().contains("Exception"), result.stderr());
        assertFalse(result.stderr().contains("Error"), result.stderr());
    }

    private record CliResult(int exitCode, String stdout, String stderr) {}
}
