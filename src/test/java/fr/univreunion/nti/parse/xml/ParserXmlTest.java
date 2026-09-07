/*
 * Copyright 2025 Etienne Payet <etiennepayet at univ-reunion.fr>
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

package fr.univreunion.nti.parse.xml;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;

import org.junit.jupiter.api.Test;

import fr.univreunion.nti.parse.SyntaxException;
import fr.univreunion.nti.program.trs.RuleTrs;
import fr.univreunion.nti.program.trs.Trs;
import fr.univreunion.nti.term.Function;

class ParserXmlTest {

	@Test
	void parsesOrderedRulesNestedTermsAndSharedRuleVariables() throws IOException {
		Trs program = parse("""
				<?xml version="1.0"?>
				<?xml-stylesheet type="text/xsl"?>
				<problem><trs><rules>
				  <rule>
				    <lhs><funapp><name>xml_test_f</name>
				      <arg><var>X</var></arg>
				      <arg><funapp><name>xml_test_g</name><arg><var>Y</var></arg></funapp></arg>
				    </funapp></lhs>
				    <rhs><funapp><name>xml_test_h</name>
				      <arg><var>Y</var></arg><arg><var>X</var></arg>
				    </funapp></rhs>
				  </rule>
				  <rule>
				    <lhs><funapp><name>xml_test_k</name></funapp></lhs>
				    <rhs><funapp><name>xml_test_a</name></funapp></rhs>
				  </rule>
				</rules><signature></signature></trs>
				<strategy>FULL</strategy>
				<metainformation><originalfilename>test.trs</originalfilename></metainformation>
				</problem>
				""");
		var rules = program.iterator();
		RuleTrs firstRule = rules.next();
		RuleTrs secondRule = rules.next();
		Function firstLeft = firstRule.getLeft();
		Function nestedLeft = (Function) firstLeft.getChild(1);
		Function firstRight = (Function) firstRule.getRight();

		assertEquals("test.xml", program.getName());
		assertEquals("FULL", program.getStrategy());
		assertEquals(2, program.size());
		assertEquals("xml_test_f", firstLeft.getRootSymbol().getName());
		assertEquals("xml_test_g", nestedLeft.getRootSymbol().getName());
		assertSame(firstLeft.getChild(0), firstRight.getChild(1));
		assertSame(nestedLeft.getChild(0), firstRight.getChild(0));
		assertEquals("xml_test_k", secondRule.getLeft().getRootSymbol().getName());
	}

	@Test
	void acceptsEmptyRulesSignatureAndAbsentMetadata() throws IOException {
		Trs program = parse(minimalDocument(""));

		assertEquals(0, program.size());
		assertEquals("FULL", program.getStrategy());
	}

	@Test
	void parsesWideFunctionsWithoutRecursiveArgumentParsing() throws IOException {
		int arity = 5_000;
		String arguments = "<arg><var>X</var></arg>".repeat(arity);
		Trs program = parse(documentWithRules("""
				<rule>
				  <lhs><funapp><name>xml_test_wide</name>%s</funapp></lhs>
				  <rhs><var>X</var></rhs>
				</rule>
				""".formatted(arguments), ""));

		assertEquals(arity,
				program.iterator().next().getLeft().getRootSymbol().getArity());
	}

	@Test
	void ignoresMetadataContentsAndTrailingTokens() throws IOException {
		Trs program = parse(minimalDocument("""
				<metainformation>
				  <author>First Last</author><date>2026-08-14</date>
				  <comment>arbitrary metadata text</comment>
				</metainformation>
				""") + "<problem>");

		assertEquals(0, program.size());
	}

	@Test
	void reportsUnexpectedTermsAndInvalidAritiesAsSyntaxErrors() {
		SyntaxException unexpectedTerm = assertThrows(SyntaxException.class,
				() -> parse(documentWithRules("""
						<rule>
						  <lhs><funapp><name>xml_test_bad</name></funapp></lhs>
						  <rhs></rhs>
						</rule>
						""", "")));
		assertEquals("syntax error at line 5: OPEN_VAR_TAG or OPEN_FUNAPP_TAG expected, "
				+ "CLOSE_RHS_TAG found instead", unexpectedTerm.getMessage());
		assertEquals(5, unexpectedTerm.getLineNumber());

		SyntaxException nonIntegerArity = assertThrows(SyntaxException.class,
				() -> parse(documentWithRules("", """
						<funcsym><name>xml_test_bad</name><arity>many</arity></funcsym>
						""")));
		assertEquals("arity at line 3 is not an integer", nonIntegerArity.getMessage());
		assertEquals(3, nonIntegerArity.getLineNumber());

		SyntaxException negativeArity = assertThrows(SyntaxException.class,
				() -> parse(documentWithRules("", """
						<funcsym><name>xml_test_bad</name><arity>-1</arity></funcsym>
						""")));
		assertEquals("arity at line 3 is not a positive integer", negativeArity.getMessage());
		assertEquals(3, negativeArity.getLineNumber());
	}

	@Test
	void reportsMetadataEndingAtEndOfInput() {
		SyntaxException exception = assertThrows(SyntaxException.class, () -> parse("""
				<?xml version="1.0"?>
				<problem><trs><rules></rules><signature></signature></trs>
				<strategy>FULL</strategy><metainformation><author>name</author>
				"""));

		assertEquals("syntax error at line 4: CLOSE_METAINFO_TAG expected, DONE found instead",
				exception.getMessage());
		assertEquals(4, exception.getLineNumber());
	}

	private static String minimalDocument(String metadata) {
		return documentWithRules("", "").replace("</problem>", metadata + "</problem>");
	}

	private static String documentWithRules(String rules, String signature) {
		return """
				<?xml version="1.0"?>
				<problem><trs><rules>
				%s</rules><signature>%s</signature></trs>
				<strategy>FULL</strategy></problem>
				""".formatted(rules, signature);
	}

	private static Trs parse(String source) throws IOException {
		try (BufferedReader input = new BufferedReader(new StringReader(source))) {
			return (Trs) new ParserXml("test.xml", new ScannerXml(input)).parse();
		}
	}
}
