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

package fr.univreunion.nti.parse;

import fr.univreunion.nti.parse.ari.ParserAri;
import fr.univreunion.nti.parse.ari.ScannerAri;
import fr.univreunion.nti.parse.lp.ParserLp;
import fr.univreunion.nti.parse.lp.ScannerLp;
import fr.univreunion.nti.parse.srs.ParserSrs;
import fr.univreunion.nti.parse.srs.ScannerSrs;
import fr.univreunion.nti.parse.trs.ParserTrs;
import fr.univreunion.nti.parse.trs.ScannerTrs;
import fr.univreunion.nti.parse.xml.ParserXml;
import fr.univreunion.nti.parse.xml.ScannerXml;
import fr.univreunion.nti.program.Program;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

/**
 * A factory for creating programs from supported input files.
 *
 * <p>Supported program types include logic programs (LP), string rewrite
 * systems (SRS), term rewrite systems (TRS), and related input formats.</p>
 *
 * @author <A HREF="mailto:etienne.payet@univ-reunion.fr">Etienne Payet</A>
 */

public final class ProgramFactory {

    private ProgramFactory() {}

    /**
     * Parses the program stored in the specified file.
     *
     * <p>The parser is selected from the file extension. Supported extensions are
     * {@code .pl}, {@code .ari}, {@code .xml}, {@code .trs}, and {@code .srs}.</p>
     *
     * @param fileName the name of the file storing the program to parse
     * @return the parsed program
     * @throws IOException if an I/O error occurs while reading the file
     * @throws IllegalArgumentException if the file extension is not supported
     */
    public static Program parse(String fileName) throws IOException {
        try (BufferedReader input = new BufferedReader(new FileReader(fileName))) {
            if (fileName.endsWith(".pl"))
                return new ParserLp(fileName, new ScannerLp(input)).parse();

            if (fileName.endsWith(".ari"))
                return new ParserAri(fileName, new ScannerAri(input)).parse();

            if (fileName.endsWith(".xml"))
                return new ParserXml(fileName, new ScannerXml(input)).parse();

            if (fileName.endsWith(".trs"))
                return new ParserTrs(fileName, new ScannerTrs(input)).parse();

            if (fileName.endsWith(".srs"))
                return new ParserSrs(fileName, new ScannerSrs(input)).parse();
        }

        throw new IllegalArgumentException("unsupported program file: " + fileName);
    }
}
