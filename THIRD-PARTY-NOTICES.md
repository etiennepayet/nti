# Third-party notices

NTI's executable jar includes the following third-party software. These
notices do not change NTI's own license.

## SAT4J Core 2.3.6

The copyright, contributor, and third-party notices for SAT4J are detailed
in the `about.html` file distributed with SAT4J and retained in NTI's
executable jar.

SAT4J is available under a choice of the Eclipse Public License version 1.0
or the GNU Lesser General Public License version 2.1 or later. NTI uses and
redistributes SAT4J under the GNU Lesser General Public License version 2.1
or later. For this distribution, NTI applies version 3 under SAT4J's
"or later" option.

The GNU GPL version 3 and GNU LGPL version 3 license texts are provided in
`COPYING.md` and `COPYING.LESSER.md`. They are also included under
`META-INF/licenses/` in the executable jar.

The exact corresponding source archive for the embedded SAT4J version is:

<https://repo.maven.apache.org/maven2/org/ow2/sat4j/org.ow2.sat4j.core/2.3.6/org.ow2.sat4j.core-2.3.6-sources.jar>

Its SHA-1 digest is `e820dd6100c304e9bb270b5132d6e5607dcd6e7d`.
The upstream project and release information are available at:

- <https://www.sat4j.org/>
- <https://gitlab.ow2.org/sat4j/sat4j/-/releases/2_3_6>

The source code and build files for NTI are distributed in this repository.
To rebuild the combined executable jar, including after replacing SAT4J with
an interface-compatible modified version, set the `sat4j.version` property in
`pom.xml` to the Maven version of that replacement and run:

```shell
./mvnw clean package
```

A locally modified SAT4J artifact can first be installed into a local Maven
repository under a distinct version, then selected through
`-Dsat4j.version=that-version` when invoking Maven. NTI does not restrict
reverse engineering performed for debugging modifications to SAT4J.

Any redistribution of NTI's executable jar must be accompanied by the
corresponding NTI and SAT4J source code, or by another source-distribution
mechanism permitted by the GNU GPL and GNU LGPL, so that recipients can
rebuild and relink the combined work.

### MiniSat-derived portions

SAT4J's `org.sat4j.core.Vec`, `org.sat4j.core.VecInt`, and
`org.sat4j.minisat.core.Solver` contain code derived from MiniSat 1.1.4,
copyright 2003-2005 Niklas Eén and Niklas Sörensson, under a permissive
license. The complete copyright, permission, and warranty notice is retained
in SAT4J's `about.html` file in the executable jar.
