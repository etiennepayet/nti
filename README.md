NTI is a **free software** distributed under the terms of the
[GNU Lesser General Public License](https://www.gnu.org/licenses/lgpl-3.0.html), version 3
or any later version. It is developed and maintained by [Étienne Payet](mailto:etienne.payet@univ-reunion.fr).

Usage: `java -jar nti.jar <file> [action] [options]`

NTI tries to prove (non)termination of the program in the provided file.
- For logic programs, the implemented technique is described in
[[Payet & Mesnard, TOPLAS'06]](http://lim.univ-reunion.fr/staff/epayet/Research/Resources/toplas06.pdf).
- For TRSs, the implemented technique uses the dependency pair (DP) framework:
first, it decomposes the initial set of DP problems into subproblems using
sound DP processors, then it tries to prove that the unsolved subproblems
are infinite using the approaches of [[Payet, TCS'08]](http://lim.univ-reunion.fr/staff/epayet/Research/Resources/tcs08.pdf),
[[Payet, LOPSTR'18]](http://arxiv.org/abs/1808.05065) and
[[Payet, JAR'24]](https://arxiv.org/abs/2312.13949).

`file` has to conform to the TPDB syntax specification
(see [here](http://termination-portal.org/wiki/TPDB) and
[here](https://termination-portal.org/wiki/Term_Rewriting)).
It has one of the following suffixes:
- `.pl`  for a  pure logic program
- `.ari` for a  TRS or an SRS in the ARI format
- `.xml` for a  TRS or an SRS in the old XML format
- `.trs` for a  TRS in the old, human readable, format
- `.srs` for an SRS in the old, human readable, format

`action` (optional) can be:
- `-h|--help`: print this help
- `--version`: print the version of NTI
- `-print`: print the program in the given file
- `-stat`: print some statistics about the program in the given file
- `-prove`: run a (non)termination proof of the program in the given file
**(THIS IS THE DEFAULT ACTION)**

`options` (optional) can be:
- `-v`: verbose mode (for printing proof details in the final output)
- `-t=n`: set a time bound on the nontermination proofs (`n` is the time bound in seconds)
- `-cTI=path`: set the path to cTI (for proving termination of logic programs)  
If no path to cTI is set, then only nontermination proofs are run for logic programs
