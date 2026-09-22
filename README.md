### Finding a Positive Index Nash Equilibrium is PPADS-Complete

This repository provides `verify_turn_tables.wl`, a Mathematica/Wolfram Language script for checking the four turn tables in Lemma 4.5 of *Finding a Positive Index Nash Equilibrium is PPADS-Complete*. Using exact integer and rational arithmetic, it enumerates all 432 relevant cubes and 2,592 Kuhn tetrahedra, checks the completeness of Table 3 and its 102 missing-color certificates, and verifies the incoming and outgoing boundary agreements. It also uses `Resolve` to check that the affine interpolant has no zero anywhere in each closed tetrahedron, including its faces. To run the checker, evaluate `Get["verify_turn_tables.wl"]` followed by `VerifyTurnTables[]`; a successful run returns a report containing `"AllPassed" -> True`. These checks cover the local three-dimensional construction; the extension to arbitrary dimensions and the global separation and compatibility arguments are established separately in the paper.

- Edit main.nb: change the path used in Get
- Run main.nb in Wolfram Mathematica
