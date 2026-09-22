(*
  Exact verification of Lemma 4.5 and Table 3 in
  "Finding a Positive Index Nash Equilibrium is PPADS-Complete",
  removing_nondegeneracy(1).pdf, pp. 30-31.

  Run in Mathematica / Wolfram Language:
    Get["/absolute/path/verify_turn_tables.wl"];
    report = TurnTableVerification`VerifyTurnTables[];
    report["AllPassed"]

  Optional stronger check of the entire three-coordinate coloring:
    integerReport = TurnTableVerification`VerifyAllIntegerCubes[];
    integerReport["AllPassed"]

  All input numbers are exact integers or rationals. There is no N[],
  numerical optimization, random sampling, or floating-point tolerance.
  A claim passes only when its result is literally True. An unresolved
  Resolve expression, $Failed, or False is never accepted as a proof.

  VerifyTurnTables checks all 4 * 6 * 6 * 3 = 432 cubes and their
  6 * 432 = 2592 Kuhn tetrahedra, all 102 missing-color claims in Table 3,
  completeness of the exceptional-cube lists, all table boundary values,
  and absence of zeros of the affine interpolants using Resolve over Reals.

  Expected finite counts:
    cubes 432; tetrahedra 2592; table entries 200; boundary claims 136;
    exceptional cubes by turn {3,5,5,4}; Table 3 claims 102;
    Boolean-predicate comparisons 3136; affine color multisets 25.

  VerifyAllIntegerCubes checks 4 * 6 = 24 universal statements using
  Resolve over Integers, one for each turn and coordinate permutation.
  This covers the entire local coloring theta, including its infinite
  straight continuations. It does not formalize the global route assembly
  in Proposition 4.10 or the arbitrary-dimensional extension in Lemma 4.6.

  These are exact computer-assisted checks within Wolfram Language's
  trusted implementation, not exported proof-assistant certificates.
  The checker must also be matched to the definitions in the manuscript.
  No Mathematica kernel was available in the authoring environment;
  its finite data and rational linear algebra were independently checked.
*)

BeginPackage["TurnTableVerification`"];

VerifyTurnTables::usage =
  "VerifyTurnTables[] verifies the finite turn tables and affine interpolants exactly, returning a report or Failure.";
VerifyAllIntegerCubes::usage =
  "VerifyAllIntegerCubes[] uses Resolve to verify the local turn coloring on all integer cubes, returning a report or Failure.";

Begin["`Private`"];

caseNames = {"++", "+-", "-+", "--"};
directions = {{1, 1}, {1, -1}, {-1, 1}, {-1, -1}};

(* IMPORTANT: rows are y = 2,1,0,-1,-2; columns are x = -2,-1,0,1,2.
   Within each turn, the first matrix is z=0 and the second is z=1. *)
turnTables = {
  {
    {{0,0,3,3,0}, {3,3,3,0,0}, {3,3,0,0,0},
     {0,0,0,0,0}, {0,0,0,0,0}},
    {{0,0,1,2,0}, {1,1,2,0,0}, {2,2,0,0,0},
     {0,0,0,0,0}, {0,0,0,0,0}}
  },
  {
    {{0,0,0,0,0}, {3,0,0,0,0}, {3,3,1,0,0},
     {0,3,1,0,0}, {0,0,1,2,0}},
    {{0,0,0,0,0}, {1,1,1,0,0}, {2,2,2,2,0},
     {0,0,3,2,0}, {0,0,3,3,0}}
  },
  {
    {{0,0,3,3,0}, {0,0,1,3,1}, {0,0,1,1,2},
     {0,0,0,2,0}, {0,0,0,0,0}},
    {{0,0,1,2,0}, {0,0,0,2,3}, {0,0,0,2,3},
     {0,0,0,0,0}, {0,0,0,0,0}}
  },
  {
    {{0,0,0,0,0}, {0,0,0,0,1}, {0,0,0,1,2},
     {0,0,1,2,0}, {0,0,1,2,0}},
    {{0,0,0,0,0}, {0,0,0,0,3}, {0,0,0,3,3},
     {0,0,0,3,0}, {0,0,3,3,0}}
  }
};

(* Exactly the permutation order used by Table 3:
   (x,y,z), (x,z,y), (y,x,z), (y,z,x), (z,x,y), (z,y,x). *)
permutationList = {{1,2,3}, {1,3,2}, {2,1,3},
                   {2,3,1}, {3,1,2}, {3,2,1}};

(* Each row is {integer lower corner, six claimed missing colors}. *)
paperTable3 = {
  {
    {{-1,0,0}, {1,1,0,0,1,0}},
    {{-1,1,0}, {0,0,2,2,0,2}},
    {{0,1,0},  {1,1,0,0,1,0}}
  },
  {
    {{-2,0,0},  {2,0,2,0,0,0}},
    {{-1,-1,0}, {0,0,0,0,1,1}},
    {{-1,0,0},  {2,0,2,2,0,0}},
    {{0,-2,0},  {3,0,3,0,0,0}},
    {{0,-1,0},  {3,3,3,0,0,0}}
  },
  {
    {{0,0,0},   {0,0,0,3,3,3}},
    {{0,1,0},   {0,0,0,0,3,3}},
    {{1,-1,0},  {1,1,0,0,1,1}},
    {{1,0,-1},  {2,3,2,2,3,2}},
    {{1,1,0},   {2,2,1,1,1,1}}
  },
  {
    {{0,-2,0}, {0,0,0,2,0,2}},
    {{0,-1,0}, {0,0,2,2,2,2}},
    {{1,-1,0}, {1,1,0,0,1,0}},
    {{1,0,0},  {0,0,2,2,0,2}}
  }
};

palette = {{-1,-1,-1}, {1,0,0}, {0,1,0}, {0,0,1}};
cubeCorners = Tuples[{Range[-3,2], Range[-3,2], Range[-1,1]}];
cubeOffsets = Tuples[{0,1}, 3];
tableVertices = Tuples[{Range[-2,2], Range[-2,2], {0,1}}];
verificationTag = "TurnTableVerificationFailure";

require[claim_, name_, details_: Null] :=
  If[!TrueQ[claim],
    Throw[Failure["VerificationFailed",
      <|"Check" -> name, "Result" -> claim, "Details" -> details|>],
      verificationTag]];

beta[s_Integer] := If[s == 1, 0, 1];

(* The two exact integer-grid rules (In-Out). *)
incomingColor[s_Integer, yy_Integer, zz_Integer] := Which[
  !MemberQ[{0,1}, yy] || !MemberQ[{0,1}, zz], 0,
  zz == beta[s], 3,
  yy == 0, 2,
  True, 1
];

outgoingColor[t_Integer, xx_Integer, zz_Integer] := Which[
  !MemberQ[{0,1}, xx] || !MemberQ[{0,1}, zz], 0,
  zz == beta[t], 3,
  xx == 0, 1,
  True, 2
];

rawTableColor[c_Integer, {xx_Integer, yy_Integer, zz_Integer}] :=
  turnTables[[c, zz + 1, 3 - yy, xx + 3]];

(* The complete (Turn) rule, in the paper's stated priority order.
   The incoming branch is tested before the outgoing branch.
   Table entries of color 0 are retained. *)
turnColor[c_Integer, {xx_Integer, yy_Integer, zz_Integer}] :=
  Module[{s = directions[[c,1]], t = directions[[c,2]]},
    Which[
      !MemberQ[{0,1}, zz], 0,
      s xx <= -2, incomingColor[s, yy, zz],
      t yy >= 2, outgoingColor[t, xx, zz],
      -2 <= xx <= 2 && -2 <= yy <= 2,
        rawTableColor[c, {xx,yy,zz}],
      True, 0
    ]
  ];

tetrahedronOffsets[perm_List] :=
  FoldList[Plus, {0,0,0}, IdentityMatrix[3][[perm]]];

tetrahedronColors[c_Integer, corner_List, perm_List] :=
  turnColor[c, #] & /@
    ((corner + #) & /@ tetrahedronOffsets[perm]);

cubeColors[c_Integer, corner_List] :=
  turnColor[c, #] & /@ ((corner + #) & /@ cubeOffsets);

(* A genuine universally quantified exact-arithmetic claim:
   every convex combination of these four vertex field values is nonzero.
   Closed simplices are checked, so all faces are included. *)
affineZeroFreeProof[colors_List] :=
  Module[{l0, l1, l2, l3, weights, field, formula},
    weights = {l0,l1,l2,l3};
    field = weights . palette[[colors + 1]];
    formula = Implies[
      (And @@ (# >= 0 & /@ weights)) && Total[weights] == 1,
      Or @@ (# != 0 & /@ field)
    ];
    (* Construct the quantifier after its arguments have been evaluated. *)
    Resolve[Apply[ForAll, {weights, formula}], Reals]
  ];

(* Control statement: the complete palette vanishes precisely at
   the equal weights 1/4, an exact rational number. *)
paletteBarycenterProof[] :=
  Module[{l0, l1, l2, l3, weights, field, formula},
    weights = {l0,l1,l2,l3};
    field = weights . palette;
    formula = Implies[
      (And @@ (# >= 0 & /@ weights)) && Total[weights] == 1,
      Equivalent[
        And @@ (# == 0 & /@ field),
        And @@ (# == 1/4 & /@ weights)
      ]
    ];
    Resolve[Apply[ForAll, {weights, formula}], Reals]
  ];

(* Pure Boolean formulas for the OPTIONAL all-integer-cubes check.
   They use only linear equations/inequalities with integer coefficients.
   Numeric turnColor above is an independent direct implementation. *)
incomingPositive[s_Integer, {xx_,yy_,zz_}, k_Integer] := Switch[k,
  1, yy == 1 && zz == 1 - beta[s],
  2, yy == 0 && zz == 1 - beta[s],
  3, (yy == 0 || yy == 1) && zz == beta[s]
];

outgoingPositive[t_Integer, {xx_,yy_,zz_}, k_Integer] := Switch[k,
  1, xx == 0 && zz == 1 - beta[t],
  2, xx == 1 && zz == 1 - beta[t],
  3, (xx == 0 || xx == 1) && zz == beta[t]
];

positiveTableVertices[c_Integer, k_Integer] :=
  positiveTableVertices[c,k] =
    Select[tableVertices, rawTableColor[c,#] == k &];

tablePositive[c_Integer, {xx_,yy_,zz_}, k_Integer] :=
  Or @@ ((xx == #[[1]] && yy == #[[2]] && zz == #[[3]]) & /@
    positiveTableVertices[c,k]);

turnPositive[c_Integer, p : {xx_,yy_,zz_}, k_Integer] :=
  Module[{s = directions[[c,1]], t = directions[[c,2]]},
    (s xx <= -2 && incomingPositive[s,p,k]) ||
    (s xx > -2 && t yy >= 2 && outgoingPositive[t,p,k]) ||
    (s xx > -2 && t yy < 2 && tablePositive[c,p,k])
  ];

turnPredicate[c_Integer, p_List, k_Integer] :=
  If[k == 0,
    Not[Or @@ Table[turnPositive[c,p,j], {j,1,3}]],
    turnPositive[c,p,k]
  ];

allIntegerCubesProof[c_Integer, perm_List] :=
  Module[{xx, yy, zz, vertices, fullyColored, formula},
    vertices = ({xx,yy,zz} + #) & /@ tetrahedronOffsets[perm];
    fullyColored = And @@ Table[
      Or @@ (turnPredicate[c,#,k] & /@ vertices), {k,0,3}];
    formula = Not[fullyColored];
    Resolve[Apply[ForAll, {{xx,yy,zz}, formula}], Integers]
  ];

VerifyTurnTables[] := Catch[
  Module[{records, exceptional, colorPatterns, affineResults,
          table3Claims = 0, boundaryClaims = 0, tableEntryClaims = 0,
          predicateClaims = 0, c, v, s, t, value, row, p, colors,
          result, vertices, gridVertices},

    require[Dimensions[turnTables] === {4,2,5,5}, "Table dimensions"];
    require[And @@ (MemberQ[Range[0,3],#] & /@ Flatten[turnTables]),
      "Every table entry is an exact color integer"];
    require[Sort[permutationList] === Sort[Permutations[{1,2,3}]],
      "All six distinct coordinate permutations"];

    (* Exact nondegeneracy of the six physical tetrahedron shapes.
       Translation does not change their determinants. *)
    Do[
      vertices = tetrahedronOffsets[p]/128;
      require[
        Abs[Det[Rest[vertices] - ConstantArray[First[vertices],3]]]
          == 1/128^3,
        "Kuhn tetrahedron determinant", p],
      {p,permutationList}];

    (* Check all 200 entries against the full rule and every relevant
       incoming, outgoing, and remaining outer-boundary condition. *)
    Do[
      s = directions[[c,1]]; t = directions[[c,2]];
      Do[
        value = rawTableColor[c,v];
        require[value == turnColor[c,v], "Full rule matches table",
          {caseNames[[c]],v}];
        tableEntryClaims++;
        If[s v[[1]] == -2,
          require[value == incomingColor[s,v[[2]],v[[3]]],
            "Incoming boundary", {caseNames[[c]],v}];
          boundaryClaims++];
        If[t v[[2]] == 2,
          require[value == outgoingColor[t,v[[1]],v[[3]]],
            "Outgoing boundary", {caseNames[[c]],v}];
          boundaryClaims++];
        If[(Abs[v[[1]]] == 2 || Abs[v[[2]]] == 2) &&
             s v[[1]] != -2 && t v[[2]] != 2,
          require[value == 0, "Remaining table boundary is zero",
            {caseNames[[c]],v}];
          boundaryClaims++],
        {v,tableVertices}],
      {c,1,4}];

    (* Each record: {turn number, cube corner, permutation number, colors}.
       Flatten only the two outer indexing levels. *)
    records = Flatten[
      Table[
        {c,v,p,tetrahedronColors[c,v,permutationList[[p]]]},
        {c,1,4}, {v,cubeCorners}, {p,1,6}], 2];
    require[4 Length[cubeCorners] == 432, "Cube count"];
    require[Length[records] == 2592, "Tetrahedron count"];
    Do[
      colors = row[[4]];
      require[Complement[Range[0,3],colors] =!= {},
        "No fully colored tetrahedron", row],
      {row,records}];

    (* Find every cube with all four colors among its eight vertices.
       Compare against Table 3, rather than checking only listed cubes. *)
    exceptional = Table[
      Select[cubeCorners,
        Sort[DeleteDuplicates[cubeColors[c,#]]] === Range[0,3] &],
      {c,1,4}];
    Do[
      require[Sort[exceptional[[c]]] === Sort[paperTable3[[c,All,1]]],
        "Table 3 exceptional list is complete", caseNames[[c]]];
      Do[
        Do[
          colors = tetrahedronColors[c,row[[1]],permutationList[[p]]];
          require[!MemberQ[colors,row[[2,p]]],
            "Table 3 claimed color is missing",
            {caseNames[[c]],row[[1]],permutationList[[p]],row[[2,p]],colors}];
          table3Claims++,
          {p,1,6}],
        {row,paperTable3[[c]]}],
      {c,1,4}];
    require[table3Claims == 102, "Number of Table 3 claims"];

    (* Compare the Boolean predicates used by the optional universal check
       against the direct coloring at every vertex in the finite region. *)
    gridVertices = Tuples[{Range[-3,3],Range[-3,3],Range[-1,2]}];
    Do[
      require[turnPredicate[c,v,p] === (turnColor[c,v] == p),
        "Boolean predicate matches direct coloring", {caseNames[[c]],v,p}];
      predicateClaims++,
      {c,1,4}, {v,gridVertices}, {p,0,3}];

    require[paletteBarycenterProof[], "Resolve: complete palette barycenter"];
    result = affineZeroFreeProof[{0,1,2,3}];
    require[result === False,
      "Control: a fully colored tetrahedron does have a zero", result];

    (* Reordering vertices only permutes barycentric variables. Thus one
       Resolve call per distinct sorted color list covers all 2592 cases.
       No color list is discarded on the basis of the earlier test. *)
    colorPatterns = DeleteDuplicates[Sort /@ records[[All,4]]];
    affineResults = Table[
      result = affineZeroFreeProof[colors];
      require[result, "Resolve: affine interpolant is zero-free", colors];
      <|"VertexColors" -> colors, "ResolveResult" -> result|>,
      {colors,colorPatterns}];

    <|
      "AllPassed" -> True,
      "CaseOrder" -> caseNames,
      "CubesChecked" -> 4 Length[cubeCorners],
      "TetrahedraChecked" -> Length[records],
      "TableEntriesChecked" -> tableEntryClaims,
      "BoundaryClaimsChecked" -> boundaryClaims,
      "ExceptionalCubesPerTurn" -> (Length /@ exceptional),
      "Table3MissingColorClaimsChecked" -> table3Claims,
      "PredicateAgreementClaimsChecked" -> predicateClaims,
      "AffineColorPatternsChecked" -> Length[colorPatterns],
      "AffineResolveResults" -> affineResults,
      "KernelVersion" -> $Version
    |>
  ], verificationTag
];

VerifyAllIntegerCubes[] := Catch[
  Module[{results, result, c, p},
    results = Flatten[
      Table[
        result = allIntegerCubesProof[c,permutationList[[p]]];
        require[result, "Resolve: every translated Kuhn tetrahedron omits a color",
          {caseNames[[c]],permutationList[[p]]}];
        <|"Turn" -> caseNames[[c]],
          "Permutation" -> permutationList[[p]],
          "ResolveResult" -> result|>,
        {c,1,4}, {p,1,6}], 1];
    <|"AllPassed" -> True, "UniversalClaimsChecked" -> Length[results],
      "Results" -> results, "KernelVersion" -> $Version|>
  ], verificationTag
];

End[];
EndPackage[];
