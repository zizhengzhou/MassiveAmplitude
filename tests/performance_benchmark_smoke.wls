Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[fail, runCase, totalCount, legacyCount, fullMassFromCase];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];
fullMassFromCase[leftSpin_, rightSpins_List, rightMass_List] := Join[
  {m1, m2},
  Table[If[MemberQ[rightMass, i], ToExpression["m" <> ToString[i]], 0], {i, 3, 2 + Length[rightSpins]}]
];
legacyCount[leftSpin_, rightSpins_List, rightMass_List, ampDim_Integer, identical_List] := Module[
  {spins = Join[{leftSpin, leftSpin}, rightSpins], fullMass, codeDim, basis},
  fullMass = fullMassFromCase[leftSpin, rightSpins, rightMass];
  codeDim = ampDim + Length[spins];
  basis = Quiet@Check[
    Block[{Print = (Null &)}, MassiveBasis`Private`ConstructGeneralBasis[spins, codeDim, identical, mass -> fullMass]],
    $Failed
  ];
  If[ListQ[basis], Length[basis], $Failed]
];

runCase[case_Association] := Module[
  {timed, result, basis, summary, legacy},
  timed = AbsoluteTiming[
    result = ConstructProjectedSewingRelativeChiralBasis[
      case["LeftSpin"],
      case["RightSpins"],
      case["RightMass"],
      case["AmpDim"],
      case["Identical"],
      ReturnProjectionData -> True,
      SewingPerformanceTrace -> True
    ]
  ];
  If[! AssociationQ[result], Return[Join[case, <|"Status" -> "Failed", "Seconds" -> timed[[1]]|>]]];
  basis = result["BasisByRelativeChiralOrder"];
  summary = result["PerformanceSummary"];
  legacy = legacyCount[case["LeftSpin"], case["RightSpins"], case["RightMass"], case["AmpDim"], case["Identical"]];
  Join[
    case,
    <|
      "Status" -> "OK",
      "Seconds" -> timed[[1]],
      "BasisCount" -> totalCount[basis],
      "LegacyCount" -> legacy,
      "CountMatchQ" -> (legacy === totalCount[basis]),
      "RelativeOrders" -> Keys[basis],
      "TraceStageCount" -> Length[summary],
      "TopStages" -> TakeLargestBy[Normal[summary], #["TotalSeconds"] &, UpTo[5]]
    |>
  ]
];

cases = {
  <|"Name" -> "4pt-baseline", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}|>,
  <|"Name" -> "5pt-scalar", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}|>,
  <|"Name" -> "6pt-two-identical-groups", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 3, "Identical" -> {{3, 4}, {5, 6}}|>
};

results = runCase /@ cases;
Scan[Print["BENCH ", InputForm[#]] &, results];

If[! AllTrue[results, #["Status"] === "OK" &], fail["benchmark smoke has failed cases", results]];
If[! AllTrue[results, IntegerQ[#["LegacyCount"]] && #["LegacyCount"] == #["BasisCount"] &],
  fail["benchmark smoke count mismatch", results]
];
If[! AllTrue[results, #["TraceStageCount"] > 0 &],
  fail["benchmark smoke missing trace stages", results]
];

Print["performance benchmark smoke ok"];
