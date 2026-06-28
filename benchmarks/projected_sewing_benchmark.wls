Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[
  totalCount, fullMassFromCase, legacyCount, topStages, runProjected,
  runCase, printResult, caseEnabledQ
];

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];
totalCount[_] := $Failed;

fullMassFromCase[leftSpin_, rightSpins_List, rightMass_List] := Join[
  {m1, m2},
  Table[If[MemberQ[rightMass, i], ToExpression["m" <> ToString[i]], 0], {i, 3, 2 + Length[rightSpins]}]
];

legacyCount[case_Association, timeoutSeconds_Integer] := Module[
  {spins, fullMass, codeDim, basis},
  spins = Join[{case["LeftSpin"], case["LeftSpin"]}, case["RightSpins"]];
  fullMass = fullMassFromCase[case["LeftSpin"], case["RightSpins"], case["RightMass"]];
  codeDim = case["AmpDim"] + Length[spins];
  basis = TimeConstrained[
    Quiet@Check[
      Block[{Print = (Null &)},
        MassiveBasis`Private`ConstructGeneralBasis[
          spins,
          codeDim,
          case["Identical"],
          mass -> fullMass
        ]
      ],
      $Failed
    ],
    timeoutSeconds,
    $TimedOut
  ];
  Which[
    basis === $TimedOut, "Timeout",
    ListQ[basis], Length[basis],
    True, $Failed
  ]
];

topStages[summary_Association, n_Integer : 8] := TakeLargestBy[
  Normal[summary],
  Lookup[#[[2]], "TotalSeconds", 0.] &,
  UpTo[n]
];
topStages[_, _Integer : 8] := {};

runProjected[case_Association, timeoutSeconds_Integer] := TimeConstrained[
  AbsoluteTiming[
    ConstructProjectedSewingRelativeChiralBasis[
      case["LeftSpin"],
      case["RightSpins"],
      case["RightMass"],
      case["AmpDim"],
      case["Identical"],
      ReturnProjectionData -> True,
      SewingPerformanceTrace -> True
    ]
  ],
  timeoutSeconds,
  $TimedOut
];

runCase[case_Association] := Module[
  {timeoutSeconds, timed, result, basisCount, legacy, summary},
  timeoutSeconds = Lookup[case, "TimeoutSeconds", 120];
  timed = runProjected[case, timeoutSeconds];
  If[timed === $TimedOut,
    Return[Join[case, <|"Status" -> "Timeout", "TimeoutSeconds" -> timeoutSeconds|>]]
  ];
  result = timed[[2]];
  If[! AssociationQ[result],
    Return[Join[case, <|"Status" -> "Failed", "Seconds" -> timed[[1]], "Result" -> result|>]]
  ];
  basisCount = totalCount[result["BasisByRelativeChiralOrder"]];
  summary = result["PerformanceSummary"];
  legacy = legacyCount[case, timeoutSeconds];
  Join[
    case,
    <|
      "Status" -> "OK",
      "Seconds" -> timed[[1]],
      "BasisCount" -> basisCount,
      "LegacyCount" -> legacy,
      "CountMatchQ" -> (IntegerQ[legacy] && legacy == basisCount),
      "RelativeOrders" -> Keys[result["BasisByRelativeChiralOrder"]],
      "TraceStageCount" -> Length[summary],
      "TopStages" -> topStages[summary],
      "JBlockDiagnostics" -> DeleteDuplicates[
        Lookup[Lookup[result["SectorResults"], "TotalJBlockDiagnostics", {}], "PtotalBlockDiagonalByJ", Missing["NoIdentical"]]
      ]
    |>
  ]
];

printResult[result_Association] := Print["BENCH ", InputForm[result]];

mode = ToLowerCase @ Replace[Environment["SEWING_BENCHMARK_MODE"], $Failed | None | "" -> "full"];

cases = {
  <|"Name" -> "4pt-spin1-half-amp4", "Group" -> "4pt", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "4pt-spin1-half-amp5-identical", "Group" -> "4pt-high", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 5, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 180|>,
  <|"Name" -> "5pt-scalar-rightmass-amp3", "Group" -> "5pt", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 3, "Identical" -> {}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "5pt-scalar-rightmass-amp4-identical", "Group" -> "5pt-high", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{4, 5}}, "TimeoutSeconds" -> 180|>,
  <|"Name" -> "5pt-spin3-half-vector-amp5", "Group" -> "5pt-spin3half", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "6pt-scalar-amp3-two-groups", "Group" -> "6pt", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 3, "Identical" -> {{3, 4}, {5, 6}}, "TimeoutSeconds" -> 180|>,
  <|"Name" -> "6pt-scalar-amp4-three-identical", "Group" -> "6pt-high", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{4, 5, 6}}, "TimeoutSeconds" -> 240|>
};

caseEnabledQ[case_Association] := mode =!= "smoke" || MemberQ[
  {"4pt-spin1-half-amp4", "5pt-scalar-rightmass-amp3", "6pt-scalar-amp3-two-groups"},
  case["Name"]
];

results = runCase /@ Select[cases, caseEnabledQ];
Scan[printResult, results];

If[! DirectoryQ["logs"], CreateDirectory["logs"]];
Export[
  FileNameJoin[{"logs", "projected_sewing_benchmark_latest.wl"}],
  results,
  "WL"
];

If[AnyTrue[results, #["Status"] === "OK" && TrueQ[#["CountMatchQ"]] &],
  Print["projected sewing benchmark completed with at least one legacy-matched nonzero sample"],
  Print["projected sewing benchmark completed without a matched sample"];
  Exit[1]
];
