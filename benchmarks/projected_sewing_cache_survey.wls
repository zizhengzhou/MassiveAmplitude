Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[
  totalCount, fullMassFromCase, legacyCount, topStages, runProjected,
  runCase, printResult, stageRows, aggregateStages
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

topStages[summary_Association, n_Integer : 10] := TakeLargestBy[
  Normal[summary],
  Lookup[#[[2]], "TotalSeconds", 0.] &,
  UpTo[n]
];
topStages[_, _Integer : 10] := {};

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
  timeoutSeconds = Lookup[case, "TimeoutSeconds", 180];
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
      "PerformanceSummary" -> summary,
      "RightRawCache" -> Lookup[summary, "Cache.GeneralRightAuxiliaryRawRecords", <||>],
      "RightPolarizationCache" -> Lookup[summary, "Cache.RightPolarizationRecords", <||>]
    |>
  ]
];

stageRows[result_Association] := Module[{summary = Lookup[result, "PerformanceSummary", <||>]},
  If[! AssociationQ[summary], Return[{}]];
  KeyValueMap[
    Join[
      <|"Case" -> result["Name"], "Stage" -> #1|>,
      #2
    ] &,
    summary
  ]
];

aggregateStages[results_List] := Module[{rows, grouped},
  rows = Flatten[stageRows /@ Select[results, AssociationQ[#] && #["Status"] === "OK" &], 1];
  grouped = GroupBy[rows, #["Stage"] &];
  ReverseSortBy[
    KeyValueMap[
      <|
        "Stage" -> #1,
        "Cases" -> Length[#2],
        "Calls" -> Total[Lookup[#2, "Calls", 0]],
        "TotalSeconds" -> Total[Lookup[#2, "TotalSeconds", 0.]],
        "MaxCaseSeconds" -> Max[Lookup[#2, "TotalSeconds", 0.]],
        "CacheHits" -> Total[Lookup[#2, "CacheHits", 0]],
        "CacheMisses" -> Total[Lookup[#2, "CacheMisses", 0]]
      |> &,
      grouped
    ],
    #["TotalSeconds"] &
  ]
];

cases = {
  <|"Name" -> "4pt-vector-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "4pt-vector-amp6-identical", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "5pt-scalar-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 180|>,
  <|"Name" -> "5pt-scalar-amp5-identical", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {{4, 5}}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "5pt-spin3half-vector-amp5", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "5pt-spin3half-vector-amp6-identical", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "6pt-scalar-amp4-no-identical", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "6pt-scalar-amp4-two-pairs", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{3, 4}, {5, 6}}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "6pt-scalar-amp4-triple", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{4, 5, 6}}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "6pt-mixed-spin-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "6pt-mixed-spin-amp5-pair", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {{4, 5}}, "TimeoutSeconds" -> 360|>
};

results = runCase /@ cases;
aggregate = aggregateStages[results];

Scan[Print["CACHE-SURVEY ", InputForm[#]] &, results];
Print["CACHE-SURVEY-AGGREGATE ", InputForm[aggregate]];

If[! DirectoryQ["logs"], CreateDirectory["logs"]];
Export[
  FileNameJoin[{"logs", "projected_sewing_cache_survey_latest.wl"}],
  <|"Results" -> results, "AggregateStages" -> aggregate|>,
  "WL"
];

If[AnyTrue[results, #["Status"] === "OK" && TrueQ[#["CountMatchQ"]] &],
  Print["projected sewing cache survey completed"],
  Print["projected sewing cache survey had no legacy-matched successful case"];
  Exit[1]
];
