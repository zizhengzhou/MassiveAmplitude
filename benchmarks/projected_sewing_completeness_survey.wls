Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[
  totalCount, fullMassFromCase, legacyCount, projectedRun, cfRun,
  summarizeProjectedCase, summarizeCFCase, aggregateVerdict
];

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];
totalCount[_] := $Failed;

fullMassFromCase[rightSpins_List, rightMass_List] := Join[
  {m1, m2},
  Table[
    If[MemberQ[rightMass, i], ToExpression["m" <> ToString[i]], 0],
    {i, 3, 2 + Length[rightSpins]}
  ]
];

legacyCount[case_Association, timeoutSeconds_Integer] := Module[
  {spins, fullMass, codeDim, basis},
  spins = Join[{case["LeftSpin"], case["LeftSpin"]}, case["RightSpins"]];
  fullMass = fullMassFromCase[case["RightSpins"], case["RightMass"]];
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

projectedRun[case_Association, timeoutSeconds_Integer] := TimeConstrained[
  Quiet@Check[
    ConstructProjectedSewingRelativeChiralBasis[
      case["LeftSpin"],
      case["RightSpins"],
      case["RightMass"],
      case["AmpDim"],
      case["Identical"],
      ReturnProjectionData -> True
    ],
    $Failed
  ],
  timeoutSeconds,
  $TimedOut
];

cfRun[case_Association, polarization_List, timeoutSeconds_Integer] := TimeConstrained[
  Quiet@Check[
    CompareGeneralSewingToCFBlocks[
      case["LeftSpin"],
      case["RightSpins"],
      case["RightMass"],
      case["AmpDim"],
      polarization
    ],
    $Failed
  ],
  timeoutSeconds,
  $TimedOut
];

summarizeProjectedCase[case_Association] := Module[
  {timeoutSeconds, result, count, legacy, sectorResults, completeSectors, jDiagnostics},
  timeoutSeconds = Lookup[case, "TimeoutSeconds", 240];
  result = projectedRun[case, timeoutSeconds];
  If[result === $TimedOut,
    Return[Join[case, <|"Status" -> "Timeout", "Layer" -> "Projected"|>]]
  ];
  If[! AssociationQ[result],
    Return[Join[case, <|"Status" -> "Failed", "Layer" -> "Projected", "Result" -> result|>]]
  ];
  count = totalCount[result["BasisByRelativeChiralOrder"]];
  legacy = legacyCount[case, timeoutSeconds];
  sectorResults = Lookup[result, "SectorResults", {}];
  completeSectors = Cases[sectorResults, assoc_Association /; TrueQ[Lookup[assoc, "CompleteQ", False]], Infinity];
  jDiagnostics = DeleteDuplicates[
    Lookup[
      Lookup[sectorResults, "TotalJBlockDiagnostics", {}],
      "PtotalBlockDiagonalByJ",
      Missing["NoIdentical"]
    ]
  ];
  Join[
    case,
    <|
      "Layer" -> "Projected",
      "Status" -> "OK",
      "BasisCount" -> count,
      "LegacyCount" -> legacy,
      "CountMatchQ" -> (IntegerQ[legacy] && count == legacy),
      "NonzeroQ" -> count > 0,
      "RelativeOrders" -> Keys[result["BasisByRelativeChiralOrder"]],
      "CompleteSectorCount" -> Length[completeSectors],
      "AllJBlockDiagonalQ" -> FreeQ[DeleteCases[jDiagnostics, Missing["NoIdentical"]], False]
    |>
  ]
];

summarizeCFCase[case_Association] := Module[
  {timeoutSeconds, polarization, result, cfRank, sewingRank, joinedRank},
  timeoutSeconds = Lookup[case, "TimeoutSeconds", 180];
  polarization = case["RightPolarization"];
  result = cfRun[case, polarization, timeoutSeconds];
  If[result === $TimedOut,
    Return[Join[case, <|"Status" -> "Timeout", "Layer" -> "CFBlock"|>]]
  ];
  If[! AssociationQ[result],
    Return[Join[case, <|"Status" -> "Failed", "Layer" -> "CFBlock", "Result" -> result|>]]
  ];
  cfRank = Lookup[Lookup[result, "CFMatrix", <||>], "Rank", Missing["NoRank"]];
  sewingRank = Lookup[Lookup[result, "SewingMatrix", <||>], "Rank", Missing["NoRank"]];
  joinedRank = Lookup[Lookup[result, "JoinedMatrix", <||>], "Rank", Missing["NoRank"]];
  Join[
    case,
    <|
      "Layer" -> "CFBlock",
      "Status" -> "OK",
      "CompleteQ" -> TrueQ[Lookup[result, "CompleteQ", False]],
      "NonzeroQ" -> (IntegerQ[cfRank] && cfRank > 0),
      "CFCount" -> Lookup[result, "CFCount", Missing["NoCount"]],
      "SewingCount" -> Lookup[result, "SewingCount", Missing["NoCount"]],
      "CFRank" -> cfRank,
      "SewingRank" -> sewingRank,
      "JoinedRank" -> joinedRank,
      "RankMatchQ" -> (cfRank === sewingRank && sewingRank === joinedRank)
    |>
  ]
];

aggregateVerdict[projectedResults_List, cfResults_List] := <|
  "ProjectedCases" -> Length[projectedResults],
  "ProjectedOK" -> Count[Lookup[projectedResults, "Status", "Missing"], "OK"],
  "ProjectedNonzero" -> Count[Lookup[projectedResults, "NonzeroQ", False], True],
  "ProjectedCountMismatch" -> Select[projectedResults, #["Status"] === "OK" && ! TrueQ[#["CountMatchQ"]] &][[All, "Name"]],
  "ProjectedJBlockFailures" -> Select[projectedResults, #["Status"] === "OK" && ! TrueQ[#["AllJBlockDiagonalQ"]] &][[All, "Name"]],
  "CFBlockCases" -> Length[cfResults],
  "CFBlockOK" -> Count[Lookup[cfResults, "Status", "Missing"], "OK"],
  "CFBlockNonzero" -> Count[Lookup[cfResults, "NonzeroQ", False], True],
  "CFBlockRankFailures" -> Select[cfResults, #["Status"] === "OK" && (! TrueQ[#["CompleteQ"]] || ! TrueQ[#["RankMatchQ"]]) &][[All, "Name"]]
|>;

projectedCases = {
  <|"Name" -> "4pt-vector-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "4pt-vector-amp6-identical", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "4pt-vector-amp7-identical-pressure", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 7, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 360|>,
  <|"Name" -> "5pt-scalar-amp3-rightmass", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 3, "Identical" -> {}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "5pt-scalar-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 180|>,
  <|"Name" -> "5pt-scalar-amp5-identical", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {{4, 5}}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "5pt-scalar-amp6-identical-pressure", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 6, "Identical" -> {{4, 5}}, "TimeoutSeconds" -> 360|>,
  <|"Name" -> "5pt-spin3half-vector-amp5", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "5pt-spin3half-vector-amp6-identical", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 360|>,
  <|"Name" -> "6pt-scalar-amp4-no-identical", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "6pt-scalar-amp4-two-pairs", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{3, 4}, {5, 6}}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "6pt-scalar-amp4-triple", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{4, 5, 6}}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "6pt-scalar-amp5-two-pairs-pressure", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {{3, 4}, {5, 6}}, "TimeoutSeconds" -> 420|>,
  <|"Name" -> "6pt-mixed-spin-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 360|>,
  <|"Name" -> "6pt-mixed-spin-amp5-pair", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {{4, 5}}, "TimeoutSeconds" -> 420|>
};

cfCases = {
  <|"Name" -> "cf-4pt-vector-amp4-pol00", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "RightPolarization" -> {0, 0}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "cf-4pt-vector-amp4-pol20", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "RightPolarization" -> {2, 0}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "cf-4pt-vector-amp6-pol00", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "RightPolarization" -> {0, 0}, "TimeoutSeconds" -> 180|>,
  <|"Name" -> "cf-5pt-scalar-amp3", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 3, "RightPolarization" -> {0, 0, 0}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "cf-5pt-scalar-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "RightPolarization" -> {0, 0, 0}, "TimeoutSeconds" -> 180|>,
  <|"Name" -> "cf-5pt-scalar-amp5", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "RightPolarization" -> {0, 0, 0}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "cf-5pt-spin3half-vector-amp5-pol10", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "RightPolarization" -> {1, 0}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "cf-5pt-spin3half-vector-amp6-pol00", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "RightPolarization" -> {0, 0}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "cf-6pt-scalar-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "RightPolarization" -> {0, 0, 0, 0}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "cf-6pt-mixed-spin-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "RightPolarization" -> {0, 0, 0, 0}, "TimeoutSeconds" -> 300|>,
  <|"Name" -> "cf-6pt-mixed-spin-amp5-pol2000", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "RightPolarization" -> {2, 0, 0, 0}, "TimeoutSeconds" -> 420|>
};

projectedResults = summarizeProjectedCase /@ projectedCases;
cfResults = summarizeCFCase /@ cfCases;
verdict = aggregateVerdict[projectedResults, cfResults];

Scan[Print["COMPLETENESS-PROJECTED ", InputForm[#]] &, projectedResults];
Scan[Print["COMPLETENESS-CFBLOCK ", InputForm[#]] &, cfResults];
Print["COMPLETENESS-VERDICT ", InputForm[verdict]];

If[! DirectoryQ["logs"], CreateDirectory["logs"]];
Export[
  FileNameJoin[{"logs", "projected_sewing_completeness_survey_latest.wl"}],
  <|"ProjectedResults" -> projectedResults, "CFBlockResults" -> cfResults, "Verdict" -> verdict|>,
  "WL"
];

If[
  verdict["ProjectedOK"] =!= verdict["ProjectedCases"] ||
    verdict["ProjectedNonzero"] == 0 ||
    verdict["ProjectedCountMismatch"] =!= {} ||
    verdict["ProjectedJBlockFailures"] =!= {} ||
    verdict["CFBlockOK"] =!= verdict["CFBlockCases"] ||
    verdict["CFBlockNonzero"] == 0 ||
    verdict["CFBlockRankFailures"] =!= {},
  Print["projected sewing completeness survey failed"];
  Exit[1]
];

Print["projected sewing completeness survey passed"];
