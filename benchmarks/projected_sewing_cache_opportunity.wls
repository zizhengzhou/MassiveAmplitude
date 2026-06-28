Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[
  totalCount, fullMassFromCase, legacyCount, topStages, runProjected,
  uniqueCountBy, duplicateStats, traceStageEvents, traceKeyStats,
  collectGeneralRecords, summarizeRecords, runCase, aggregateOpportunity
];

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];
totalCount[_] := $Failed;

fullMassFromCase[leftSpin_, rightSpins_List, rightMass_List] := Join[
  {m1, m2},
  Table[
    If[MemberQ[rightMass, i], ToExpression["m" <> ToString[i]], 0],
    {i, 3, 2 + Length[rightSpins]}
  ]
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

uniqueCountBy[list_List, keyFunction_] := Length[DeleteDuplicates[keyFunction /@ list]];

duplicateStats[name_String, list_List, keyFunction_] := Module[
  {calls = Length[list], unique},
  unique = uniqueCountBy[list, keyFunction];
  <|
    "Name" -> name,
    "Calls" -> calls,
    "UniqueKeys" -> unique,
    "DuplicateCalls" -> Max[calls - unique, 0],
    "DuplicateFraction" -> If[calls == 0, 0., N[(calls - unique)/calls]]
  |>
];

traceStageEvents[trace_List, stage_String] := Select[trace, Lookup[#, "Stage", None] === stage &];

traceKeyStats[trace_List, stage_String, name_String, keyFunction_] := Module[
  {events = traceStageEvents[trace, stage]},
  duplicateStats[name, events, keyFunction]
];

collectGeneralRecords[case_Association, rightPolarization_List, timeoutSeconds_Integer] := Module[
  {timed},
  timed = TimeConstrained[
    AbsoluteTiming[
      Quiet@Check[
        Block[{Print = (Null &)},
          ConstructGeneralSewingAmplitudeRecords[
            case["LeftSpin"],
            case["RightSpins"],
            case["AmpDim"],
            rightPolarization,
            RightMass -> case["RightMass"],
            LeftMass -> {1, 2},
            FilterPhysicalSector -> False
          ]
        ],
        $Failed
      ]
    ],
    timeoutSeconds,
    $TimedOut
  ];
  Which[
    timed === $TimedOut, <|"RightPolarization" -> rightPolarization, "Status" -> "Timeout"|>,
    ListQ[timed[[2]]], <|"RightPolarization" -> rightPolarization, "Status" -> "OK", "Seconds" -> timed[[1]], "Records" -> timed[[2]]|>,
    True, <|"RightPolarization" -> rightPolarization, "Status" -> "Failed", "Seconds" -> timed[[1]], "Result" -> timed[[2]]|>
  ]
];

summarizeRecords[records_List] := Module[
  {recordCount = Length[records]},
  If[recordCount == 0,
    Return[
      <|
        "RecordCount" -> 0,
        "DuplicateStats" -> {}
      |>
    ]
  ];
  <|
    "RecordCount" -> recordCount,
    "DuplicateStats" -> {
      duplicateStats[
        "General.ReduceSewnAmp.TotalAmpKey",
        records,
        ToString[Lookup[#, "TotalAmp", Missing["NoTotalAmp"]], InputForm] &
      ],
      duplicateStats[
        "General.ReduceSewnAmp.RawAmpFormKey",
        records,
        ToString[Lookup[#, "SewingAmpFormRaw", Missing["NoRawAmp"]], InputForm] &
      ],
      duplicateStats[
        "General.ReducedAmp.ResultKey",
        records,
        ToString[Lookup[#, "ReducedAmp", Missing["NoReducedAmp"]], InputForm] &
      ],
      duplicateStats[
        "General.RightProjected.TargetEstimate",
        records,
        {
          Lookup[#, "RightPolarization", {}],
          Lookup[#, "RightAmpDim", Missing["NoRightAmpDim"]],
          Lookup[Lookup[#, "RightRecord", <||>], "ProjectedJCounts", Missing["NoJCounts"]]
        } &
      ],
      duplicateStats[
        "General.Left3Point.LeftRecordEstimate",
        records,
        {
          Lookup[#, "J", Missing["NoJ"]],
          Lookup[#, "LeftStructure", Missing["NoLeftStructure"]],
          Lookup[#, "QComponent", {}],
          Lookup[#, "OpenAmpL", Missing["NoOpenAmpL"]]
        } &
      ]
    }
  |>
];

runCase[case_Association] := Module[
  {
    timeoutSeconds, timed, result, basisCount, legacy, summary, trace,
    physicalBlocks, fullPolarizations, rightPolarizations, rightPolarizationCounts,
    generalTimeout, generalResults, generalRecords, opportunity
  },
  timeoutSeconds = Lookup[case, "TimeoutSeconds", 240];
  generalTimeout = Lookup[case, "GeneralTimeoutSeconds", timeoutSeconds];
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
  trace = result["PerformanceTrace"];
  legacy = legacyCount[case, timeoutSeconds];
  physicalBlocks = result["PhysicalBlocks"];
  fullPolarizations = physicalBlocks[[All, 2]];
  rightPolarizations = DeleteDuplicates[fullPolarizations[[All, 3 ;;]]];
  rightPolarizationCounts = Counts[fullPolarizations[[All, 3 ;;]]];
  generalResults = collectGeneralRecords[case, #, generalTimeout] & /@ rightPolarizations;
  generalRecords = Flatten[Lookup[Select[generalResults, #["Status"] === "OK" &], "Records", {}], 1];
  opportunity = <|
    "RightPolarizationCalls" -> Length[fullPolarizations],
    "RightPolarizationUnique" -> Length[rightPolarizations],
    "RightPolarizationDuplicateCalls" -> Length[fullPolarizations] - Length[rightPolarizations],
    "RightPolarizationCounts" -> rightPolarizationCounts,
    "TraceDuplicateStats" -> {
      traceKeyStats[
        trace,
        "General.Left3Point",
        "General.Left3Point.JAcrossProjectedCall",
        Lookup[Lookup[#, "Meta", <||>], "J", Missing["NoJ"]] &
      ],
      traceKeyStats[
        trace,
        "General.RightProjectedRecords",
        "General.RightProjectedRecords.JDimAcrossProjectedCall",
        {
          Lookup[Lookup[#, "Meta", <||>], "J", Missing["NoJ"]],
          Lookup[Lookup[#, "Meta", <||>], "RightAmpDim", Missing["NoRightAmpDim"]]
        } &
      ],
      traceKeyStats[
        trace,
        "Projected.ConstructIndepCFBlock",
        "Projected.ConstructIndepCFBlock.BlockKey",
        Lookup[Lookup[#, "Meta", <||>], "Block", Missing["NoBlock"]] &
      ]
    },
    "GeneralRecordStatusCounts" -> Counts[Lookup[generalResults, "Status", "Missing"]],
    "GeneralRecordSeconds" -> Total[Lookup[Select[generalResults, #["Status"] === "OK" &], "Seconds", 0.]],
    "GeneralRecordSummary" -> summarizeRecords[generalRecords]
  |>;
  Join[
    KeyDrop[case, {"GeneralTimeoutSeconds"}],
    <|
      "Status" -> "OK",
      "Seconds" -> timed[[1]],
      "BasisCount" -> basisCount,
      "LegacyCount" -> legacy,
      "CountMatchQ" -> (IntegerQ[legacy] && legacy == basisCount),
      "RelativeOrders" -> Keys[result["BasisByRelativeChiralOrder"]],
      "TopStages" -> topStages[summary],
      "Opportunity" -> opportunity
    |>
  ]
];

aggregateOpportunity[results_List] := Module[
  {okResults, duplicateRows, grouped},
  okResults = Select[results, AssociationQ[#] && #["Status"] === "OK" &];
  duplicateRows = Flatten[
    Join[
      Lookup[Lookup[#, "Opportunity", <||>], "TraceDuplicateStats", {}],
      Lookup[Lookup[Lookup[#, "Opportunity", <||>], "GeneralRecordSummary", <||>], "DuplicateStats", {}]
    ] & /@ okResults,
    1
  ];
  grouped = GroupBy[duplicateRows, #["Name"] &];
  ReverseSortBy[
    KeyValueMap[
      <|
        "Name" -> #1,
        "Cases" -> Length[#2],
        "Calls" -> Total[Lookup[#2, "Calls", 0]],
        "UniqueKeys" -> Total[Lookup[#2, "UniqueKeys", 0]],
        "DuplicateCalls" -> Total[Lookup[#2, "DuplicateCalls", 0]],
        "DuplicateFraction" -> If[
          Total[Lookup[#2, "Calls", 0]] == 0,
          0.,
          N[Total[Lookup[#2, "DuplicateCalls", 0]]/Total[Lookup[#2, "Calls", 0]]]
        ]
      |> &,
      grouped
    ],
    #["DuplicateCalls"] &
  ]
];

cases = {
  <|"Name" -> "4pt-vector-amp4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "TimeoutSeconds" -> 120|>,
  <|"Name" -> "4pt-vector-amp6-identical", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 240|>,
  <|"Name" -> "4pt-vector-amp7-identical-pressure", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 7, "Identical" -> {{3, 4}}, "TimeoutSeconds" -> 360|>,
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

results = runCase /@ cases;
aggregate = aggregateOpportunity[results];

Scan[Print["CACHE-OPPORTUNITY ", InputForm[#]] &, results];
Print["CACHE-OPPORTUNITY-AGGREGATE ", InputForm[aggregate]];

If[! DirectoryQ["logs"], CreateDirectory["logs"]];
Export[
  FileNameJoin[{"logs", "projected_sewing_cache_opportunity_latest.wl"}],
  <|"Results" -> results, "AggregateOpportunity" -> aggregate|>,
  "WL"
];

If[AnyTrue[results, #["Status"] === "OK" && TrueQ[#["CountMatchQ"]] &],
  Print["projected sewing cache opportunity survey completed"],
  Print["projected sewing cache opportunity survey had no legacy-matched successful case"];
  Exit[1]
];
