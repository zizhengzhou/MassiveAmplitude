Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[
  fail, massCasesFor, rightIdentityRecordsQ, compareCase, projectedCase
];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

massCasesFor[rightCount_Integer] := Module[
  {labels = Range[3, 2 + rightCount], mixed},
  mixed = Select[labels, OddQ];
  DeleteDuplicates[{{}, labels, mixed}]
];

rightIdentityRecordsQ[records_List] := AllTrue[
  records,
  Function[
    record,
    Module[{rightRecord = Lookup[record, "RightRecord", <||>]},
      Lookup[rightRecord, "Method", Missing[]] === "ScalarIdentityRightResidual" &&
        Lookup[rightRecord, "AmpR", Missing[]] === 1 &&
        Lookup[rightRecord, "ProjectedAmpR", Missing[]] === 1 &&
        Lookup[rightRecord, "ProjectedJCounts", <||>] ===
          <|"AngleJ" -> 0, "SquareJ" -> 0, "TotalJ" -> 0|>
    ]
  ]
];

compareCase[leftSpin_, rightCount_Integer, rightMass_List] := Module[
  {rightSpins, rightPolarization, ampDim, expectedRank, timed, comparison, ranks},
  rightSpins = ConstantArray[0, rightCount];
  rightPolarization = ConstantArray[0, rightCount];
  ampDim = 2 leftSpin;
  expectedRank = 2 leftSpin + 1;
  timed = AbsoluteTiming @ TimeConstrained[
    Quiet @ Check[
      CompareGeneralSewingToCFBlocks[
        leftSpin,
        rightSpins,
        rightMass,
        ampDim,
        rightPolarization,
        JMax -> 0
      ],
      $Failed
    ],
    90,
    $Timeout
  ];
  comparison = timed[[2]];
  If[! AssociationQ[comparison],
    Return[
      <|
        "Kind" -> "Compare",
        "LeftSpin" -> leftSpin,
        "RightCount" -> rightCount,
        "RightMass" -> rightMass,
        "Status" -> comparison,
        "Seconds" -> timed[[1]]
      |>
    ]
  ];
  ranks = Lookup[#, "Rank", Missing[]] & /@
    {comparison["CFMatrix"], comparison["SewingMatrix"], comparison["JoinedMatrix"]};
  <|
    "Kind" -> "Compare",
    "LeftSpin" -> leftSpin,
    "RightCount" -> rightCount,
    "RightMass" -> rightMass,
    "AmpDim" -> ampDim,
    "ExpectedRank" -> expectedRank,
    "CompleteQ" -> TrueQ[comparison["CompleteQ"]],
    "Ranks" -> ranks,
    "RightIdentityRecordsQ" -> rightIdentityRecordsQ[comparison["SewingRecords"]],
    "CFRecords" -> Length[comparison["CFRecords"]],
    "SewingRecords" -> Length[comparison["SewingRecords"]],
    "Seconds" -> timed[[1]]
  |>
];

projectedCase[leftSpin_, rightCount_Integer, rightMass_List] := Module[
  {rightSpins, ampDim, expectedRank, timed, data, count},
  rightSpins = ConstantArray[0, rightCount];
  ampDim = 2 leftSpin;
  expectedRank = 2 leftSpin + 1;
  timed = AbsoluteTiming @ TimeConstrained[
    Quiet @ Check[
      ConstructProjectedSewingRelativeChiralBasis[
        leftSpin,
        rightSpins,
        rightMass,
        ampDim,
        {},
        su3ShapeList -> {},
        ReturnProjectionData -> True,
        JMax -> 0
      ],
      $Failed
    ],
    90,
    $Timeout
  ];
  data = timed[[2]];
  If[! AssociationQ[data],
    Return[
      <|
        "Kind" -> "Projected",
        "LeftSpin" -> leftSpin,
        "RightCount" -> rightCount,
        "RightMass" -> rightMass,
        "Status" -> data,
        "Seconds" -> timed[[1]]
      |>
    ]
  ];
  count = Total[Length /@ Values[data["BasisByRelativeChiralOrder"]]];
  <|
    "Kind" -> "Projected",
    "LeftSpin" -> leftSpin,
    "RightCount" -> rightCount,
    "RightMass" -> rightMass,
    "AmpDim" -> ampDim,
    "ExpectedRank" -> expectedRank,
    "BasisCount" -> count,
    "AllSectorCompleteQ" ->
      And @@ (TrueQ[Lookup[#, "CompleteQ", False]] & /@ data["SectorResults"]),
    "Seconds" -> timed[[1]]
  |>
];

compareCases = Flatten[
  Table[
    {leftSpin, rightCount, rightMass},
    {leftSpin, {1/2, 1, 3/2, 2, 5/2, 3}},
    {rightCount, Range[2, 5]},
    {rightMass, massCasesFor[rightCount]}
  ],
  2
];
compareResults = compareCase @@@ compareCases;
compareFailures = Select[
  compareResults,
  ! (
      TrueQ[#["CompleteQ"]] &&
        #["Ranks"] === ConstantArray[#["ExpectedRank"], 3] &&
        TrueQ[#["RightIdentityRecordsQ"]]
    ) &
];

projectedCases = Flatten[
  Table[
    {leftSpin, rightCount, rightMass},
    {leftSpin, {1/2, 1, 3/2, 2, 3}},
    {rightCount, {2, 3, 4}},
    {rightMass, massCasesFor[rightCount]}
  ],
  2
];
projectedResults = projectedCase @@@ projectedCases;
projectedFailures = Select[
  projectedResults,
  ! (
      TrueQ[#["AllSectorCompleteQ"]] &&
        #["BasisCount"] === #["ExpectedRank"]
    ) &
];

If[compareFailures =!= {},
  fail["scalar identity broad compare scan failed", compareFailures]
];

If[projectedFailures =!= {},
  fail["scalar identity broad projected scan failed", projectedFailures]
];

Print[
  "scalar identity broad regression ok: compare cases ",
  Length[compareResults],
  ", projected cases ",
  Length[projectedResults]
];
