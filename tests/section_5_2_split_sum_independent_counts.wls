Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[fail, compareCase, blockCase, rankValue, expectedRanks, dims, results, failures];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

rankValue[assoc_Association, key_String] :=
  Lookup[Lookup[assoc, key, <||>], "Rank", Missing["NoRank"]];

compareCase[d_Integer, mode_String] := Module[{cmp},
  ClearCache[];
  cmp = CompareGeneralSewingToCFBlocks[
    1/2, {1, 1}, {3}, d, {1, 0},
    JMax -> 3,
    QReplacement -> 2,
    SewingContractionMode -> mode,
    SewingDebug -> False
  ];
  If[! AssociationQ[cmp],
    Return[<|"AmpDim" -> d, "Mode" -> mode, "Error" -> "NoAssociation", "Result" -> cmp|>]
  ];
  <|
    "AmpDim" -> d,
    "Mode" -> mode,
    "Records" -> If[ListQ[Lookup[cmp, "SewingRecords", $Failed]], Length[cmp["SewingRecords"]], Missing["NoSewingRecords"]],
    "CFRank" -> rankValue[cmp, "CFMatrix"],
    "SewingRank" -> rankValue[cmp, "SewingMatrix"],
    "JoinedRank" -> rankValue[cmp, "JoinedMatrix"],
    "CompleteQ" -> Lookup[cmp, "CompleteQ", Missing["NoCompleteQ"]]
  |>
];

blockCase[d_Integer, mode_String] := Module[{block, matrixRank},
  ClearCache[];
  block = ConstructIndepSewingBlock[
    1/2, {1, 1}, {3}, d, {1, 0},
    JMax -> 3,
    QReplacement -> 2,
    SewingContractionMode -> mode,
    CheckAgainstCF -> True,
    SewingDebug -> False
  ];
  If[! (ListQ[block] && Length[block] == 3),
    Return[<|"AmpDim" -> d, "Mode" -> mode, "Error" -> "BadBlock", "Result" -> block|>]
  ];
  matrixRank = MatrixRank[block[[2]]];
  <|
    "AmpDim" -> d,
    "Mode" -> mode,
    "BasisLength" -> Length[block[[1]]],
    "MatrixRank" -> matrixRank,
    "MonomialCount" -> Length[block[[3]]]
  |>
];

expectedRanks = <|3 -> 2, 4 -> 3, 5 -> 4, 6 -> 5|>;
dims = Keys[expectedRanks];

results = Association @ Table[
  d -> <|
    "SplitCompare" -> compareCase[d, "Split"],
    "SumCompare" -> compareCase[d, "Sum"],
    "SplitBlock" -> blockCase[d, "Split"],
    "SumBlock" -> blockCase[d, "Sum"]
  |>,
  {d, dims}
];

failures = Reap[
  Do[
    Module[
      {
        expected = expectedRanks[d],
        splitCompare = results[d, "SplitCompare"],
        sumCompare = results[d, "SumCompare"],
        splitBlock = results[d, "SplitBlock"],
        sumBlock = results[d, "SumBlock"]
      },
      If[! TrueQ[splitCompare["CompleteQ"]],
        Sow[<|"AmpDim" -> d, "Failure" -> "SplitIncomplete", "Data" -> splitCompare|>]
      ];
      If[! TrueQ[sumCompare["CompleteQ"]],
        Sow[<|"AmpDim" -> d, "Failure" -> "SumIncomplete", "Data" -> sumCompare|>]
      ];
      If[
        ! And[
          splitCompare["CFRank"] === expected,
          splitCompare["SewingRank"] === expected,
          splitCompare["JoinedRank"] === expected,
          sumCompare["CFRank"] === expected,
          sumCompare["SewingRank"] === expected,
          sumCompare["JoinedRank"] === expected
        ],
        Sow[
          <|
            "AmpDim" -> d,
            "Failure" -> "CompareRanksChanged",
            "ExpectedRank" -> expected,
            "Split" -> splitCompare,
            "Sum" -> sumCompare
          |>
        ]
      ];
      If[
        ! And[
          splitBlock["BasisLength"] === expected,
          splitBlock["MatrixRank"] === expected,
          sumBlock["BasisLength"] === expected,
          sumBlock["MatrixRank"] === expected
        ],
        Sow[
          <|
            "AmpDim" -> d,
            "Failure" -> "IndependentBlockCountChanged",
            "ExpectedRank" -> expected,
            "Split" -> splitBlock,
            "Sum" -> sumBlock
          |>
        ]
      ];
      If[splitCompare["Records"] < sumCompare["Records"],
        Sow[
          <|
            "AmpDim" -> d,
            "Failure" -> "SplitHasFewerRawRecords",
            "SplitRecords" -> splitCompare["Records"],
            "SumRecords" -> sumCompare["Records"]
          |>
        ]
      ];
    ],
    {d, dims}
  ]
][[2]];

Print["section 5.2 split/sum independent-count summaries: ", InputForm[results]];

If[failures === {},
  Print["section 5.2 split/sum independent-count preservation ok"],
  Print["section 5.2 split/sum independent-count preservation failed: ", InputForm[failures]];
  Exit[1]
];
