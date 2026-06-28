Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[rankCase];

rankCase[d_Integer] := Module[{cmp},
  ClearCache[];
  cmp = CompareGeneralSewingToCFBlocks[
    1/2, {1, 1}, {3}, d, {1, 0},
    JMax -> 3,
    QReplacement -> 2,
    SewingDebug -> False
  ];
  If[!AssociationQ[cmp], Return[<|"AmpDim" -> d, "Error" -> "NoAssociation", "Result" -> cmp|>]];
  <|
    "AmpDim" -> d,
    "CodeDim" -> Lookup[cmp, "CodeDim", Missing["NoCodeDim"]],
    "CFRecords" -> If[ListQ[Lookup[cmp, "CFRecords", $Failed]], Length[cmp["CFRecords"]], Missing["NoCFRecords"]],
    "SewingRecords" -> If[ListQ[Lookup[cmp, "SewingRecords", $Failed]], Length[cmp["SewingRecords"]], cmp["SewingRecords"]],
    "CFRank" -> Lookup[Lookup[cmp, "CFMatrix", <||>], "Rank", Missing["NoCFRank"]],
    "SewingRank" -> Lookup[Lookup[cmp, "SewingMatrix", <||>], "Rank", Missing["NoSewingRank"]],
    "JoinedRank" -> Lookup[Lookup[cmp, "JoinedMatrix", <||>], "Rank", Missing["NoJoinedRank"]],
    "CompleteQ" -> Lookup[cmp, "CompleteQ", Missing["NoCompleteQ"]]
  |>
];

results = rankCase /@ {3, 4, 5, 6};
expectedRanks = <|3 -> 2, 4 -> 3, 5 -> 4, 6 -> 5|>;
failures = Select[
  results,
  !(TrueQ[#CompleteQ] && #CFRank === expectedRanks[#AmpDim] && #SewingRank === expectedRanks[#AmpDim] && #JoinedRank === expectedRanks[#AmpDim]) &
];

Print["section 5.2 summaries: ", InputForm[results]];
If[failures === {},
  Print["section 5.2 reproduction ok"],
  Print["section 5.2 reproduction failed: ", InputForm[failures]];
  Exit[1]
];
