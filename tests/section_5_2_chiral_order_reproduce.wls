Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[
  fail, texAmp, rowKind, rowMeta, rowCoordinates, selectCumulative,
  collectRecords, writeWitnessLog
];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

texAmp[expr_] := StringReplace[
  ExportAmp2Tex[expr],
  {"+ -" -> "- ", "+-" -> "-", "MassiveBasis`Private`J" -> "J"}
];

rowKind[rec_Association] := Module[{data = SewingSortData[rec], x = SewingStaticXPower[rec]},
  Which[
    data["J"] === 0 && x > 0, "x",
    data["J"] === 0, "y",
    True, "open"
  ]
];

rowMeta[rec_Association] := <|
  "AmpDim" -> rec["AmpDim"],
  "J" -> rec["J"],
  "Kind" -> rowKind[rec],
  "XPower" -> SewingStaticXPower[rec],
  "RelativeOrder" -> SewingRelativeChiralOrder[rec],
  "AmpL" -> texAmp[rec["AmpL"]],
  "AmpR" -> texAmp[rec["AmpR"]],
  "TotalAmp" -> texAmp[rec["TotalAmp"]],
  "ReducedAmp" -> texAmp[rec["ReducedAmp"]]
|>;

rowCoordinates[records_, monoms_] := Table[
  Coefficient[Expand[rec["ReducedAmp"]], monom],
  {rec, records}, {monom, monoms}
];

selectCumulative[records_List] := Module[
  {sorted, monoms, chosen = {}, matrix = {}, vector, rank},
  sorted = SewingSortRecordsByChiralOrder[records];
  If[sorted === $Failed, fail["relative chiral sorting failed"]];
  monoms = Poly2Singlet[Lookup[sorted, "ReducedAmp"]];
  rank[mat_] := If[mat === {}, 0, MatrixRank[mat]];
  Do[
    vector = rowCoordinates[{rec}, monoms][[1]];
    If[rank[Append[matrix, vector]] > rank[matrix],
      AppendTo[chosen, rec];
      AppendTo[matrix, vector]
    ],
    {rec, sorted}
  ];
  chosen
];

collectRecords[dims_List] := Flatten[Table[
  Module[{cmp},
    ClearCache[];
    cmp = CompareGeneralSewingToCFBlocks[
      1/2, {1, 1}, {3}, d, {1, 0},
      JMax -> 4,
      QReplacement -> 2,
      SewingDebug -> False
    ];
    If[! AssociationQ[cmp] || ! TrueQ[cmp["CompleteQ"]],
      fail["section 5.2 comparison failed", <|"AmpDim" -> d, "Result" -> cmp|>]
    ];
    cmp["SewingRecords"]
  ],
  {d, dims}
]];

writeWitnessLog[path_, byOrder_Association] := Module[{lines = {}},
  If[! DirectoryQ[DirectoryName[path]], CreateDirectory[DirectoryName[path]]];
  AppendTo[lines, "Section 5.2 relative chiral-order witness"];
  AppendTo[lines, "Rule: RelativeOrder = AmpDim - XPower - J"];
  KeyValueMap[
    Function[{ord, rows},
      AppendTo[lines, ""];
      AppendTo[lines, "RELATIVE_ORDER " <> ToString[ord] <> " COUNT " <> ToString[Length[rows]]];
      Do[
        AppendTo[lines, "ROW " <> ToString[i]];
        AppendTo[lines, "  AmpDim: " <> ToString[rows[[i, "AmpDim"]]]];
        AppendTo[lines, "  J: " <> ToString[rows[[i, "J"]]]];
        AppendTo[lines, "  Kind: " <> rows[[i, "Kind"]]];
        AppendTo[lines, "  XPower: " <> ToString[rows[[i, "XPower"]]]];
        AppendTo[lines, "  AmpL: " <> rows[[i, "AmpL"]]];
        AppendTo[lines, "  AmpR: " <> rows[[i, "AmpR"]]];
        AppendTo[lines, "  TotalAmp: " <> rows[[i, "TotalAmp"]]];
        AppendTo[lines, "  ReducedAmp: " <> rows[[i, "ReducedAmp"]]],
        {i, Length[rows]}
      ]
    ],
    KeySort[byOrder]
  ];
  Export[path, StringRiffle[lines, "\n"], "Text"]
];

records = collectRecords[{3, 4, 5, 6}];
badAmpDim4J1 = Select[records, #["AmpDim"] === 4 && #["J"] === 1 &];
If[badAmpDim4J1 =!= {},
  fail["ampDim=4,J=1 records should be absent", KeyTake[#, {"AmpDim", "J", "AmpL", "AmpR"}] & /@ badAmpDim4J1]
];
selected = selectCumulative[records];
rows = Select[rowMeta /@ selected, MemberQ[{2, 3, 4}, #RelativeOrder] &];
byOrder = GroupBy[rows, #RelativeOrder &];
summary = Association[KeyValueMap[#1 -> Length[#2] &, byOrder]];
keys = AssociationMap[
  (KeyTake[#, {"AmpDim", "J", "Kind", "XPower", "RelativeOrder"}] & /@ Lookup[byOrder, #, {}]) &,
  {2, 3, 4}
];

expectedSummary = <|2 -> 3, 3 -> 4, 4 -> 5|>;
expectedKeys = <|
  2 -> {
    <|"AmpDim" -> 3, "J" -> 1, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 2|>,
    <|"AmpDim" -> 3, "J" -> 1, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 2|>,
    <|"AmpDim" -> 4, "J" -> 2, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 2|>
  },
  3 -> {
    <|"AmpDim" -> 4, "J" -> 0, "Kind" -> "x", "XPower" -> 1, "RelativeOrder" -> 3|>,
    <|"AmpDim" -> 5, "J" -> 2, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 3|>,
    <|"AmpDim" -> 5, "J" -> 2, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 3|>,
    <|"AmpDim" -> 6, "J" -> 3, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 3|>
  },
  4 -> {
    <|"AmpDim" -> 4, "J" -> 0, "Kind" -> "y", "XPower" -> 0, "RelativeOrder" -> 4|>,
    <|"AmpDim" -> 5, "J" -> 1, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 4|>,
    <|"AmpDim" -> 5, "J" -> 1, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 4|>,
    <|"AmpDim" -> 6, "J" -> 2, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 4|>,
    <|"AmpDim" -> 6, "J" -> 2, "Kind" -> "open", "XPower" -> 0, "RelativeOrder" -> 4|>
  }
|>;

writeWitnessLog[FileNameJoin[{"logs", "section_5_2_relative_chiral_orders.log"}], byOrder];

Print["section 5.2 relative chiral-order summary: ", InputForm[summary]];
Print["section 5.2 relative chiral-order keys: ", InputForm[keys]];

If[summary =!= expectedSummary,
  fail["section 5.2 relative chiral-order summary mismatch", summary]
];
If[keys =!= expectedKeys,
  fail["section 5.2 relative chiral-order keys mismatch", keys]
];

Print["section 5.2 relative chiral-order reproduction ok"];
