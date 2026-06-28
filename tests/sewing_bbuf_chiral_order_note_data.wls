If[!StringQ[$HBPTestCodeRoot],
  $HBPTestCodeRoot = If[
    DirectoryQ[FileNameJoin[{Directory[], "Codes", "MassiveAmplitude-Code"}]],
    FileNameJoin[{Directory[], "Codes", "MassiveAmplitude-Code"}],
    Directory[]
  ]
];
SetDirectory[$HBPTestCodeRoot];
Get[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]];

ClearAll[texAmp, emit, matrixRows, recordKind, nxValue, nuValue, printDim];

$SewingBBufChiralLines = {};
emit[args___] := Module[{s},
  s = StringJoin[ToString /@ {args}];
  AppendTo[$SewingBBufChiralLines, s];
  Print[s]
];

texAmp[expr_] := StringReplace[
  ExportAmp2Tex[expr],
  {"+ -" -> "- ", "+-" -> "-"}
];

matrixRows[m_] := StringRiffle[
  ("(" <> StringRiffle[ToString[#, InputForm] & /@ #, ","] <> ")") & /@ m,
  "; "
];

recordKind[rec_Association] := Module[{j = rec["J"], amp = rec["AmpL"]},
  Which[
    j > 0, "open",
    ! FreeQ[amp, -ab[1, 2] - sb[7, 8]], "x",
    ! FreeQ[amp, ab[1, 2] - sb[7, 8]], "y",
    True, "unknown"
  ]
];

nxValue[rec_Association] := If[recordKind[rec] === "x", 1, 0];
nuValue[rec_Association] := rec["AmpDim"] - nxValue[rec];

printDim[ampDim_Integer] := Module[
  {cmp, records, monoms, mat, rows},
  ClearCache[];
  cmp = CompareGeneralSewingToCFBlocks[
    1/2, {1, 1}, {3}, ampDim, {1, 0},
    JMax -> 3, QReplacement -> 2
  ];
  If[! AssociationQ[cmp] || ! TrueQ[cmp["CompleteQ"]],
    emit["CASE ampDim=", ampDim];
    emit["ERROR ", InputForm[cmp]];
    emit["ENDCASE"];
    Return[$Failed]
  ];
  records = cmp["SewingRecords"];
  monoms = cmp["Monomials"];
  mat = Table[
    Coefficient[Expand[rec["ReducedAmp"]], monom],
    {rec, records}, {monom, monoms}
  ];
  emit["CASE ampDim=", ampDim];
  emit["SUMMARY ", InputForm[<|
    "CFRank" -> cmp["CFMatrix"]["Rank"],
    "SewingRank" -> cmp["SewingMatrix"]["Rank"],
    "JoinedRank" -> cmp["JoinedMatrix"]["Rank"],
    "Records" -> Length[records]
  |>]];
  rows = Range[Length[records]];
  Do[
    emit[
      "R", i,
      " ; J: ", records[[i, "J"]],
      " ; Kind: ", recordKind[records[[i]]],
      " ; nx: ", nxValue[records[[i]]],
      " ; nuCandidate: ", nuValue[records[[i]]],
      " ; AmpL: ", texAmp[records[[i, "AmpL"]]],
      " ; AmpR: ", texAmp[records[[i, "AmpR"]]],
      " ; AmpSew: ", texAmp[records[[i, "TotalAmp"]]],
      " ; Reduced: ", texAmp[records[[i, "ReducedAmp"]]],
      " ; Coord: ", InputForm[mat[[i]]]
    ],
    {i, rows}
  ];
  emit["ENDCASE"];
];

Scan[printDim, {3, 4, 5, 6}];

Export[
  FileNameJoin[{$HBPTestCodeRoot, "logs", "sewing_bbuf_chiral_order_note_data.log"}],
  StringRiffle[$SewingBBufChiralLines, "\n"],
  "Text"
];
