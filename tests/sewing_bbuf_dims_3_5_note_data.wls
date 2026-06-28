If[!StringQ[$HBPTestCodeRoot],
  $HBPTestCodeRoot = If[
    DirectoryQ[FileNameJoin[{Directory[], "Codes", "MassiveAmplitude-Code"}]],
    FileNameJoin[{Directory[], "Codes", "MassiveAmplitude-Code"}],
    Directory[]
  ]
];
SetDirectory[$HBPTestCodeRoot];
Get[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]];

ClearAll[texAmp, matrixRows, emit, independentRecordBlock, printCase];

$SewingBBufDims35Lines = {};
emit[args___] := Module[{s},
  s = StringJoin[ToString /@ {args}];
  AppendTo[$SewingBBufDims35Lines, s];
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

independentRecordBlock[records_List, basis_List] := Module[
  {block, amps, positions},
  block = SewingIndependentBlockFromRecords[records, basis];
  If[!ListQ[block] || Length[block] != 3, Return[$Failed]];
  amps = block[[1]];
  positions = Flatten[
    FirstPosition[records[[All, "TotalAmp"]], #, Missing["NotFound"]] & /@ amps
  ];
  If[MemberQ[positions, Missing["NotFound"]], Return[$Failed]];
  <|
    "Records" -> records[[positions]],
    "Positions" -> positions,
    "Matrix" -> block[[2]],
    "Monomials" -> block[[3]]
  |>
];

printCase[ampDim_Integer] := Module[
  {cmp, cfRows, sewRows, block, rows, sewMat, cfPos, cfMat, monoms},
  ClearCache[];
  cmp = CompareGeneralSewingToCFBlocks[
    1/2, {1, 1}, {3}, ampDim, {1, 0},
    JMax -> 3, QReplacement -> 2
  ];
  If[!AssociationQ[cmp] || !TrueQ[cmp["CompleteQ"]],
    emit["CASE ampDim=", ampDim];
    emit["ERROR comparison failed: ", InputForm[cmp]];
    emit["ENDCASE"];
    Return[$Failed]
  ];
  cfRows = cmp["CFRecords"];
  sewRows = cmp["SewingRecords"];
  block = independentRecordBlock[sewRows, cmp["Monomials"]];
  If[block === $Failed,
    emit["CASE ampDim=", ampDim];
    emit["ERROR SewingIndependentBlockFromRecords did not return recoverable records"];
    emit["ENDCASE"];
    Return[$Failed]
  ];
  rows = block["Records"];
  sewMat = block["Matrix"];
  monoms = block["Monomials"];
  cfPos = FindIndependentBasisPos[cmp["CFMatrix"]["Matrix"]];
  cfMat = cmp["CFMatrix"]["Matrix"][[cfPos]];

  emit["CASE ampDim=", ampDim];
  emit["SUMMARY ", InputForm[<|
    "CodeDim" -> cmp["CodeDim"],
    "CFRecords" -> Length[cfRows],
    "SewingRecords" -> Length[sewRows],
    "CFRank" -> cmp["CFMatrix"]["Rank"],
    "SewingRank" -> cmp["SewingMatrix"]["Rank"],
    "JoinedRank" -> cmp["JoinedMatrix"]["Rank"],
    "CompleteQ" -> cmp["CompleteQ"],
    "CFIndependentRows" -> cfPos,
    "SewingIndependentRows" -> block["Positions"],
    "QValues" -> DeleteDuplicates[Lookup[sewRows, "QReplacement"]],
    "IndependentSelector" -> "SewingIndependentBlockFromRecords"
  |>]];
  emit["MONOMIALS"];
  Do[emit["e", i, " = ", texAmp[monoms[[i]]]], {i, Length[monoms]}];
  emit["CF_MATRIX ", matrixRows[cfMat]];
  emit["INDEPENDENT_SEWING_ROWS"];
  Do[
    emit[
      "S", i,
      " ; RawIndex: ", block["Positions"][[i]],
      " ; J: ", rows[[i, "J"]],
      " ; Q: ", InputForm[rows[[i, "QReplacement"]]],
      " ; AmpL: ", texAmp[rows[[i, "AmpL"]]],
      " ; AmpR: ", texAmp[rows[[i, "AmpR"]]],
      " ; AmpSew: ", texAmp[rows[[i, "TotalAmp"]]],
      " ; Reduced: ", texAmp[rows[[i, "ReducedAmp"]]],
      " ; Coord: ", InputForm[sewMat[[i]]]
    ],
    {i, Length[rows]}
  ];
  emit["SEWING_MATRIX ", matrixRows[sewMat]];
  emit["ENDCASE"];
];

Scan[printCase, {3, 4, 5}];

Export[
  FileNameJoin[{$HBPTestCodeRoot, "logs", "sewing_bbuf_dims_3_5_note_data.log"}],
  StringRiffle[$SewingBBufDims35Lines, "\n"],
  "Text"
];
