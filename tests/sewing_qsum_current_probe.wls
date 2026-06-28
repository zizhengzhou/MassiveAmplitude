If[!StringQ[$HBPTestCodeRoot],
  $HBPTestCodeRoot = If[
    DirectoryQ[FileNameJoin[{Directory[], "Codes", "MassiveAmplitude-Code"}]],
    FileNameJoin[{Directory[], "Codes", "MassiveAmplitude-Code"}],
    Directory[]
  ]
];
SetDirectory[$HBPTestCodeRoot];
Get[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]];
Get[FileNameJoin[{$HBPTestCodeRoot, "SoftHeavyFactorization.executable.m"}]];

ClearAll[probeCase, row];

probeCase[case_Association, q_] := Module[{cmp, opts},
  ClearCache[];
  opts = Lookup[case, "Options", {}] /. (QReplacement -> _) -> Sequence[];
  cmp = Quiet@Check[
    TimeConstrained[
      CompareGeneralSewingToCFBlocks[
        case["LeftSpin"],
        case["RightSpins"],
        case["RightMass"],
        case["AmpDim"],
        case["RightPolarization"],
        Sequence @@ Join[opts, {QReplacement -> q}]
      ],
      Lookup[case, "Timeout", 240],
      $TimedOut
    ],
    $Failed
  ];
  If[!AssociationQ[cmp],
    <|"Q" -> q, "Status" -> ToString[cmp, InputForm]|>,
    <|
      "Q" -> q,
      "Status" -> "Compared",
      "CFRecords" -> Length[cmp["CFRecords"]],
      "SewingRecords" -> Length[cmp["SewingRecords"]],
      "CFRank" -> cmp["CFMatrix"]["Rank"],
      "SewingRank" -> cmp["SewingMatrix"]["Rank"],
      "JoinedRank" -> cmp["JoinedMatrix"]["Rank"],
      "CompleteQ" -> cmp["CompleteQ"],
      "QValues" -> If[ListQ[cmp["SewingRecords"]], DeleteDuplicates[Lookup[cmp["SewingRecords"], "QReplacement"]], {}]
    |>
  ]
];

row[case_Association] := <|
  "ID" -> case["ID"],
  "Q2" -> probeCase[case, 2],
  "Qsum12" -> probeCase[case, {1, 2}]
|>;

cases = {
  <|"ID" -> "4pt-s11-m3-pol10-d4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "RightPolarization" -> {1, 0}, "Options" -> {JMax -> 2}, "Timeout" -> 180|>,
  <|"ID" -> "4pt-s10-m3-pol10-d4", "LeftSpin" -> 1/2, "RightSpins" -> {1, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "RightPolarization" -> {1, 0}, "Options" -> {JMax -> 2}, "Timeout" -> 180|>,
  <|"ID" -> "4pt-left1-s11-m3-pol10-d5", "LeftSpin" -> 1, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "RightPolarization" -> {1, 0}, "Options" -> {JMax -> 3}, "Timeout" -> 240|>,
  <|"ID" -> "5pt-s111-m3-pol100-d5", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "RightPolarization" -> {1, 0, 0}, "Options" -> {JMax -> 2}, "Timeout" -> 240|>,
  <|"ID" -> "6pt-vectors-R1111-M3-P1000-D5", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "RightPolarization" -> {1, 0, 0, 0}, "Options" -> {JMax -> 2}, "Timeout" -> 300|>,
  <|"ID" -> "4pt-left32-R11-M3-P10-D5", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 5, "RightPolarization" -> {1, 0}, "Options" -> {JMax -> 4}, "Timeout" -> 240|>,
  <|"ID" -> "5pt-left32-R111-M3-P100-D6", "LeftSpin" -> 3/2, "RightSpins" -> {1, 1, 1}, "RightMass" -> {3}, "AmpDim" -> 6, "RightPolarization" -> {1, 0, 0}, "Options" -> {JMax -> 5}, "Timeout" -> 360|>
};

results = row /@ cases;
Print["QSUM_PROBE_RESULTS"];
Print[InputForm[results]];
bad = Select[
  Flatten[Lookup[results, {"Q2", "Qsum12"}]],
  Lookup[#, "Status", ""] =!= "Compared" || !TrueQ[Lookup[#, "CompleteQ", False]] &
];
If[Length[bad] > 0,
  Print["QSUM_PROBE_BAD"];
  Print[InputForm[bad]];
  Exit[1]
];
Print["ALL_QSUM_PROBE_CASES_COMPLETE"];
