Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

requiredSymbols = {
  ConstructLeft3PointOpenBasis,
  ConstructRightProjectedJResidualRecords,
  ConstructGeneralSewingAmplitudeRecords,
  ConstructIndepSewingBlock,
  CompareGeneralSewingToCFBlocks,
  SewingSymbolToAmpForm,
  SewingRecordSymbolForm,
  SewingRecordAmpForm,
  SewingContractionTerms,
  SymmetricSewContract,
  SewingSortRecordsForBasis,
  SewingRelativeChiralOrder,
  SewingSortRecordsByChiralOrder,
  SewingLog,
  ConstructIndepCFBlock,
  ConstructAmp,
  ReduceSt,
  ExportAmp2Tex
};

missingDefinitions = Select[
  requiredSymbols,
  Length[DownValues[#]] == 0 && Length[SubValues[#]] == 0 &
];

missingUsage = Select[
  requiredSymbols,
  ! StringQ[MessageName[#, "usage"]] &
];

missingOptions = Complement[
  {SewingDebug, RightMass, LeftMass, QReplacement, PointCount, SewingContractionMode},
  Options[ConstructGeneralSewingAmplitudeRecords][[All, 1]]
];

If[missingDefinitions =!= {},
  Print["Missing definitions: ", missingDefinitions];
  Exit[1]
];

If[missingUsage =!= {},
  Print["Missing usage strings: ", missingUsage];
  Exit[1]
];

If[missingOptions =!= {},
  Print["Missing ConstructGeneralSewingAmplitudeRecords options: ", missingOptions];
  Exit[1]
];

If[$SewingDebug =!= False,
  Print["$SewingDebug should default to False."];
  Exit[1]
];

If[
  Expand[
    SewingSymbolToAmpForm[Xhard ab[Q, 4] sb[Q, 4], 4] -
      (sb[8, 7] - ab[1, 2]) (ab[1, 4] sb[1, 4] - ab[2, 4] sb[2, 4])
  ] =!= 0,
  Print["SewingSymbolToAmpForm should map Xhard and default Q to p1-p2."];
  Exit[1]
];

If[
  Expand[
    SewingSymbolToAmpForm[Xsoft ab[Q, 4] sb[Q, 4], 4, qSym] -
      (sb[8, 7] + ab[1, 2]) ab[qSym, 4] sb[qSym, 4]
  ] =!= 0,
  Print["SewingSymbolToAmpForm should keep symbolic QReplacement labels symbolic."];
  Exit[1]
];

If[SewingStaticXPower[<|"SortData" -> <|"J" -> 1, "Xhard" -> 2, "Xsoft" -> 0|>|>] =!= 2,
  Print["SewingStaticXPower should read Xhard for J>0 records."];
  Exit[1]
];

leftForContractionTest = First[ConstructLeft3PointOpenBasis[2, QReplacement -> 2]];
rightForContractionTest = First[
  ConstructRightProjectedJResidualRecords[
    <|"AngleJ" -> 1, "SquareJ" -> 3|>,
    {1, 1},
    {3},
    {1, 0},
    4
  ]
];
contractTerms = SewingContractionTerms[leftForContractionTest["AmpL"], rightForContractionTest["AmpR"]];
If[Length[contractTerms] <= 1 || Expand[Total[contractTerms] - SymmetricSewContract[leftForContractionTest["AmpL"], rightForContractionTest["AmpR"]]] =!= 0,
  Print["SewingContractionTerms should split the symmetric contraction and sum back to SymmetricSewContract."];
  Exit[1]
];

splitRecords = ConstructGeneralSewingAmplitudeRecords[
  1/2, {1, 1}, {3}, 4, {1, 0},
  JRange -> {2},
  QReplacement -> 2
];
sumRecords = ConstructGeneralSewingAmplitudeRecords[
  1/2, {1, 1}, {3}, 4, {1, 0},
  JRange -> {2},
  QReplacement -> 2,
  SewingContractionMode -> "Sum"
];
If[
  Length[splitRecords] <= Length[sumRecords] ||
    DeleteDuplicates[Lookup[splitRecords, "ContractionMode"]] =!= {"Split"} ||
    DeleteDuplicates[Lookup[sumRecords, "ContractionMode"]] =!= {"Sum"},
  Print["SewingContractionMode should default to Split and retain Sum as the one-record mode."];
  Exit[1]
];

Print["package smoke ok"];
