Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

requiredSymbols = {
  ConstructLeft3PointOpenBasis,
  ConstructRightProjectedJResidualRecords,
  ConstructGeneralSewingAmplitudeRecords,
  ConstructIndepSewingBlock,
  CompareGeneralSewingToCFBlocks,
  SewingSortRecordsForBasis,
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
  {SewingDebug, RightMass, LeftMass, QReplacement, PointCount},
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

Print["package smoke ok"];
