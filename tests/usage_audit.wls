Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

publicSymbols = {
  Amp2WeylOp,
  Amp2MetaInfo,
  DisplayYT,
  ExportAmp2Tex,
  ConstructIndependentBasis,
  ConstructAmp,
  ConstructCFIByFakeDim,
  ConstructIndepCFBlock,
  GenerateNeedCFBlocks,
  ConstructLeft3PointOpenBasis,
  ConstructRightProjectedJResidualRecords,
  ConstructGeneralSewingAmplitudeRecords,
  ConstructIndepSewingBlock,
  CompareGeneralSewingToCFBlocks,
  SewingSortRecordsForBasis,
  SewingIndependentBlockFromRecords,
  SewingCoeffMatrixDataUnion,
  SewingDebug,
  SewingLog,
  RightMass,
  LeftMass,
  QReplacement,
  PointCount
};

missingUsage = Select[
  publicSymbols,
  ! StringQ[MessageName[#, "usage"]] &
];

If[missingUsage =!= {},
  Print["Missing usage strings: ", missingUsage];
  Exit[1]
];

messageSymbols = {
  ConstructRightAuxiliaryOnShellRecords::amp,
  ConstructGeneralSewingAmplitudeRecords::args,
  ConstructGeneralSewingAmplitudeRecords::ampdim,
  ConstructGeneralSewingAmplitudeRecords::check,
  ConstructIndepSewingBlock::cfcheck,
  ConstructIndepSewingBlock::indcheck,
  ConstructIndepSewingBlock::records,
  SewingSortRecordsForBasis::sortdata,
  ConstructCFIByFakeDim::BelowDim,
  ConstructCFIByFakeDim::MismatchDim
};

missingMessages = Select[messageSymbols, ! StringQ[#] &];

If[missingMessages =!= {},
  Print["Missing message strings: ", missingMessages];
  Exit[1]
];

Print["usage audit ok"];