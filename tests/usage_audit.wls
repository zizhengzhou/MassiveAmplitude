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
  SewingSymbolToAmpForm,
  SewingRecordSymbolForm,
  SewingRecordAmpForm,
  SewingContractionTerms,
  SymmetricSewContract,
  SewingSortRecordsForBasis,
  SewingStaticXPower,
  SewingRelativeChiralOrder,
  SewingChiralSortKey,
  SewingSortRecordsByChiralOrder,
  SewingIndependentBlockFromRecords,
  SewingCoeffMatrixDataUnion,
  SewingDebug,
  SewingLog,
  RightMass,
  LeftMass,
  QReplacement,
  PointCount,
  SewingContractionMode
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
  ConstructGeneralSewingAmplitudeRecords::mode,
  ConstructIndepSewingBlock::cfcheck,
  ConstructIndepSewingBlock::indcheck,
  ConstructIndepSewingBlock::records,
  SewingSortRecordsForBasis::sortdata,
  SewingSortRecordsByChiralOrder::metadata,
  ConstructCFIByFakeDim::BelowDim,
  ConstructCFIByFakeDim::MismatchDim
};

missingMessages = Select[messageSymbols, ! StringQ[#] &];

If[missingMessages =!= {},
  Print["Missing message strings: ", missingMessages];
  Exit[1]
];

Print["usage audit ok"];
