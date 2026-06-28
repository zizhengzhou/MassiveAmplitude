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
  ConstructSewingRelativeChiralBasis,
  ProjectSewingAmplitudeRecords,
  ConstructProjectedSewingRelativeChiralBasis,
  SewingSymbolToAmpForm,
  SewingReplaceQInSymbolForm,
  SewingDisplayForm,
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
  SewingContractionMode,
  JRange,
  JMax,
  AutoJNoRightWindow,
  ReturnRecords,
  ReplaceQInFinalSymbolForm,
  SewingOutputForm,
  ReturnProjectionData,
  SewingPerformanceTrace,
  RightPolarizationFilter,
  Q,
  Xhard,
  Xsoft
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
  ConstructGeneralSewingAmplitudeRecords::mass,
  ConstructIndepSewingBlock::cfcheck,
  ConstructIndepSewingBlock::indcheck,
  ConstructIndepSewingBlock::records,
  ConstructIndepSewingBlock::mass,
  CompareGeneralSewingToCFBlocks::mass,
  ConstructSewingRelativeChiralBasis::cfcheck,
  ConstructSewingRelativeChiralBasis::sort,
  ConstructSewingRelativeChiralBasis::count,
  ProjectSewingAmplitudeRecords::basis,
  ProjectSewingAmplitudeRecords::empty,
  ConstructProjectedSewingRelativeChiralBasis::identical,
  ConstructProjectedSewingRelativeChiralBasis::cf,
  ConstructProjectedSewingRelativeChiralBasis::sewing,
  ConstructProjectedSewingRelativeChiralBasis::complete,
  ConstructProjectedSewingRelativeChiralBasis::su3,
  ConstructProjectedSewingRelativeChiralBasis::count,
  ConstructProjectedSewingRelativeChiralBasis::polfilter,
  SewingSymbolToAmpForm::badq,
  SewingReplaceQInSymbolForm::badq,
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

requiredUsageFragments = {
  ConstructProjectedSewingRelativeChiralBasis -> {
    "identicalParam",
    "su3ShapeList",
    "ReturnProjectionData",
    "BasisByRelativeChiralOrder",
    "SU3IndexDictionary",
    "DirectProduct",
    "FindIndependentBasisPos",
    "RightPolarizationFilter"
  },
  ProjectSewingAmplitudeRecords -> {
    "full polarization",
    "ConstructIndepCFBlock",
    "FindIndependentBasisPos",
    "LorentzYoungOperator",
    "J block diagnostics"
  },
  ReturnProjectionData -> {
    "BasisByRelativeChiralOrder",
    "SU3IndexDictionaries",
    "J block diagnostics"
  },
  SewingPerformanceTrace -> {
    "per-stage timing",
    "cache hit/miss",
    "ReturnProjectionData"
  },
  RightPolarizationFilter -> {
    "Association",
    "right-side particle labels",
    "All"
  },
  Q -> {
    "formal momentum label",
    "QReplacement"
  },
  Xhard -> {
    "formal symbolic factor",
    "hard/static"
  },
  Xsoft -> {
    "formal symbolic factor",
    "soft/recoil"
  }
};

missingUsageFragments = DeleteCases[
  Flatten[
    KeyValueMap[
      Function[{symbol, fragments},
        Select[fragments, ! StringContainsQ[MessageName[symbol, "usage"], #] &] /. 
          fragment_String :> {symbol, fragment}
      ],
      Association[requiredUsageFragments]
    ],
    1
  ],
  {}
];

If[missingUsageFragments =!= {},
  Print["Missing required usage fragments: ", missingUsageFragments];
  Exit[1]
];

Print["usage audit ok"];
