(* ::Package:: *)

LogPri["Sewing Loaded"];

ClearAll[
  SewingJFactorQ, SewingJCounts, SewingCountsMatchQ,
  SewingClosedPairMonomials, SewingOpenPairMonomials,
  SewingBalancedOpenPairQ,
  ConstructLeft3PointOpenBasis,
  SewingQLabelQ, SewingXSymbolQ, SewingContainsXSymbolQ, SewingDisplayForm,
  SewingQSingleFactor, SewingApplyLeftQReplacement, SewingSymbolToAmpForm, SewingReplaceQInSymbolForm,
  SewingRecordSymbolForm, SewingRecordAmpForm,
  SewingRightResidualRecordsDirect, SewingRightResidualRecordsAuxiliary,
  CompareRightResidualBackends, SewingAuxiliaryAmpToFormalJ, SewingAuxiliaryAmpToFormalJCandidates,
  ConstructRightAuxiliaryOnShellRecords, CompareRightAuxiliaryOnShellToDirectJ,
  SewingProjectAuxiliaryLabels, SewingNormalizeJTarget, ConstructRightProjectedJResidualRecords,
  SewingContractMonomialTerms, SewingContractionTerms, SymmetricSewContract,
  ConstructGeneralSewingAmplitudeRecords, ConstructIndepSewingBlock,
  CompareGeneralSewingToCFBlocks,
  SewingReducedMassless, SewingReducedMasslessGeneral,
  SewingMasslessRule, SewingLeftSquareRelabelRule,
  SewingLeftMassiveSquareRelabel, SewingLeftForPointCount, SewingGeneralEOMRules,
  SewingRightJCountsMatchQ, SewingBracketDegree, SewingAmpDimMatchQ,
  SewingLeftDegreeData, SewingCodeDimFromAmpDim, SewingDefaultJMax, SewingDefaultRightMass,
  SewingMassOptionData, SewingCoeffMatrixDataUnion, SewingValidMetaQ,
  SewingAmpMetaTerms, SewingPhysicalAmpTermQ, SewingRecordPolarizationMatchQ, SewingIndependentBlockFromRecords,
  SewingProjectReducedAmpToBasis,
  SewingMasslessSelfColumnFreeQ, SewingLeftRecordCheck, SewingRightRecordCheck, SewingSewnRecordCheck,
  SewingCheckFailureQ, SewingCheckFailureMessage,
  SewingProjectAuxiliaryLabels, SewingNormalizeJTarget,
  SewingSortData, SewingSortDataQ,
  SewingStaticXPower, SewingRelativeChiralOrder, SewingChiralSortKey, SewingSortRecordsByChiralOrder,
  SewingBasisSortKey, SewingSortRecordsForBasis,
  ConstructSewingRelativeChiralBasis
];

ConstructLeft3PointOpenBasis::usage =
  "ConstructLeft3PointOpenBasis[J, opts] returns association records for equal-spin massive-massive-current three-point structures with open J slots. The result records include symbolic left form `AmpLSymbolForm`, internal spinor form `AmpLAmpForm`, compatibility key `AmpL`, and explicit sorting metadata `SortData = <|\"J\", \"Xhard\", \"Xsoft\"|>`. Options include `MassiveSpin`, `PointCount`, and `QReplacement`.";
SewingSymbolToAmpForm::usage =
  "SewingSymbolToAmpForm[expr, np, qSpec] converts display-level `Xhard`, `Xsoft`, and `Q` factors into the spinor-helicity amp form used internally. The default qSpec is {1, -2}, i.e. Q = p1 - p2.";
SewingReplaceQInSymbolForm::usage =
  "SewingReplaceQInSymbolForm[expr, qSpec] replaces only formal `Q` bracket pairs in a symbolic/display expression, preserving `Xhard` and `Xsoft`. The default qSpec is {1, -2}.";
SewingRecordSymbolForm::usage =
  "SewingRecordSymbolForm[record] returns the preferred display form of a sewing record, using `SewingSymForm` when present and falling back to legacy amplitude keys.";
SewingRecordAmpForm::usage =
  "SewingRecordAmpForm[record] returns the internal spinor-helicity amp form of a sewing record, using `SewingAmpForm` when present and falling back to legacy amplitude keys.";
SewingDisplayForm::usage =
  "SewingDisplayForm[expr, np] converts internal left square placeholders to the massive square labels for an explicit np-point amplitude. The np argument is required.";
SewingRightResidualRecordsDirect::usage =
  "SewingRightResidualRecordsDirect[target, nCols] enumerates right-side residual SSYT records from explicit angular/square target counts.";
SewingRightResidualRecordsAuxiliary::usage =
  "SewingRightResidualRecordsAuxiliary[target, nCols] enumerates right-side residual SSYT records using two auxiliary massless labels and translates them back to J.";
CompareRightResidualBackends::usage =
  "CompareRightResidualBackends[target, nCols] compares direct and auxiliary residual SSYT backends.";
SewingAuxiliaryAmpToFormalJ::usage =
  "SewingAuxiliaryAmpToFormalJ[amp] filters and translates an auxiliary on-shell amplitude to the formal-J right-half amplitude.";
SewingAuxiliaryAmpToFormalJCandidates::usage =
  "SewingAuxiliaryAmpToFormalJCandidates[amp] returns all formal-J right-half amplitudes obtained by keeping each single auxiliary label as a supplemental left label or replacing it by J.";
SewingProjectAuxiliaryLabels::usage =
  "SewingProjectAuxiliaryLabels[amp, auxLabels, jLabel] replaces the two auxiliary labels in amp by the formal current label jLabel and removes self-contractions. The default is SewingProjectAuxiliaryLabels[amp, {1, 2}, J].";
SewingNormalizeJTarget::usage =
  "SewingNormalizeJTarget[target] returns an association with separate \"AngleJ\", \"SquareJ\", and \"TotalJ\" counts extracted from a target association containing \"Angle\" and \"Square\" count associations.";
ConstructRightAuxiliaryOnShellRecords::usage =
  "ConstructRightAuxiliaryOnShellRecords[rightSpins, nCols, opts] constructs right-half auxiliary on-shell amplitudes, translates the auxiliary labels to the formal J slot, and returns records with angle/square label counts.";
ConstructRightAuxiliaryOnShellRecords::amp =
  "Auxiliary amplitude construction failed for spins `1`, codeDim `2`, antispinor `3`, and mass `4`.";
ConstructRightProjectedJResidualRecords::usage =
  "ConstructRightProjectedJResidualRecords[leftJTarget, rightSpins, rightMass, rightPolarization, rightAmpDim, opts] constructs right residual records from auxiliary particles, projects them to the formal J slot, removes vanishing projections, and filters the survivors by separate J-angle and J-square counts.";
CompareRightAuxiliaryOnShellToDirectJ::usage =
  "CompareRightAuxiliaryOnShellToDirectJ[target, nCols] compares balanced auxiliary on-shell records against direct formal-J residual records.";
SewingContractMonomialTerms::usage =
  "SewingContractMonomialTerms[monomialL, monomialR] returns the individual fully symmetric J-slot contraction terms for one left/right monomial pair.";
SewingContractionTerms::usage =
  "SewingContractionTerms[ampL, ampR] returns the expanded list of individual fully symmetric J-slot contraction terms before summing them.";
SymmetricSewContract::usage =
  "SymmetricSewContract[ampL, ampR] contracts all J slots by summing over all fully symmetric contraction terms. Use SewingContractionTerms to keep the terms split.";
ConstructGeneralSewingAmplitudeRecords::usage =
  "ConstructGeneralSewingAmplitudeRecords[leftSpin, rightSpins, ampDim, rightPolarization, opts] constructs sewn amplitude records for an equal-spin left current and a physical right residual sector. Each record carries display-level `SewingSymForm`, internal `SewingAmpForm`, reduced `ReducedAmp`, left/right provenance, `SortData`, and `QReplacement`. The default `QReplacement -> {1,-2}` uses Q = p1 - p2. With automatic `JRange` and `JMax`, the constructor scans J until `AutoJNoRightWindow` consecutive J sectors have no right-side records, with a hard internal search cap.";
ConstructGeneralSewingAmplitudeRecords::ampdim =
  "Internal sewing dimension mismatch for J=`1`, left degree data `2`, right ampDim `3`. The sewn amplitude has bracket degrees `4`, but expected ampDim `5`.";
ConstructGeneralSewingAmplitudeRecords::args =
  "Invalid sewing input: full point count `1`, right spin count `2`, and right polarization length `3`.";
ConstructGeneralSewingAmplitudeRecords::check =
  "Sewing construction check failed: `1`.";
ConstructGeneralSewingAmplitudeRecords::mode =
  "Unsupported SewingContractionMode `1`. Use \"Split\" or \"Sum\".";
ConstructIndepSewingBlock::usage =
  "ConstructIndepSewingBlock[leftSpin, rightSpins, ampDim, rightPolarization, opts] returns `{basis, coefficientMatrix, reducedMonomialBasis}` for the independent sewn basis after fixed priority sorting by lower `J`, then higher `Xsoft`, then higher `Xhard`. With `CheckAgainstCF -> True`, the sewn span is validated against `ConstructIndepCFBlock`. With `ReturnRecords -> True`, it returns an association containing the selected records, amplitudes, matrix, monomials, and positions.";
ConstructIndepSewingBlock::cfcheck =
  "Sewing span is not complete against CF blocks. CF rank `1`, sewing rank `2`, joined rank `3`.";
ConstructIndepSewingBlock::indcheck =
  "Independent sewing block check failed: `1`.";
ConstructIndepSewingBlock::records =
  "Sewing record construction failed.";
SewingSortRecordsForBasis::sortdata =
  "Cannot sort sewing records because at least one record has missing or invalid SortData metadata.";
SewingSortRecordsByChiralOrder::metadata =
  "Cannot sort sewing records by chiral order because at least one record has missing or invalid AmpDim or SortData metadata.";
SewingSymbolToAmpForm::badq =
  "Unsupported Q replacement specification `1`. Use Automatic, a symbol, an integer label, or a signed integer list such as {1,-2}.";
SewingReplaceQInSymbolForm::badq =
  "Unsupported Q replacement specification `1`. Use Automatic, a symbol, an integer label, or a signed integer list such as {1,-2}.";
SewingSortData::usage =
  "SewingSortData[record] returns the explicit SortData association for a sewing record, falling back to record[\"LeftRecord\", \"SortData\"] when present.";
SewingSortDataQ::usage =
  "SewingSortDataQ[record] returns True when the sewing record carries valid integer SortData fields \"J\", \"Xsoft\", and \"Xhard\".";
SewingStaticXPower::usage =
  "SewingStaticXPower[record] returns the Xhard power recorded in the sewing record SortData metadata. This is the XPower used by SewingRelativeChiralOrder.";
SewingRelativeChiralOrder::usage =
  "SewingRelativeChiralOrder[record] returns the relative chiral-order sorting label dAmp - nStaticX - J read from explicit sewing metadata. It does not include any sector-dependent additive offset.";
SewingChiralSortKey::usage =
  "SewingChiralSortKey[record] returns a stable key for table-level chiral sorting: relative chiral-order label, amplitude dimension, J, static/recoil/open priority, and the existing basis sort key.";
SewingSortRecordsByChiralOrder::usage =
  "SewingSortRecordsByChiralOrder[records] sorts sewing records by SewingChiralSortKey and fails if required SortData or AmpDim metadata is missing.";
SewingBasisSortKey::usage =
  "SewingBasisSortKey[record] returns the fixed priority key used for independent sewing basis selection: lower J, then higher Xsoft, then higher Xhard.";
SewingSortRecordsForBasis::usage =
  "SewingSortRecordsForBasis[records] sorts sewing records using explicit SortData metadata and fails if any record has missing or invalid SortData.";
SewingIndependentBlockFromRecords::usage =
  "SewingIndependentBlockFromRecords[records, basis] reduces sorted sewn records to a rank-maximal independent block and returns {basisAmplitudes, coefficientMatrix, reducedMonomialBasis}. The basis amplitudes use `SewingOutputForm`, defaulting to `SymbolForm`. With ReturnRecords -> True it returns an association containing the selected records, positions, matrix, and monomial basis. If basis is Automatic, it is built from reduced monomials.";
SewingCoeffMatrixDataUnion::usage =
  "SewingCoeffMatrixDataUnion[records, basis] returns an association containing the coefficient matrix, rank, reduced amplitudes, and monomial basis for a list of sewing records.";
CompareGeneralSewingToCFBlocks::usage =
  "CompareGeneralSewingToCFBlocks[leftSpin, rightSpins, ampDim, rightPolarization, opts] compares the sewn records against matching `ConstructIndepCFBlock` results after massless reduction. It returns the sewn/CF records, common monomial basis, coefficient matrices, ranks, and the completeness verdict `CompleteQ`.";
ConstructSewingRelativeChiralBasis::usage =
  "ConstructSewingRelativeChiralBasis[leftSpin, rightSpins, ampDim, rightPolarization, opts] returns an association whose keys are relative chiral-order labels and whose values are independent symbolic sewing basis amplitudes. It first verifies CF/sewing span equivalence and a strict selected-count equality before returning. By default it replaces final Q factors using `QReplacement -> {1,-2}` while preserving `Xhard` and `Xsoft`; use `ReplaceQInFinalSymbolForm -> False` to keep Q visible. ConstructSewingRelativeChiralBasis[leftSpin, rightSpins, rightMass, ampDim, rightPolarization, opts] specifies the right-side mass option explicitly.";

SewingApplyLeftQReplacement::badq =
  "Unsupported QReplacement specification `1`. Use a symbol, an integer label, or a signed integer list such as {1,2} or {1,-2}.";
ConstructRightProjectedJResidualRecords::check =
  "Projected right residual construction failed the J-shape filter: `1`.";
CompareGeneralSewingToCFBlocks::cf =
  "CF comparison failed for spin sector `1`, codeDim `2`, polarization `3`, mass `4`.";
ConstructSewingRelativeChiralBasis::cfcheck =
  "Sewing span is not complete against CF blocks. CF rank `1`, sewing rank `2`, joined rank `3`.";
ConstructSewingRelativeChiralBasis::sort =
  "Could not sort sewing records by relative chiral order because required metadata is missing.";
ConstructSewingRelativeChiralBasis::count =
  "Relative chiral basis count check failed: `1`.";

SewingJFactorQ[head_][factor_] :=
  MatchQ[factor, _[_, _]] && Head[factor] === head && MemberQ[List @@ factor, J];

SewingJCounts[amp_] := Module[{termCounts},
  termCounts = DeleteDuplicates[
    Module[{factors, angleJ, squareJ},
      factors = Prod2List[#];
      angleJ = Select[factors, SewingJFactorQ[ab]];
      squareJ = Select[factors, SewingJFactorQ[sb]];
      <|
        "AngleJ" -> Length[angleJ],
        "SquareJ" -> Length[squareJ],
        "TotalJ" -> Length[angleJ] + Length[squareJ]
      |>
    ] & /@ Sum2List[Expand[amp]]
  ];
  If[Length[termCounts] == 1, First[termCounts], $Failed]
];

SewingCountsMatchQ[{angleCounts_, squareCounts_}, target_Association] :=
  Normal[angleCounts] === Normal[target["Angle"]] &&
    Normal[squareCounts] === Normal[target["Square"]];

SewingZeroCounts[labels_List] := AssociationThread[labels, ConstantArray[0, Length[labels]]];
SewingNormalizeTarget[target_Association] := Module[{labels, a, s},
  labels = Lookup[target, "Labels", {1, 2, J, 3, 4, 6}];
  a = SewingZeroCounts[labels];
  s = SewingZeroCounts[labels];
  KeyValueMap[(If[KeyExistsQ[a, #1], a[#1] = #2]) &, Lookup[target, "Angle", <||>]];
  KeyValueMap[(If[KeyExistsQ[s, #1], s[#1] = #2]) &, Lookup[target, "Square", <||>]];
  Join[target, <|"Labels" -> labels, "Angle" -> a, "Square" -> s|>]
];

SewingColumnOKForLabelsQ[col : {a_, b_}, labels_List] := Module[{labelOrder},
  labelOrder = AssociationThread[labels, Range[Length[labels]]];
  Lookup[labelOrder, a, 1000] < Lookup[labelOrder, b, 1000]
];

SewingSSYTForLabelsQ[yt_, labels_List] := Module[{rows = yt, nCols, labelOrder},
  nCols = Length[rows[[1]]];
  labelOrder = AssociationThread[labels, Range[Length[labels]]];
  And @@ Join[
    Flatten@Table[
      Lookup[labelOrder, rows[[r, c]], 1000] <= Lookup[labelOrder, rows[[r, c + 1]], 1000],
      {r, 2}, {c, nCols - 1}
    ],
    Table[
      Lookup[labelOrder, rows[[1, c]], 1000] < Lookup[labelOrder, rows[[2, c]], 1000],
      {c, nCols}
    ]
  ]
];

SewingTableauxForLabels[nCols_Integer?NonNegative, labels_List] := Module[{pairs, yts},
  pairs = Select[Tuples[labels, 2], SewingColumnOKForLabelsQ[#, labels] &];
  yts = ({#[[All, 1]], #[[All, 2]]} &) /@ Tuples[pairs, nCols];
  Select[yts, SewingSSYTForLabelsQ[#, labels] &]
];

SewingHodgeDualWithJ[col_List, physicalLabels_List, supplementLabels_List, jLabel_] := Module[{other},
  If[MemberQ[col, jLabel],
    other = DeleteCases[col, jLabel];
    Return[Join[{jLabel}, ComplementMultiSet[physicalLabels, other]]]
  ];
  ComplementMultiSet[Join[supplementLabels, physicalLabels], col]
];

SewingAngularColumnValidWithJQ[col_List, physicalLabels_List, supplementLabels_List, jLabel_] :=
  Length[SewingHodgeDualWithJ[col, physicalLabels, supplementLabels, jLabel]] == Length[col];

SewingYTtoAmpRWithJ[yt_, nt_Integer, physicalLabels_List, supplementLabels_List, jLabel_] := Module[
  {nCols, abPart, sbPart},
  nCols = Length[yt[[1]]];
  abPart = Table[
    ab @@ SewingHodgeDualWithJ[yt[[All, c]], physicalLabels, supplementLabels, jLabel],
    {c, nt}
  ];
  sbPart = Table[sb @@ yt[[All, c]], {c, nt + 1, nCols}];
  Times @@ Join[abPart, sbPart]
];

SewingActualCountsWithJ[yt_, nt_Integer, labels_List, physicalLabels_List, supplementLabels_List, jLabel_] := Module[
  {nCols, angleLabels, squareLabels},
  nCols = Length[yt[[1]]];
  angleLabels = Flatten@Table[
    SewingHodgeDualWithJ[yt[[All, c]], physicalLabels, supplementLabels, jLabel],
    {c, nt}
  ];
  squareLabels = Flatten@Table[yt[[All, c]], {c, nt + 1, nCols}];
  {
    AssociationThread[labels, Count[angleLabels, #] & /@ labels],
    AssociationThread[labels, Count[squareLabels, #] & /@ labels]
  }
];

SewingYTStringForRows[yt_, nt_Integer] := StringRiffle[
  Table[
    StringJoin[ToString /@ yt[[r, ;; nt]]] <> "|" <>
      StringJoin[ToString /@ yt[[r, nt + 1 ;;]]],
    {r, Length[yt]}
  ],
  ";"
];

Options[SewingRightResidualRecordsDirect] = {
  Labels -> Automatic,
  PhysicalLabels -> Automatic,
  SupplementLabels -> {1, 2},
  JLabel -> J,
  SplitColumns -> Automatic
};
SewingRightResidualRecordsDirect[targetIn_Association, nCols_Integer?NonNegative, OptionsPattern[]] := Module[
  {target, labels, physicalLabels, supplementLabels, jLabel, splitColumns, yts, records = {}, nt, counts, ampR},
  target = SewingNormalizeTarget[targetIn];
  labels = Replace[OptionValue[Labels], Automatic -> target["Labels"]];
  supplementLabels = OptionValue[SupplementLabels];
  jLabel = OptionValue[JLabel];
  physicalLabels = Replace[
    OptionValue[PhysicalLabels],
    Automatic -> Complement[labels, Join[supplementLabels, {jLabel, 6}]]
  ];
  splitColumns = Replace[OptionValue[SplitColumns], Automatic -> Range[0, nCols]];
  yts = SewingTableauxForLabels[nCols, labels];
  Do[
    If[
      ! And @@ Table[
        SewingAngularColumnValidWithJQ[yt[[All, c]], physicalLabels, supplementLabels, jLabel],
        {c, nt}
      ],
      Continue[]
    ];
    counts = SewingActualCountsWithJ[yt, nt, labels, physicalLabels, supplementLabels, jLabel];
    If[! SewingCountsMatchQ[counts, target], Continue[]];
    ampR = SewingYTtoAmpRWithJ[yt, nt, physicalLabels, supplementLabels, jLabel];
    AppendTo[records,
      <|
        "Method" -> "DirectJ",
        "YTData" -> yt,
        "SplitColumn" -> nt,
        "YT" -> SewingYTStringForRows[yt, nt],
        "AmpR" -> ampR,
        "AngleCounts" -> counts[[1]],
        "SquareCounts" -> counts[[2]]
      |>
    ],
    {yt, yts}, {nt, splitColumns}
  ];
  DeleteDuplicatesBy[records, {#["YT"], #["SplitColumn"], ToString[#["AmpR"], InputForm]} &]
];

SewingAuxiliaryAllowedQ[yt_, nt_Integer, auxLabels_List] := Module[
  {nCols, columnOK},
  nCols = Length[yt[[1]]];
  columnOK[col_, c_Integer] := Module[{nAux = Count[col, Alternatives @@ auxLabels]},
    Which[
      nAux == 0, True,
      nAux == 1, True,
      nAux == Length[auxLabels] && c <= nt, Sort[col] === Sort[auxLabels],
      True, False
    ]
  ];
  And @@ Flatten@Table[columnOK[yt[[All, c]], c], {c, nCols}]
];

SewingTranslateAuxiliaryYT[yt_, nt_Integer, auxLabels_List, supplementLabels_List, jLabel_] := Module[
  {translated = yt, nCols},
  nCols = Length[yt[[1]]];
  Do[
    If[c <= nt && Sort[yt[[All, c]]] === Sort[auxLabels],
      translated[[All, c]] = supplementLabels,
      translated[[All, c]] = translated[[All, c]] /. Thread[auxLabels -> jLabel]
    ],
    {c, nCols}
  ];
  translated
];

Options[SewingRightResidualRecordsAuxiliary] = {
  AuxiliaryLabels -> {1, 2},
  PhysicalLabels -> Automatic,
  SupplementLabels -> {1, 2},
  JLabel -> J,
  SplitColumns -> Automatic
};
SewingRightResidualRecordsAuxiliary[targetIn_Association, nCols_Integer?NonNegative, OptionsPattern[]] := Module[
  {
    target, auxLabels, physicalLabels, supplementLabels, jLabel, auxLabelsAll, splitColumns,
    yts, records = {}, nt, auxYT, jYT, directRecords, directIndex, directKey, directRecord
  },
  target = SewingNormalizeTarget[targetIn];
  auxLabels = OptionValue[AuxiliaryLabels];
  supplementLabels = OptionValue[SupplementLabels];
  jLabel = OptionValue[JLabel];
  physicalLabels = Replace[
    OptionValue[PhysicalLabels],
    Automatic -> Complement[target["Labels"], Join[supplementLabels, {jLabel}]]
  ];
  auxLabelsAll = Join[auxLabels, physicalLabels];
  splitColumns = Replace[OptionValue[SplitColumns], Automatic -> Range[0, nCols]];
  directRecords = SewingRightResidualRecordsDirect[
    target,
    nCols,
    Labels -> target["Labels"],
    PhysicalLabels -> Complement[target["Labels"], Join[supplementLabels, {jLabel, 6}]],
    SupplementLabels -> supplementLabels,
    JLabel -> jLabel,
    SplitColumns -> splitColumns
  ];
  directKey[rec_] := ToString[{rec["SplitColumn"], rec["YTData"]}, InputForm];
  directIndex = GroupBy[directRecords, directKey];
  yts = SewingTableauxForLabels[nCols, auxLabelsAll];
  Do[
    If[! SewingAuxiliaryAllowedQ[auxYT, nt, auxLabels], Continue[]];
    jYT = SewingTranslateAuxiliaryYT[auxYT, nt, auxLabels, supplementLabels, jLabel];
    directRecord = Lookup[directIndex, ToString[{nt, jYT}, InputForm], {}];
    records = Join[
      records,
      Join[
        #,
        <|
          "Method" -> "AuxiliaryMassless",
          "AuxiliaryYTData" -> auxYT,
          "AuxiliaryYT" -> SewingYTStringForRows[auxYT, nt],
          "TranslatedYTData" -> jYT
        |>
      ] & /@ directRecord
    ],
    {auxYT, yts}, {nt, splitColumns}
  ];
  DeleteDuplicatesBy[records, {#["YT"], #["SplitColumn"], ToString[#["AmpR"], InputForm], #["AuxiliaryYT"]} &]
];

Options[CompareRightResidualBackends] = Join[
  Options[SewingRightResidualRecordsDirect],
  Options[SewingRightResidualRecordsAuxiliary]
];
CompareRightResidualBackends[target_Association, nCols_Integer?NonNegative, opts : OptionsPattern[]] := Module[
  {direct, auxiliary, key, directKeys, auxKeys},
  direct = SewingRightResidualRecordsDirect[target, nCols, FilterRules[{opts}, Options[SewingRightResidualRecordsDirect]]];
  auxiliary = SewingRightResidualRecordsAuxiliary[target, nCols, FilterRules[{opts}, Options[SewingRightResidualRecordsAuxiliary]]];
  key[rec_] := {rec["YT"], rec["SplitColumn"], ToString[rec["AmpR"], InputForm]};
  directKeys = DeleteDuplicates[key /@ direct];
  auxKeys = DeleteDuplicates[key /@ auxiliary];
  <|
    "DirectRecords" -> direct,
    "AuxiliaryRecords" -> auxiliary,
    "DirectCount" -> Length[direct],
    "AuxiliaryCount" -> Length[auxiliary],
    "DirectKeyCount" -> Length[directKeys],
    "AuxiliaryKeyCount" -> Length[auxKeys],
    "OnlyDirect" -> Complement[directKeys, auxKeys],
    "OnlyAuxiliary" -> Complement[auxKeys, directKeys],
    "EquivalentQ" -> (Sort[directKeys] === Sort[auxKeys])
  |>
];

ClearAll[
  SewingAuxiliaryBracketQ, SewingAmpCounts, SewingAutomaticAuxiliarySpinRange,
  SewingAuxiliarySpinPairs, SewingConstructAmpRaw
];
SewingAuxiliaryBracketQ[f_, auxLabels_List] :=
  MatchQ[f, _ab | _sb] && ! DisjointQ[List @@ f, auxLabels];

SewingAmpCounts[amp_, labels_List] := Module[
  {factors, angleLabels, squareLabels},
  factors = Select[Prod2List[Expand[amp]], MatchQ[#, _ab | _sb] &];
  angleLabels = Flatten[List @@@ Select[factors, Head[#] === ab &]];
  squareLabels = Flatten[List @@@ Select[factors, Head[#] === sb &]];
  {
    AssociationThread[labels, Count[angleLabels, #] & /@ labels],
    AssociationThread[labels, Count[squareLabels, #] & /@ labels]
  }
];

SewingMasslessSelfColumnFreeQ[amp_, np_Integer?Positive] := Module[
  {pairs, conjugates},
  pairs = Sort /@ (List @@@ Cases[Prod2List[Expand[amp]], _ab | _sb]);
  conjugates = Sort /@ Table[{i, 2 np + 1 - i}, {i, np}];
  DisjointQ[pairs, conjugates]
];

SewingAutomaticAuxiliarySpinRange[nCols_Integer?NonNegative] :=
  Table[h/2, {h, -2 nCols, 2 nCols}];

SewingAuxiliarySpinPairs[
  rightSpins_List,
  codeDim_Integer,
  rightAntispinor_List,
  massesIn_,
  auxRange_List,
  equalAuxQ_
] := Module[{spinPairs, spins, antispinor, masses, np},
  spinPairs = If[equalAuxQ, ({#, #} & /@ auxRange), Tuples[auxRange, 2]];
  DeleteDuplicates@Select[
    spinPairs,
    (
      spins = Join[#, rightSpins];
      np = Length[spins];
      antispinor = Join[ConstantArray[0, Length[#]], rightAntispinor];
      masses = MassOption[massesIn, np];
      CheckAmpConstruction[spins, codeDim - np, antispinor, masses]
    ) &
  ]
];

SewingConstructAmpRaw[spins_List, codeDim_Integer, antispinorsIn_List, massesIn_] := Module[
  {np = Length[spins], antispinors, masses, para, yd, filling, amps},
  If[np < 4, Return[{}]];
  masses = MassOption[massesIn, np];
  antispinors = If[np > Length[antispinorsIn],
    Join[antispinorsIn, ConstantArray[0, np - Length[antispinorsIn]]],
    antispinorsIn[[1 ;; np]]
  ];
  If[! CheckAmpConstruction[spins, codeDim - np, antispinors, masses], Return[{}]];
  para = InnerConstructAmp[spins, antispinors, np, codeDim, masses];
  If[Length[Select[para, Negative[#] &]] != 0, Return[{}]];
  yd = Join[Table[0, 2, para[[1]] + para[[2]]], Table[0, np - 4, para[[1]]]];
  filling = Flatten[
    Join[
      Table[Table[i, para[[2 + i]]], {i, np}],
      Table[Table[np*2 + 1 - i, para[[-(np + 1 - i)]]], {i, np}]
    ]
  ] // Sort;
  amps = YTtoAmpmass[#, para[[1]], Range[np]] & /@ StrangeSSYT[yd, filling, para[[1]], Range[np + 1, 2*np, 1]];
  If[$BHOmitLowDim,
    amps = amps /. RuleOmitLowDim[np] // DeleteCases[0]
  ];
  amps
];

Options[SewingAuxiliaryAmpToFormalJ] = {
  AuxiliaryLabels -> {1, 2},
  JLabel -> J
};
Options[SewingAuxiliaryAmpToFormalJCandidates] = Options[SewingAuxiliaryAmpToFormalJ];
SewingAuxiliaryAmpToFormalJCandidates[amp_, OptionsPattern[]] := Module[
  {auxLabels, jLabel, translateTerm, terms},
  auxLabels = OptionValue[AuxiliaryLabels];
  jLabel = OptionValue[JLabel];
  translateTerm[term_] := Module[{choices, alternatives},
    choices = Replace[
      Prod2List[term],
      f : (_ab | _sb) :> Module[{args = List @@ f, auxInFactor, replaced},
        auxInFactor = Cases[args, Alternatives @@ auxLabels];
        Which[
          Length[auxInFactor] == 0,
            {f},
          Length[auxInFactor] >= 2,
            Return[{}],
          True,
            replaced = Head[f] @@ (args /. First[auxInFactor] -> jLabel);
            DeleteCases[DeleteDuplicates[{f, replaced}], 0]
        ]
      ],
      {1}
    ];
    alternatives = DeleteCases[Expand[Times @@ #] & /@ Tuples[choices], 0];
    alternatives
  ];
  terms = Flatten[translateTerm /@ Sum2List[Expand[amp]]];
  DeleteDuplicates[DeleteCases[terms, 0]]
];
SewingAuxiliaryAmpToFormalJ[amp_, opts : OptionsPattern[]] := Module[{candidates},
  candidates = Select[
    SewingAuxiliaryAmpToFormalJCandidates[amp, FilterRules[{opts}, Options[SewingAuxiliaryAmpToFormalJCandidates]]],
    FreeQ[#, Alternatives @@ OptionValue[AuxiliaryLabels]] &
  ];
  If[Length[candidates] == 0, $Failed, First[candidates]]
];

Options[ConstructRightAuxiliaryOnShellRecords] = Join[
  {
    AuxiliarySpinRange -> Automatic,
    EqualAuxiliarySpin -> True,
    RightAntispinor -> Automatic,
    Target -> Automatic,
    Labels -> Automatic,
    AuxiliaryLabels -> {1, 2},
    JLabel -> J,
    CodeDim -> Automatic,
    RejectMasslessSelfColumns -> True,
    SewingDebug -> False,
    mass -> {3}
  }
];
ConstructRightAuxiliaryOnShellRecords[rightSpins_List, nCols_Integer?NonNegative, opts : OptionsPattern[]] := Module[
  {
    auxRange, equalAuxQ, rightAntispinor, targetIn, target, labels, auxLabels, jLabel,
    codeDimOpt, masses, spinPairs, records, np, spins, antispinor,
    codeDim, amps, formalAmps, formalAmp, counts, recordLabels, debug
  },
  debug = TrueQ[OptionValue[SewingDebug]];
  auxRange = Replace[OptionValue[AuxiliarySpinRange], Automatic -> SewingAutomaticAuxiliarySpinRange[nCols]];
  equalAuxQ = OptionValue[EqualAuxiliarySpin];
  rightAntispinor = Replace[
    OptionValue[RightAntispinor],
    Automatic -> If[Length[rightSpins] == 0, {}, UnitVector[Length[rightSpins], 1]]
  ];
  targetIn = OptionValue[Target];
  target = If[AssociationQ[targetIn], SewingNormalizeTarget[targetIn], Automatic];
  labels = Replace[
    OptionValue[Labels],
    Automatic -> If[AssociationQ[target], target["Labels"], Automatic]
  ];
  auxLabels = OptionValue[AuxiliaryLabels];
  jLabel = OptionValue[JLabel];
  codeDimOpt = OptionValue[CodeDim];
  masses = OptionValue[mass];
  spinPairs = SewingAuxiliarySpinPairs[
    rightSpins,
    Replace[codeDimOpt, Automatic -> nCols + 2 + Length[rightSpins]],
    rightAntispinor,
    masses,
    auxRange,
    equalAuxQ
  ];
  SewingLog[
    debug,
    "RightAuxiliary.Start",
    <|"RightSpins" -> rightSpins, "nCols" -> nCols, "SpinPairs" -> spinPairs|>
  ];
  records = Flatten@Table[
    spins = Join[spinPair, rightSpins];
    np = Length[spins];
    antispinor = Join[ConstantArray[0, Length[spinPair]], rightAntispinor];
    codeDim = Replace[codeDimOpt, Automatic -> nCols + np];
    amps = Quiet@Check[
      SewingConstructAmpRaw[spins, codeDim, antispinor, masses],
      Message[ConstructRightAuxiliaryOnShellRecords::amp, spins, codeDim, antispinor, masses];
      {}
    ];
    If[! ListQ[amps], amps = {}];
    SewingLog[debug, "RightAuxiliary.Sector", <|"SpinPair" -> spinPair, "RawAmpCount" -> Length[amps]|>];
    Table[
      If[
        TrueQ[OptionValue[RejectMasslessSelfColumns]] &&
          ! SewingMasslessSelfColumnFreeQ[amp, np],
        Nothing,
        formalAmps = SewingAuxiliaryAmpToFormalJCandidates[
          amp,
          AuxiliaryLabels -> auxLabels,
          JLabel -> jLabel
        ];
        If[Length[formalAmps] == 0, Nothing,
          Table[
          recordLabels = Replace[labels, Automatic -> DeleteDuplicates@Flatten[List @@@ Cases[Prod2List[formalAmp], _ab | _sb]]];
          counts = SewingAmpCounts[formalAmp, recordLabels];
          If[AssociationQ[target] && ! SewingCountsMatchQ[counts, target], Nothing,
            <|
              "Method" -> "AuxiliaryOnShellAmp",
              "AuxiliarySpin" -> spinPair,
              "Spins" -> spins,
              "Antispinor" -> antispinor,
              "CodeDim" -> codeDim,
              "AuxiliaryAmp" -> amp,
              "AmpR" -> formalAmp,
              "AngleCounts" -> counts[[1]],
              "SquareCounts" -> counts[[2]]
            |>
          ],
          {formalAmp, formalAmps}]
        ]
      ],
      {amp, amps}
    ],
    {spinPair, spinPairs}
  ];
  records = DeleteDuplicatesBy[records, {#["AuxiliarySpin"], ToString[#["AmpR"], InputForm]} &];
  SewingLog[debug, "RightAuxiliary.Done", <|"RecordCount" -> Length[records]|>];
  records
];

SewingProjectAuxiliaryLabels[amp_, auxLabels_: {1, 2}, jLabel_: J] :=
  Expand[ReplaceBraNumber[Thread[auxLabels -> jLabel]][amp]] /. {
    ab[jLabel, jLabel] -> 0,
    sb[jLabel, jLabel] -> 0
  };

SewingNormalizeJTarget[target_Association] := <|
  "AngleJ" -> Lookup[target, "AngleJ", Lookup[Lookup[target, "Angle", <||>], J, 0]],
  "SquareJ" -> Lookup[target, "SquareJ", Lookup[Lookup[target, "Square", <||>], J, 0]]
|>;

Options[ConstructRightProjectedJResidualRecords] = Join[
  {
    ReturnRejected -> False,
    RejectZeroProjection -> True
  },
  Options[ConstructRightAuxiliaryOnShellRecords]
];
ConstructRightProjectedJResidualRecords[
  leftJTargetIn_Association,
  rightSpins_List,
  rightMass_,
  rightPolarization_List,
  rightAmpDim_Integer?NonNegative,
  opts : OptionsPattern[]
] := Module[
  {
    leftJTarget, auxLabels, jLabel, raw, projected, counts, keepQ, rejectedReason,
    accepted, rejected, decorate, debug
  },
  debug = TrueQ[OptionValue[SewingDebug]];
  leftJTarget = SewingNormalizeJTarget[leftJTargetIn];
  auxLabels = OptionValue[AuxiliaryLabels];
  jLabel = OptionValue[JLabel];
  raw = ConstructRightAuxiliaryOnShellRecords[
    rightSpins,
    rightAmpDim,
    Sequence @@ Join[
      FilterRules[{opts}, Options[ConstructRightAuxiliaryOnShellRecords]],
      {
        RightAntispinor -> rightPolarization,
        CodeDim -> Replace[OptionValue[CodeDim], Automatic -> SewingCodeDimFromAmpDim[rightAmpDim, 2 + Length[rightSpins]]],
        mass -> rightMass,
        Target -> Automatic,
        AuxiliaryLabels -> auxLabels,
        JLabel -> jLabel,
        EqualAuxiliarySpin -> OptionValue[EqualAuxiliarySpin],
        AuxiliarySpinRange -> OptionValue[AuxiliarySpinRange],
        RejectMasslessSelfColumns -> OptionValue[RejectMasslessSelfColumns]
      }
    ]
  ];
  If[raw === $Failed || ! ListQ[raw], Return[{}]];
  SewingLog[debug, "RightProjected.Raw", <|"RawCount" -> Length[raw], "Target" -> leftJTarget|>];
  decorate[rec_] := Module[{projectedAmp, jCounts},
    projectedAmp = rec["AmpR"];
    jCounts = SewingJCounts[projectedAmp];
    Join[
      rec,
      <|
        "RawAmpR" -> rec["AuxiliaryAmp"],
        "AmpR" -> projectedAmp,
        "ProjectedAmpR" -> projectedAmp,
        "ProjectedJCounts" -> jCounts,
        "LeftJTarget" -> leftJTarget
      |>
    ]
  ];
  raw = decorate /@ raw;
  rejectedReason[rec_] := Which[
    TrueQ[OptionValue[RejectZeroProjection]] && TrueQ[Expand[rec["ProjectedAmpR"]] === 0],
      "ZeroProjection",
    ! AssociationQ[rec["ProjectedJCounts"]],
      "NonUniformJCounts",
    rec["ProjectedJCounts"]["AngleJ"] =!= leftJTarget["AngleJ"] ||
      rec["ProjectedJCounts"]["SquareJ"] =!= leftJTarget["SquareJ"],
      "JCountMismatch",
    True,
      None
  ];
  accepted = Select[raw, rejectedReason[#] === None &];
  accepted = DeleteDuplicatesBy[
    accepted,
    {#["AuxiliarySpin"], ToString[#["ProjectedAmpR"], InputForm]} &
  ];
  SewingLog[debug, "RightProjected.Done", <|"Accepted" -> Length[accepted], "Rejected" -> Length[raw] - Length[accepted]|>];
  If[! TrueQ[OptionValue[ReturnRejected]],
    Return[accepted]
  ];
  rejected = Select[
    Append[#, "RejectReason" -> rejectedReason[#]] & /@ raw,
    #["RejectReason"] =!= None &
  ];
  <|"Accepted" -> accepted, "Rejected" -> rejected|>
];

Options[CompareRightAuxiliaryOnShellToDirectJ] = Join[
  {
    RightSpins -> {1, 1},
    RightAntispinor -> {1, 0}
  },
  Options[ConstructRightAuxiliaryOnShellRecords],
  Options[SewingRightResidualRecordsDirect]
];
CompareRightAuxiliaryOnShellToDirectJ[target_Association, nCols_Integer?NonNegative, opts : OptionsPattern[]] := Module[
  {rightSpins, rightAntispinor, direct, auxiliary, key, directKeys, auxKeys},
  rightSpins = OptionValue[RightSpins];
  rightAntispinor = OptionValue[RightAntispinor];
  direct = SewingRightResidualRecordsDirect[
    target,
    nCols,
    FilterRules[{opts}, Options[SewingRightResidualRecordsDirect]]
  ];
  auxiliary = ConstructRightAuxiliaryOnShellRecords[
    rightSpins,
    nCols,
    Sequence @@ Join[
      FilterRules[{opts}, Options[ConstructRightAuxiliaryOnShellRecords]],
      {RightAntispinor -> rightAntispinor, Target -> target}
    ]
  ];
  key[rec_] := ToString[Expand[rec["AmpR"]], InputForm];
  directKeys = DeleteDuplicates[key /@ direct];
  auxKeys = DeleteDuplicates[key /@ auxiliary];
  <|
    "DirectRecords" -> direct,
    "AuxiliaryRecords" -> auxiliary,
    "DirectKeyCount" -> Length[directKeys],
    "AuxiliaryKeyCount" -> Length[auxKeys],
    "OnlyDirect" -> Complement[directKeys, auxKeys],
    "OnlyAuxiliary" -> Complement[auxKeys, directKeys],
    "EquivalentQ" -> (Sort[directKeys] === Sort[auxKeys])
  |>
];

Options[ConstructLeft3PointOpenBasis] = {
  MassiveSpin -> 1/2,
  PointCount -> Automatic,
  QReplacement -> {1, -2}
};

(* Open question:
   The current constructor covers equal-spin l+l+J three-point structures.
   A future l1+l2+J version should separately enumerate open slots on leg 1
   and leg 2, require the remaining closed slots to pair consistently, and
   then add any excess current spin through Q-raising factors. *)
(* Physical convention:
   Q is the hard relative momentum of the heavy pair and should be read as
   P1 - P2 (equivalently p_-).  The soft sum P1 + P2 belongs to the right
   residual sector and must not be used as the Q-label in the left current.
   This choice preserves the hard/soft separation and keeps the chiral
   filtration aligned with the J-priority ordering. *)
SewingClosedPairMonomials[n_Integer?NonNegative, np_: Automatic] := Module[
  {sq1, sq2},
  {sq1, sq2} = If[IntegerQ[np], {2 np, 2 np - 1}, {8, 7}];
  Table[
  <|
    "ClosedPowers" -> <|"Xhard" -> n - k, "Xsoft" -> k|>,
    "Amp" -> (sb[sq1, sq2] - ab[1, 2])^(n - k) (sb[sq1, sq2] + ab[1, 2])^k,
    "SymbolicAmp" -> Xhard^(n - k) Xsoft^k
  |>,
  {k, 0, n}
  ]
];

SewingQLabelQ[x_] := MatchQ[x, _Symbol] && SymbolName[Unevaluated[x]] === "Q";
SewingXSymbolQ[x_] := MatchQ[x, _Symbol] && MemberQ[{"Xhard", "Xsoft"}, SymbolName[Unevaluated[x]]];
SewingContainsXSymbolQ[expr_] := ! FreeQ[expr, s_Symbol /; SewingXSymbolQ[s]];
SewingDisplayForm[expr_, np_Integer?Positive] := Module[{sq1, sq2},
  {sq1, sq2} = {2 np, 2 np - 1};
  expr /. {L1 -> sq1, L2 -> sq2}
];

SewingQSingleFactor[0] := 0;
SewingQSingleFactor[q_?Negative] := -SewingQSingleFactor[-q];
SewingQSingleFactor[q_] := ab[q, J] sb[q, J];

SewingQTerms[qSpec_] := Module[{qActual},
  qActual = Replace[qSpec, Automatic -> {1, -2}];
  Which[
    ListQ[qActual], qActual,
    IntegerQ[qActual] || MatchQ[qActual, _Symbol], {qActual},
    True, $Failed
  ]
];

SewingReplaceQInSymbolForm[expr_, qSpec_: {1, -2}] := Module[
  {qTerms, qFactorQ, replaceQ, qPairAmp, convertTerm, converted},
  qTerms = SewingQTerms[qSpec];
  If[qTerms === $Failed,
    Message[SewingReplaceQInSymbolForm::badq, qSpec];
    Return[$Failed]
  ];
  qFactorQ[f_] := MatchQ[f, _ab | _sb] && AnyTrue[List @@ f, SewingQLabelQ];
  replaceQ[f_ab, q_?Negative] := replaceQ[f, -q];
  replaceQ[f_sb, q_?Negative] := replaceQ[f, -q];
  replaceQ[ab[a_, b_], q_] := Which[
    SewingQLabelQ[a], ab[q, b],
    SewingQLabelQ[b], ab[a, q],
    True, ab[a, b]
  ];
  replaceQ[sb[a_, b_], q_] := Which[
    SewingQLabelQ[a], sb[q, b],
    SewingQLabelQ[b], sb[a, q],
    True, sb[a, b]
  ];
  qPairAmp[a_, s_] := Total[
    (If[IntegerQ[#] && Negative[#], -1, 1] replaceQ[a, #] replaceQ[s, #]) & /@ qTerms
  ];
  convertTerm[term_] := Module[{factors, qAngles, qSquares, baseFactors},
    factors = Prod2List[term];
    qAngles = Select[factors, qFactorQ[#] && Head[#] === ab &];
    qSquares = Select[factors, qFactorQ[#] && Head[#] === sb &];
    If[Length[qAngles] =!= Length[qSquares], Return[$Failed]];
    baseFactors = Select[factors, ! qFactorQ[#] &];
    Expand[(Times @@ baseFactors) Times @@ MapThread[qPairAmp, {qAngles, qSquares}]]
  ];
  converted = convertTerm /@ Sum2List[Expand[expr]];
  If[MemberQ[converted, $Failed], Return[$Failed]];
  Expand[Total[converted]]
];

SewingSymbolToAmpForm[expr_, np_: Automatic, qSpec_: Automatic] := Module[
  {sq1, sq2, qActual, qTerms, qFactorQ, baseRules, replaceQ, qPairAmp, convertTerm, converted},
  {sq1, sq2} = If[IntegerQ[np], {2 np, 2 np - 1}, {8, 7}];
  qTerms = SewingQTerms[qSpec];
  If[qTerms === $Failed,
    Message[SewingSymbolToAmpForm::badq, qSpec];
    Return[$Failed]
  ];
  qFactorQ[f_] := MatchQ[f, _ab | _sb] && AnyTrue[List @@ f, SewingQLabelQ];
  baseRules = {
    s_Symbol /; SymbolName[Unevaluated[s]] === "Xhard" :> (sb[sq1, sq2] - ab[1, 2]),
    s_Symbol /; SymbolName[Unevaluated[s]] === "Xsoft" :> (sb[sq1, sq2] + ab[1, 2]),
    L1 -> sq1,
    L2 -> sq2,
    sb[1, x_] /; x =!= 2 :> sb[sq1, x],
    sb[x_, 1] /; x =!= 2 :> sb[x, sq1],
    sb[2, x_] /; x =!= 1 :> sb[sq2, x],
    sb[x_, 2] /; x =!= 1 :> sb[x, sq2],
    Xhard -> (sb[sq1, sq2] - ab[1, 2]),
    Xsoft -> (sb[sq1, sq2] + ab[1, 2])
  };
  replaceQ[f_ab, q_?Negative] := replaceQ[f, -q];
  replaceQ[f_sb, q_?Negative] := replaceQ[f, -q];
  replaceQ[ab[a_, b_], q_] := Which[
    SewingQLabelQ[a], ab[q, b],
    SewingQLabelQ[b], ab[a, q],
    True, ab[a, b]
  ];
  replaceQ[sb[a_, b_], q_] := Which[
    SewingQLabelQ[a], sb[q, b],
    SewingQLabelQ[b], sb[a, q],
    True, sb[a, b]
  ];
  qPairAmp[a_, s_] := Total[
    (If[IntegerQ[#] && Negative[#], -1, 1] replaceQ[a, #] replaceQ[s, #]) & /@ qTerms
  ];
  convertTerm[term_] := Module[{factors, qAngles, qSquares, baseFactors},
    factors = Prod2List[term];
    qAngles = Select[factors, qFactorQ[#] && Head[#] === ab &];
    qSquares = Select[factors, qFactorQ[#] && Head[#] === sb &];
    If[Length[qAngles] =!= Length[qSquares], Return[$Failed]];
    baseFactors = Select[factors, ! qFactorQ[#] &] /. baseRules;
    Expand[(Times @@ baseFactors) Times @@ MapThread[qPairAmp, {qAngles, qSquares}]]
  ];
  converted = convertTerm /@ Sum2List[Expand[expr]];
  If[MemberQ[converted, $Failed], Return[$Failed]];
  Expand[Total[converted]]
];

SewingRecordSymbolForm[rec_Association] := Lookup[
  rec,
  "SewingDisplayForm",
  Lookup[rec, "SewingSymForm",
  Lookup[rec, "TotalAmp", Lookup[rec, "AmpL", Missing["NoSymbolForm"]]]
  ]
];

SewingRecordAmpForm[rec_Association] := Lookup[
  rec,
  "SewingAmpForm",
  Lookup[rec, "TotalAmp", Lookup[rec, "AmpLAmpForm", Lookup[rec, "AmpL", Missing["NoAmpForm"]]]]
];

SewingOpenPairMonomials[m_Integer?NonNegative, np_: Automatic] := Module[
  {sq1, sq2},
  {sq1, sq2} = If[IntegerQ[np], {2 np, 2 np - 1}, {8, 7}];
  Flatten@Table[
  <|
    "OpenPowers" -> <|"Angle1" -> a, "Square1" -> m - a, "Angle2" -> b, "Square2" -> m - b|>,
    "Amp" -> ab[1, J]^a sb[sq1, J]^(m - a) ab[2, J]^b sb[sq2, J]^(m - b),
    "SymbolicAmp" -> ab[1, J]^a sb[L1, J]^(m - a) ab[2, J]^b sb[L2, J]^(m - b)
  |>,
  {a, 0, m}, {b, 0, m}
  ]
];

SewingBalancedOpenPairQ[open_Association] := Module[{p = open["OpenPowers"]},
  Lookup[p, "Angle1", 0] + Lookup[p, "Angle2", 0] ===
    Lookup[p, "Square1", 0] + Lookup[p, "Square2", 0]
];

ConstructLeft3PointOpenBasis[spinJ_Integer?NonNegative, OptionsPattern[]] := Module[
  {
    spin = OptionValue[MassiveSpin], pointCount = OptionValue[PointCount],
    qSpec = OptionValue[QReplacement], nSlots, openSlots, closedSlots, qExponent, qPower,
    closed, open, records
  },
  nSlots = 2 spin;
  If[! IntegerQ[nSlots] || nSlots < 0, Return[{}]];
  openSlots = Min[spinJ, nSlots];
  closedSlots = nSlots - openSlots;
  qExponent = Max[spinJ - nSlots, 0];
  qPower = (ab[Q, J] sb[Q, J])^qExponent;
  closed = SewingClosedPairMonomials[closedSlots, pointCount];
  open = SewingOpenPairMonomials[openSlots, pointCount];
  records = Flatten@Table[
    With[{sym = Expand[o["SymbolicAmp"] c["SymbolicAmp"] qPower]},
    <|
      "J" -> spinJ,
      "MassiveSpin" -> spin,
      "PointCount" -> pointCount,
      "OpenSlots" -> openSlots,
      "ClosedSlots" -> closedSlots,
      "LeftStructure" -> StringJoin["S", ToString[nSlots], "J", ToString[spinJ], "O", ToString[oi], "C", ToString[ci]],
      "OpenPowers" -> o["OpenPowers"],
      "ClosedPowers" -> c["ClosedPowers"],
      "SortData" -> <|
        "J" -> spinJ,
        "Xhard" -> c["ClosedPowers"]["Xhard"],
        "Xsoft" -> c["ClosedPowers"]["Xsoft"]
      |>,
      "QComponent" -> If[qExponent == 0, {}, {"Q"}],
      "QReplacement" -> qSpec,
      "AmpLSymbolForm" -> sym,
      "AmpLAmpForm" -> SewingSymbolToAmpForm[sym, pointCount, qSpec],
      "AmpL" -> SewingSymbolToAmpForm[sym, pointCount, qSpec],
      "ClosedBasisAmpL" -> sym
    |>],
    {oi, Length[open]}, {ci, Length[closed]},
    {o, {open[[oi]]}}, {c, {closed[[ci]]}}
  ];
  If[qSpec =!= Automatic,
    records = SewingApplyLeftQReplacement[#, qSpec] & /@ records;
    If[MemberQ[records, $Failed], Return[$Failed]]
  ];
  records
];

SewingApplyLeftQReplacement[leftRecord_Association, qSpec_] := Module[
  {amp, qBracketQ, qLabel, qActual, qCounts, ampForm},
  amp = Lookup[leftRecord, "AmpLSymbolForm", leftRecord["AmpL"]];
  qBracketQ[f_] := MatchQ[f, _ab | _sb] && MemberQ[List @@ f, Q] && MemberQ[List @@ f, J];
  qActual = Replace[qSpec, Automatic -> {1, -2}];
  qLabel = If[ListQ[qActual],
    StringJoin["Qsum", StringRiffle[ToString /@ qActual, ""]],
    StringJoin["Q", ToString[qSpec]]
  ];
  qCounts = DeleteDuplicates[
    Count[Prod2List[#], f_ /; qBracketQ[f] && Head[f] === ab] & /@ Sum2List[Expand[amp]]
  ];
  If[
    qCounts =!= DeleteDuplicates[
      Count[Prod2List[#], f_ /; qBracketQ[f] && Head[f] === sb] & /@ Sum2List[Expand[amp]]
    ],
    Return[$Failed]
  ];
  ampForm = SewingSymbolToAmpForm[amp, Lookup[leftRecord, "PointCount", Automatic], qSpec];
  If[ampForm === $Failed, Return[$Failed]];
  Append[
    leftRecord,
    {
      "OpenAmpL" -> amp,
      "QComponent" -> If[Max[qCounts] == 0, {}, {qLabel}],
      "QReplacement" -> qSpec,
      "AmpLSymbolForm" -> amp,
      "AmpLAmpForm" -> ampForm,
      "AmpL" -> ampForm
    }
  ]
];

ClearAll[SewingJOtherLabel];
SewingJOtherLabel[head_[a_, J]] := a;
SewingJOtherLabel[head_[J, b_]] := b;

ClearAll[SewingContractMonomialTerms, SewingContractMonomial];
SewingContractMonomialTerms[ampL_, ampR_] := Module[
  {leftFactors, rightFactors, allFactors, nonJFactors, contractHeadTerms, abTerms, sbTerms},
  leftFactors = Prod2List[ampL];
  rightFactors = Prod2List[ampR];
  allFactors = Join[leftFactors, rightFactors];
  nonJFactors = Select[allFactors, !(MatchQ[#, _ab | _sb] && MemberQ[List @@ #, J]) &];
  contractHeadTerms[head_] := Module[{left, right, n},
    left = SewingJOtherLabel /@
      Select[leftFactors, MatchQ[#, _[_, _]] && Head[#] === head && MemberQ[List @@ #, J] &];
    right = SewingJOtherLabel /@
      Select[rightFactors, MatchQ[#, _[_, _]] && Head[#] === head && MemberQ[List @@ #, J] &];
    n = Length[left];
    If[n =!= Length[right], Return[{}]];
    If[n == 0, Return[{1}]];
    Times @@@ (MapThread[head, {left, right[[#]]}] & /@ Permutations[Range[n]])
  ];
  abTerms = contractHeadTerms[ab];
  sbTerms = contractHeadTerms[sb];
  If[abTerms === {} || sbTerms === {}, Return[{}]];
  DeleteCases[Expand[(Times @@ nonJFactors) #1 #2] & @@@ Tuples[{abTerms, sbTerms}], 0]
];
SewingContractMonomial[ampL_, ampR_] := Expand[Total[SewingContractMonomialTerms[ampL, ampR]]];

Options[SymmetricSewContract] = {};
SewingContractionTerms[ampL_, ampR_] := Module[{leftTerms, rightTerms},
  leftTerms = Sum2List[Expand[ampL]];
  rightTerms = Sum2List[Expand[ampR]];
  DeleteCases[Flatten@Table[SewingContractMonomialTerms[l, r], {l, leftTerms}, {r, rightTerms}], 0]
];
SymmetricSewContract[ampL_, ampR_, OptionsPattern[]] := Module[{terms},
  terms = SewingContractionTerms[ampL, ampR];
  Expand[Total[terms]]
];

Options[SewingReducedMassless] = {
  MasslessRule -> {8 -> 1, 7 -> 2, 6 -> 3, 5 -> 4},
  EOMRules -> {
    sb[1, 1] -> 0, sb[2, 2] -> 0, ab[1, 1] -> 0, ab[2, 2] -> 0,
    sb[1, 8] -> 0, sb[2, 7] -> 0, sb[8, 1] -> 0, sb[7, 2] -> 0
  }
};
SewingReducedMassless[amp_, OptionsPattern[]] :=
  ReduceSt[4] @ ReplaceBraNumber[OptionValue[MasslessRule]][Expand[amp /. OptionValue[EOMRules]]];

SewingMasslessRule[np_Integer?Positive] := Table[2 np + 1 - i -> i, {i, np}];

SewingLeftSquareRelabelRule[np_Integer?Positive] := {
  8 -> 2 np,
  7 -> 2 np - 1
};

SewingLeftMassiveSquareRelabel[amp_, np_Integer?Positive] :=
  ReplaceBraNumber[SewingLeftSquareRelabelRule[np]][amp] /. {
    sb[1, 2] -> sb[2 np, 2 np - 1],
    sb[2, 1] -> sb[2 np - 1, 2 np]
  };

SewingLeftForPointCount[leftRecord_Association, np_Integer?Positive] := Module[
  {rule = SewingLeftSquareRelabelRule[np]},
  Join[
    leftRecord,
    <|
      "AmpL" -> SewingLeftMassiveSquareRelabel[leftRecord["AmpL"], np],
      "OriginalAmpL" -> leftRecord["AmpL"],
      "LeftSquareRelabelRule" -> rule
    |>
  ]
];

SewingGeneralEOMRules[np_Integer?Positive] := Module[{c1 = 2 np, c2 = 2 np - 1},
  {
    sb[1, 1] -> 0, sb[2, 2] -> 0, ab[1, 1] -> 0, ab[2, 2] -> 0,
    sb[1, c1] -> 0, sb[2, c2] -> 0, sb[c1, 1] -> 0, sb[c2, 2] -> 0
  }
];

Options[SewingReducedMasslessGeneral] = {
  PointCount -> Automatic,
  MasslessRule -> Automatic,
  EOMRules -> Automatic
};
SewingReducedMasslessGeneral[amp_, opts : OptionsPattern[]] := Module[
  {np, rule, eom},
  np = OptionValue[PointCount];
  If[np === Automatic, Return[SewingReducedMassless[amp]]];
  rule = Replace[OptionValue[MasslessRule], Automatic -> SewingMasslessRule[np]];
  eom = Replace[OptionValue[EOMRules], Automatic -> SewingGeneralEOMRules[np]];
  ReduceSt[np] @ ReplaceBraNumber[rule][Expand[amp /. eom]]
];

SewingRightJCountsMatchQ[leftAmp_, rightAmp_] := Module[{lc, rc},
  lc = SewingJCounts[leftAmp];
  rc = SewingJCounts[rightAmp];
  lc["AngleJ"] === rc["AngleJ"] && lc["SquareJ"] === rc["SquareJ"]
];

SewingBracketDegree[amp_] := DeleteDuplicates[
  Length[Select[Prod2List[#], MatchQ[#, _ab | _sb] &]] & /@ Sum2List[Expand[amp]]
];

SewingAmpDimMatchQ[amp_, ampDim_Integer] := SewingBracketDegree[amp] === {ampDim};

SewingLeftDegreeData[amp_] := Module[
  {termData},
  termData = DeleteDuplicates[
    Module[{brackets = Select[Prod2List[#], MatchQ[#, _ab | _sb] &], jCount},
      jCount = Count[brackets, f_ /; MemberQ[List @@ f, J]];
      <|"NonJ" -> Length[brackets] - jCount, "J" -> jCount, "Total" -> Length[brackets]|>
    ] & /@ Sum2List[Expand[amp]]
  ];
  If[Length[termData] == 1, First[termData], termData]
];

SewingCheckFailureQ[check_Association] := ! TrueQ[Lookup[check, "ValidQ", False]];

SewingCheckFailureMessage[check_Association] := ToString[check, InputForm];

SewingSortData[rec_Association] := Lookup[
  rec,
  "SortData",
  Lookup[Lookup[rec, "LeftRecord", <||>], "SortData", $Failed]
];

SewingSortDataQ[rec_Association] := Module[
  {data = SewingSortData[rec], j, xs, xh},
  If[! AssociationQ[data], Return[False]];
  j = Lookup[data, "J", Missing["Absent"]];
  xs = Lookup[data, "Xsoft", Missing["Absent"]];
  xh = Lookup[data, "Xhard", Missing["Absent"]];
  IntegerQ[j] && j >= 0 && IntegerQ[xs] && xs >= 0 && IntegerQ[xh] && xh >= 0
];

SewingStaticXPower[rec_Association] := Module[{data = SewingSortData[rec]},
  If[! TrueQ[SewingSortDataQ[rec]], Return[$Failed]];
  data["Xhard"]
];

SewingRelativeChiralOrder[rec_Association] := Module[{ampDim, data, staticX},
  ampDim = Lookup[rec, "AmpDim", Missing["Absent"]];
  data = SewingSortData[rec];
  staticX = SewingStaticXPower[rec];
  If[! IntegerQ[ampDim] || ! AssociationQ[data] || staticX === $Failed, Return[$Failed]];
  ampDim - staticX - data["J"]
];

SewingChiralSortKey[rec_Association] := Module[{data = SewingSortData[rec], order, staticX, kindPriority},
  order = SewingRelativeChiralOrder[rec];
  staticX = SewingStaticXPower[rec];
  If[order === $Failed || staticX === $Failed, Return[$Failed]];
  kindPriority = Which[
    data["J"] === 0 && staticX > 0, 0,
    data["J"] === 0, 1,
    True, 2
  ];
  {
    order,
    Lookup[rec, "AmpDim", 0],
    data["J"],
    kindPriority,
    SewingBasisSortKey[rec]
  }
];

SewingSortRecordsByChiralOrder[records_List] := Module[{bad},
  bad = Select[records, SewingChiralSortKey[#] === $Failed &];
  If[bad =!= {},
    Message[SewingSortRecordsByChiralOrder::metadata];
    Return[$Failed]
  ];
  SortBy[records, SewingChiralSortKey]
];

SewingBasisSortKey[rec_Association] := Module[
  {data = SewingSortData[rec]},
  {
    data["J"],
    -data["Xsoft"],
    -data["Xhard"],
    Lookup[rec, "LeftStructure", ""],
    ToString[Lookup[rec, "QComponent", {}], InputForm],
    Lookup[rec, "AuxiliarySpin", {}],
    ToString[Lookup[rec, "AmpR", 0], InputForm],
    Lookup[rec, "ContractionMode", ""],
    Lookup[rec, "ContractionTermIndex", 0]
  }
];

(* Basis reduction order is fixed by convention: lower J first, then higher
   Xsoft power, then higher Xhard power.  This is intentionally not an option. *)
SewingSortRecordsForBasis[records_List] := Module[{bad},
  bad = Select[records, ! TrueQ[SewingSortDataQ[#]] &];
  If[bad =!= {},
    Message[SewingSortRecordsForBasis::sortdata];
    Return[$Failed]
  ];
  SortBy[records, SewingBasisSortKey]
];

SewingLeftRecordCheck[left_Association] := Module[
  {issues = {}, jCounts, degree, qPower, expectedJ, expectedNonJ},
  jCounts = SewingJCounts[left["AmpL"]];
  degree = SewingLeftDegreeData[left["AmpL"]];
  qPower = Max[Lookup[left, "J", 0] - 2 Lookup[left, "MassiveSpin", 1/2], 0];
  expectedJ = 2 (Lookup[left, "OpenSlots", 0] + qPower);
  expectedNonJ = Lookup[left, "ClosedSlots", 0];
  If[jCounts === $Failed,
    AppendTo[issues, <|"Check" -> "3pt.JCounts", "Message" -> "J counts are not monomial-uniform."|>],
    If[jCounts["TotalJ"] =!= expectedJ,
      AppendTo[issues, <|"Check" -> "3pt.ExpectedJSlots", "Observed" -> jCounts["TotalJ"], "Expected" -> expectedJ|>]
    ]
  ];
  If[! AssociationQ[degree],
    AppendTo[issues, <|"Check" -> "3pt.DegreeUniform", "Observed" -> degree|>],
    If[degree["NonJ"] =!= expectedNonJ,
      AppendTo[issues, <|"Check" -> "3pt.NonJDegree", "Observed" -> degree["NonJ"], "Expected" -> expectedNonJ|>]
    ]
  ];
  <|"ValidQ" -> Length[issues] == 0, "Stage" -> "Left3Point", "Issues" -> issues, "Record" -> KeyDrop[left, {"LeftRecord", "RightRecord"}]|>
];

SewingRightRecordCheck[left_Association, right_Association, rightAmpDim_Integer] := Module[
  {issues = {}, rightDegree},
  If[! SewingRightJCountsMatchQ[left["AmpL"], right["AmpR"]],
    AppendTo[
      issues,
      <|
        "Check" -> "Right.JCountsMatch",
        "LeftJCounts" -> SewingJCounts[left["AmpL"]],
        "RightJCounts" -> SewingJCounts[right["AmpR"]]
      |>
    ]
  ];
  rightDegree = SewingBracketDegree[right["AmpR"]];
  If[rightDegree =!= {rightAmpDim},
    AppendTo[issues, <|"Check" -> "Right.AmpDim", "Observed" -> rightDegree, "Expected" -> rightAmpDim|>]
  ];
  <|"ValidQ" -> Length[issues] == 0, "Stage" -> "RightResidual", "Issues" -> issues, "AmpR" -> right["AmpR"], "RightRecord" -> KeyDrop[right, {"AuxiliaryAmp"}]|>
];

SewingSewnRecordCheck[record_Association, fullMass_List, cfPolarizations_List] := Module[
  {issues = {}, np, metas, physicalTerms, reduced, expectedSpins},
  np = record["PointCount"];
  metas = SewingAmpMetaTerms[record["TotalAmp"], np, fullMass];
  reduced = record["ReducedAmp"];
  expectedSpins = Join[{record["LeftSpin"], record["LeftSpin"]}, record["RightSpins"]];
  physicalTerms = If[
    SewingContainsXSymbolQ[Lookup[record, "SewingSymForm", 0]],
    Sum2List[Expand[record["TotalAmp"]]],
    Select[
      Sum2List[Expand[record["TotalAmp"]]],
      SewingPhysicalAmpTermQ[#, np, fullMass, expectedSpins, cfPolarizations] &
    ]
  ];
  If[Length[metas] == 0 || ! AllTrue[metas, SewingValidMetaQ[#, np] &],
    AppendTo[issues, <|"Check" -> "Sewing.Amp2MetaInfo.Valid", "MetaTerms" -> metas|>]
  ];
  If[Length[physicalTerms] == 0,
    AppendTo[
      issues,
      <|"Check" -> "Sewing.Amp2MetaInfo.PhysicalSector", "MetaTerms" -> metas, "ExpectedSpins" -> expectedSpins, "AllowedPolarizations" -> cfPolarizations|>
    ]
  ];
  If[TrueQ[Expand[reduced] === 0],
    AppendTo[issues, <|"Check" -> "Sewing.ReducedNonZero", "Message" -> "ReducedAmp vanished after massless limit and ReduceSt."|>]
  ];
  <|
    "ValidQ" -> Length[issues] == 0,
    "Stage" -> "Sewing",
    "Issues" -> issues,
    "J" -> record["J"],
    "LeftStructure" -> record["LeftStructure"],
    "AmpL" -> record["AmpL"],
    "AmpR" -> record["AmpR"],
    "TotalAmp" -> record["TotalAmp"],
    "ReducedAmp" -> reduced
  |>
];

SewingCodeDimFromAmpDim[ampDim_Integer, np_Integer?Positive] := ampDim + np;

SewingDefaultJMax[leftSpin_, ampDim_Integer, rightSpins_List] := Module[{nSlots = 2 leftSpin},
  Max[0, Floor[ampDim/2]]
];

SewingAutoJSearchLimit[leftSpin_, ampDim_Integer, rightSpins_List] := Module[
  {base = SewingDefaultJMax[leftSpin, ampDim, rightSpins], spinPad},
  spinPad = Max[0, Ceiling[2 Total[Abs[rightSpins]]]];
  Max[base + spinPad + 3, ampDim + spinPad + 3]
];

SewingDefaultRightMass[np_Integer?Positive] := If[np >= 3, {3}, {}];
SewingMassLabelValue[i_Integer?Positive] :=
  "\!\(\*SubscriptBox[\(m\), \(" <> ToString[i] <> "\)]\)";
SewingMassVectorFromPositions[positions_List, np_Integer?Positive] :=
  Table[If[MemberQ[positions, i], SewingMassLabelValue[i], 0], {i, np}];

SewingMassOptionData[leftMassIn_, rightMassIn_, rightSpins_List] := Module[
  {np = 2 + Length[rightSpins], rightMass, rightPositionQ, rightVectorQ, leftVector, rightVector},
  rightMass = Replace[rightMassIn, Automatic -> SewingDefaultRightMass[np]];
  rightPositionQ = ListQ[rightMass] && And @@ ((IntegerQ[#] && 3 <= # <= np) & /@ rightMass);
  rightVectorQ = ListQ[rightMass] && Length[rightMass] == Length[rightSpins] && ! rightPositionQ;
  Which[
    rightPositionQ,
      leftVector = MassOption[leftMassIn, 2];
      rightVector = SewingMassVectorFromPositions[rightMass, np];
      <|
        "RightConstructMass" -> rightVector,
        "FullMass" -> Join[leftVector, Drop[rightVector, 2]],
        "PhysicalRightMass" -> rightMass
      |>,
    rightVectorQ,
      leftVector = MassOption[leftMassIn, 2];
      <|
        "RightConstructMass" -> Join[{0, 0}, rightMass],
        "FullMass" -> Join[leftVector, rightMass],
        "PhysicalRightMass" -> Flatten[Position[rightMass, Except[0]]] + 2
      |>,
    True,
      <|
        "RightConstructMass" -> rightMass,
        "FullMass" -> Join[MassOption[leftMassIn, 2], Drop[MassOption[rightMass, np], 2]],
        "PhysicalRightMass" -> Flatten[Position[Drop[MassOption[rightMass, np], 2], Except[0]]] + 2
      |>
  ]
];

Options[ConstructGeneralSewingAmplitudeRecords] = Join[
  {
    RightMass -> Automatic,
    LeftMass -> {1, 2},
    JRange -> Automatic,
    JMax -> Automatic,
    AuxiliarySpinRange -> Automatic,
    EqualAuxiliarySpin -> True,
    QReplacement -> {1, -2},
    AutoJNoRightWindow -> 3,
    SewingContractionMode -> "Split",
    VerifyAmpDim -> True,
    Check3Point -> False,
    CheckRight -> False,
    CheckSewing -> False,
    CheckVerbose -> False,
    FilterPhysicalSector -> True,
    FilterByAmpDim -> True,
    DeduplicateByReducedAmp -> False,
    SewingDebug -> False
  },
  Options[ConstructRightAuxiliaryOnShellRecords],
  Options[SewingReducedMasslessGeneral]
];
ConstructGeneralSewingAmplitudeRecords[
  leftSpin_,
  rightSpins_List,
  rightMass_,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := ConstructGeneralSewingAmplitudeRecords[
  leftSpin,
  rightSpins,
  ampDim,
  rightPolarization,
  Sequence @@ Join[{RightMass -> rightMass}, {opts}]
];

ConstructGeneralSewingAmplitudeRecords[
  leftSpin_,
  rightSpins_List,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := Module[
  {
    npFull, npRight, rightMassData, rightMass, jRangeOpt, jMaxOpt, jRange, autoJQ,
    autoJLimit, noRightWindow, noRightCount,
    leftRecords, rightRecordsFor, rightRecords, rows, reducedOpts, key, qSpec, contractionMode,
    leftChecks, failedChecks, cfPolarizations, debug, buildLeftRecordsForJ, jLeftRecords, hasRightRecordsQ
  },
  debug = TrueQ[OptionValue[SewingDebug]];
  npFull = 2 + Length[rightSpins];
  npRight = 2 + Length[rightSpins];
  If[npFull < 4 || Length[rightPolarization] =!= Length[rightSpins],
    Message[ConstructGeneralSewingAmplitudeRecords::args, npFull, Length[rightSpins], Length[rightPolarization]];
    Return[{}]
  ];
  rightMassData = SewingMassOptionData[OptionValue[LeftMass], OptionValue[RightMass], rightSpins];
  rightMass = rightMassData["RightConstructMass"];
  jRangeOpt = OptionValue[JRange];
  jMaxOpt = OptionValue[JMax];
  autoJQ = ! ListQ[jRangeOpt] && ! IntegerQ[jMaxOpt];
  jRange = Which[
    ListQ[jRangeOpt], jRangeOpt,
    IntegerQ[jMaxOpt], Range[0, jMaxOpt],
    True, {}
  ];
  qSpec = OptionValue[QReplacement];
  contractionMode = OptionValue[SewingContractionMode];
  If[! MemberQ[{"Split", "Sum"}, contractionMode],
    Message[ConstructGeneralSewingAmplitudeRecords::mode, contractionMode];
    Return[$Failed]
  ];
  SewingLog[
    debug,
    "General.Start",
    <|"LeftSpin" -> leftSpin, "RightSpins" -> rightSpins, "AmpDim" -> ampDim, "JRange" -> jRange|>
  ];
  cfPolarizations = Flatten[
    Table[
      Join[{a, b}, rightPolarization],
      {a, Range[0, 2 leftSpin]},
      {b, Range[0, 2 leftSpin]}
    ],
    1
  ];
  rightRecordsFor[left_Association] := rightRecordsFor[
    left["J"],
    ToString[left["AmpL"], InputForm],
    ampDim - SewingLeftDegreeData[left["AmpL"]]["Total"] + SewingJCounts[left["AmpL"]]["TotalJ"]
  ] = Module[
    {leftJCounts = SewingJCounts[left["AmpL"]], rightAmpDim},
    rightAmpDim = ampDim - SewingLeftDegreeData[left["AmpL"]]["Total"] + leftJCounts["TotalJ"];
    If[rightAmpDim < 0,
      {},
      Module[{rr},
        rr = Append[#, "RightAmpDim" -> rightAmpDim] & /@
          ConstructRightProjectedJResidualRecords[
            <|"AngleJ" -> leftJCounts["AngleJ"], "SquareJ" -> leftJCounts["SquareJ"]|>,
            rightSpins,
            rightMass,
            rightPolarization,
            rightAmpDim,
            Sequence @@ Join[
              FilterRules[{opts}, Options[ConstructRightProjectedJResidualRecords]],
              {
                CodeDim -> SewingCodeDimFromAmpDim[rightAmpDim, npRight],
                EqualAuxiliarySpin -> OptionValue[EqualAuxiliarySpin]
              }
            ]
          ];
        SewingLog[debug, "General.RightRecords", <|"J" -> left["J"], "RightAmpDim" -> rightAmpDim, "Count" -> Length[rr]|>];
        rr
      ]
    ]
  ];
  buildLeftRecordsForJ[j_Integer?NonNegative] := ConstructLeft3PointOpenBasis[
      j,
      MassiveSpin -> leftSpin,
      PointCount -> npFull,
      QReplacement -> qSpec
  ];
  hasRightRecordsQ[records_List] := AnyTrue[records, Length[rightRecordsFor[#]] > 0 &];
  If[TrueQ[autoJQ],
    autoJLimit = SewingAutoJSearchLimit[leftSpin, ampDim, rightSpins];
    noRightWindow = OptionValue[AutoJNoRightWindow];
    If[! IntegerQ[noRightWindow] || noRightWindow < 1, noRightWindow = 3];
    noRightCount = 0;
    leftRecords = Reap[
      Do[
        jLeftRecords = buildLeftRecordsForJ[j];
        If[MemberQ[jLeftRecords, $Failed], Sow[$Failed]; Break[]];
        If[hasRightRecordsQ[jLeftRecords],
          noRightCount = 0;
          Scan[Sow, jLeftRecords],
          noRightCount++;
          If[noRightCount >= noRightWindow,
            SewingLog[debug, "General.AutoJStop", <|"LastJ" -> j, "NoRightWindow" -> noRightWindow|>];
            Break[]
          ]
        ],
        {j, 0, autoJLimit}
      ]
    ][[2]];
    leftRecords = If[leftRecords === {}, {}, First[leftRecords]];
    jRange = DeleteDuplicates[Lookup[Cases[leftRecords, _Association], "J", {}]],
    leftRecords = Flatten[buildLeftRecordsForJ /@ jRange]
  ];
  If[MemberQ[leftRecords, $Failed], Return[$Failed]];
  SewingLog[debug, "General.LeftRecords", <|"Count" -> Length[leftRecords]|>];
  If[TrueQ[OptionValue[Check3Point]],
    leftChecks = SewingLeftRecordCheck /@ leftRecords;
    failedChecks = Select[leftChecks, SewingCheckFailureQ];
    If[Length[failedChecks] > 0,
      Message[ConstructGeneralSewingAmplitudeRecords::check, SewingCheckFailureMessage[First[failedChecks]]];
      Return[$Failed]
    ];
    If[TrueQ[OptionValue[CheckVerbose]], Print["Sewing 3pt checks passed: ", Length[leftChecks]]]
  ];
  reducedOpts = Sequence @@ Join[
    FilterRules[{opts}, Options[SewingReducedMasslessGeneral]],
    {PointCount -> npFull}
  ];
  rows = Catch[Flatten@Table[
    rightRecords = rightRecordsFor[left];
    Table[
      If[! SewingRightJCountsMatchQ[left["AmpL"], right["AmpR"]], Nothing,
        Module[{symTotals, ampTotals, symTotal, totalRaw, totalTerms, total, rec, check},
          symTotals = Switch[
            contractionMode,
            "Sum", {SymmetricSewContract[left["AmpLSymbolForm"], right["AmpR"]]},
            "Split", SewingContractionTerms[left["AmpLSymbolForm"], right["AmpR"]]
          ];
          If[Length[symTotals] == 0, Nothing,
          ampTotals = SewingSymbolToAmpForm[#, npFull, qSpec] & /@ symTotals;
          If[MemberQ[ampTotals, $Failed], Throw[$Failed, ConstructGeneralSewingAmplitudeRecords]];
          Table[
          symTotal = symTotals[[termIndex]];
          totalRaw = ampTotals[[termIndex]];
          totalTerms = Sum2List[Expand[totalRaw]];
          total = If[TrueQ[OptionValue[FilterPhysicalSector]] && ! SewingContainsXSymbolQ[symTotal],
            Total @ Select[
              totalTerms,
              SewingPhysicalAmpTermQ[
                #,
                npFull,
                rightMassData["FullMass"],
                Join[{leftSpin, leftSpin}, rightSpins],
                cfPolarizations
              ] &
            ],
            totalRaw
          ];
          If[total === 0, Nothing,
          If[TrueQ[OptionValue[CheckRight]],
            check = SewingRightRecordCheck[left, right, right["RightAmpDim"]];
            If[SewingCheckFailureQ[check],
              Message[ConstructGeneralSewingAmplitudeRecords::check, SewingCheckFailureMessage[check]];
              Throw[$Failed, ConstructGeneralSewingAmplitudeRecords]
            ]
          ];
          If[TrueQ[OptionValue[VerifyAmpDim]] && ! SewingAmpDimMatchQ[total, ampDim],
            Message[
              ConstructGeneralSewingAmplitudeRecords::ampdim,
              left["J"],
              SewingLeftDegreeData[left["AmpL"]],
              right["RightAmpDim"],
              SewingBracketDegree[total],
              ampDim
            ];
            Throw[$Failed, ConstructGeneralSewingAmplitudeRecords],
            rec = <|
              "J" -> left["J"],
              "AmpDim" -> ampDim,
              "RightAmpDim" -> right["RightAmpDim"],
              "LeftDegreeData" -> SewingLeftDegreeData[left["AmpL"]],
              "CodeDim" -> SewingCodeDimFromAmpDim[ampDim, npFull],
              "PointCount" -> npFull,
              "LeftSpin" -> leftSpin,
              "RightSpins" -> rightSpins,
              "RightMass" -> rightMassData["PhysicalRightMass"],
              "RightConstructMass" -> rightMass,
              "RightPolarization" -> rightPolarization,
              "LeftStructure" -> left["LeftStructure"],
              "SortData" -> left["SortData"],
              "QComponent" -> left["QComponent"],
              "QReplacement" -> Lookup[left, "QReplacement", None],
              "ContractionMode" -> contractionMode,
              "ContractionTermIndex" -> termIndex,
              "ContractionTermCount" -> Length[symTotals],
              "OpenAmpL" -> left["OpenAmpL"],
              "ClosedBasisAmpL" -> left["ClosedBasisAmpL"],
              "AuxiliarySpin" -> right["AuxiliarySpin"],
              "AmpLSymbolForm" -> left["AmpLSymbolForm"],
              "AmpLAmpForm" -> left["AmpLAmpForm"],
              "AmpL" -> left["AmpL"],
              "AmpR" -> right["AmpR"],
              "SewingSymForm" -> symTotal,
              "SewingDisplayForm" -> SewingDisplayForm[symTotal, npFull],
              "SewingAmpFormRaw" -> totalRaw,
              "SewingAmpFormTerms" -> totalTerms,
              "SewingAmpForm" -> total,
              "FormMap" -> <|
                "SymbolForm" -> symTotal,
                "DisplayForm" -> SewingDisplayForm[symTotal, npFull],
                "AmpFormRaw" -> totalRaw,
                "WorkingAmpForm" -> total
              |>,
              "TotalAmp" -> total,
              "ReducedAmp" -> SewingReducedMasslessGeneral[total, reducedOpts],
              "LeftRecord" -> left,
              "RightRecord" -> right
            |>;
            If[TrueQ[OptionValue[FilterPhysicalSector]] || TrueQ[OptionValue[CheckSewing]],
              check = SewingSewnRecordCheck[rec, rightMassData["FullMass"], cfPolarizations];
              If[TrueQ[OptionValue[FilterPhysicalSector]] && SewingCheckFailureQ[check],
                Nothing,
                If[TrueQ[OptionValue[CheckSewing]] && SewingCheckFailureQ[check],
                  Message[ConstructGeneralSewingAmplitudeRecords::check, SewingCheckFailureMessage[check]];
                  Throw[$Failed, ConstructGeneralSewingAmplitudeRecords]
                ];
                rec
              ],
              rec
            ]
          ]],
          {termIndex, Length[symTotals]}]
          ]
        ]
      ],
      {right, rightRecords}
    ],
    {left, leftRecords}
  ], ConstructGeneralSewingAmplitudeRecords];
  If[rows === $Failed, Return[$Failed]];
  SewingLog[debug, "General.Rows", <|"RowsBeforeDedup" -> Length[rows]|>];
  key[rec_] := If[TrueQ[OptionValue[DeduplicateByReducedAmp]],
    ToString[rec["ReducedAmp"], InputForm],
    ToString[{rec["J"], rec["LeftStructure"], rec["QComponent"], rec["AuxiliarySpin"], rec["SewingSymForm"], rec["SewingAmpForm"], rec["AmpR"], rec["ContractionMode"], rec["ContractionTermIndex"]}, InputForm]
  ];
  rows = DeleteDuplicatesBy[rows, key];
  SewingLog[debug, "General.Done", <|"Rows" -> Length[rows]|>];
  rows
];

Options[SewingIndependentBlockFromRecords] = {ReturnRecords -> False, SewingOutputForm -> "SymbolForm"};
SewingIndependentBlockFromRecords[records_List, basis_: Automatic, OptionsPattern[]] := Module[
  {monoms, reduced, matrix, posIndep, selected, empty, outputForm, outputAmps},
  empty = If[TrueQ[OptionValue[ReturnRecords]],
    <|"Records" -> {}, "Amplitudes" -> {}, "Matrix" -> {}, "Monomials" -> {}, "Positions" -> {}|>,
    {}
  ];
  outputForm = OptionValue[SewingOutputForm];
  If[Length[records] == 0, Return[empty]];
  reduced = Lookup[records, "ReducedAmp", {}];
  monoms = Replace[basis, Automatic -> Poly2Singlet[reduced]];
  If[Length[monoms] == 0, Return[empty]];
  matrix = Table[Coefficient[Expand[row], monom], {row, reduced}, {monom, monoms}];
  posIndep = FindIndependentBasisPos[matrix];
  selected = records[[posIndep]];
  outputAmps = Switch[
    outputForm,
    "SymbolForm", SewingRecordSymbolForm /@ selected,
    "AmpForm", SewingRecordAmpForm /@ selected,
    _, SewingRecordSymbolForm /@ selected
  ];
  If[TrueQ[OptionValue[ReturnRecords]],
    <|
      "Records" -> selected,
      "Amplitudes" -> outputAmps,
      "Matrix" -> matrix[[posIndep]],
      "Monomials" -> monoms,
      "Positions" -> posIndep
    |>,
    {outputAmps, matrix[[posIndep]], monoms}
  ]
];

Options[SewingCoeffMatrixDataUnion] = {};
SewingCoeffMatrixDataUnion[records_List, basis_List] := Module[{reduced, matrix},
  If[Length[records] == 0, Return[<|"Monomials" -> basis, "Matrix" -> {}, "Rank" -> 0|>]];
  reduced = records[[All, "ReducedAmp"]];
  matrix = Table[Coefficient[Expand[row], monom], {row, reduced}, {monom, basis}];
  <|"Monomials" -> basis, "Matrix" -> matrix, "Rank" -> MatrixRank[matrix]|>
];

SewingProjectReducedAmpToBasis[amp_, basis_List] := Expand[
  Total[Coefficient[Expand[amp], #] # & /@ basis]
];

SewingValidMetaQ[meta_, np_Integer?Positive] :=
  ListQ[meta] && Length[meta] == 2 && ListQ[meta[[2]]] && Length[meta[[2]]] == np;

SewingAmpMetaTerms[amp_, np_Integer?Positive, masses_] :=
  DeleteDuplicates[Amp2MetaInfo[#, np, mass -> masses] & /@ Sum2List[Expand[amp]]];

SewingPhysicalAmpTermQ[
  term_,
  np_Integer?Positive,
  masses_,
  expectedSpins_List,
  cfPolarizations_List
] := Module[{meta = Amp2MetaInfo[term, np, mass -> masses]},
  SewingValidMetaQ[meta, np] && meta[[1]] === expectedSpins && MemberQ[cfPolarizations, meta[[2]]]
];

SewingRecordPolarizationMatchQ[rec_Association, cfPolarizations_List, np_Integer?Positive, masses_] := Module[
  {terms = Sum2List[Expand[rec["TotalAmp"]]], expectedSpins},
  If[SewingContainsXSymbolQ[Lookup[rec, "SewingSymForm", 0]], Return[True]];
  expectedSpins = Join[{rec["LeftSpin"], rec["LeftSpin"]}, rec["RightSpins"]];
  AnyTrue[terms, SewingPhysicalAmpTermQ[#, np, masses, expectedSpins, cfPolarizations] &]
];

Options[CompareGeneralSewingToCFBlocks] = Join[
  {
    RightMass -> Automatic,
    LeftMass -> {1, 2},
    LeftPolarizationRange -> Automatic,
    CFPolarizations -> Automatic,
    FilterSewingByCFPolarization -> True
  },
  Options[ConstructGeneralSewingAmplitudeRecords],
  Options[SewingReducedMasslessGeneral]
];
CompareGeneralSewingToCFBlocks[
  leftSpin_,
  rightSpins_List,
  rightMass_,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := CompareGeneralSewingToCFBlocks[
  leftSpin,
  rightSpins,
  ampDim,
  rightPolarization,
  Sequence @@ Join[{RightMass -> rightMass}, {opts}]
];

CompareGeneralSewingToCFBlocks[
  leftSpin_,
  rightSpins_List,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := Module[
  {
    np, codeDim, leftMass, rightMassData, rightMass, fullMass, spins, leftPolarRange, cfPolarizations,
    cfRows, sewingRows, basis, cfBasis, cfMatrix, sewingMatrix, joinedMatrix, debug
  },
  debug = TrueQ[OptionValue[SewingDebug]];
  np = 2 + Length[rightSpins];
  If[np < 4, Return[<|"Error" -> "Right side must contain at least two physical particles, so full n must be at least 4."|>]];
  codeDim = SewingCodeDimFromAmpDim[ampDim, np];
  leftMass = OptionValue[LeftMass];
  rightMassData = SewingMassOptionData[leftMass, OptionValue[RightMass], rightSpins];
  rightMass = rightMassData["RightConstructMass"];
  fullMass = rightMassData["FullMass"];
  spins = Join[{leftSpin, leftSpin}, rightSpins];
  leftPolarRange = Replace[OptionValue[LeftPolarizationRange], Automatic -> Range[0, 2 leftSpin]];
  cfPolarizations = Replace[
    OptionValue[CFPolarizations],
    Automatic -> Flatten[Table[Join[{a, b}, rightPolarization], {a, leftPolarRange}, {b, leftPolarRange}], 1]
  ];
  cfRows = Flatten@Table[
    Module[{cf = Quiet@Check[ConstructIndepCFBlock[spins, codeDim, polar, mass -> fullMass], $Failed], amps},
      If[! ListQ[cf] || Length[cf] < 3 || Length[cf[[1]]] == 0,
        Nothing,
        amps = cf[[1]];
        Table[
          <|
            "AmpDim" -> ampDim,
            "CodeDim" -> codeDim,
            "PointCount" -> np,
            "Polarization" -> polar,
            "Amp" -> amps[[i]],
            "Meta" -> Amp2MetaInfo[amps[[i]], np, mass -> fullMass],
            "ReducedAmp" -> SewingReducedMasslessGeneral[
              amps[[i]],
              Sequence @@ Join[FilterRules[{opts}, Options[SewingReducedMasslessGeneral]], {PointCount -> np}]
            ]
          |>,
          {i, Length[amps]}
        ]
      ]
    ],
    {polar, cfPolarizations}
  ];
  SewingLog[debug, "Compare.CF", <|"CFRecords" -> Length[cfRows], "CFPolarizations" -> Length[cfPolarizations]|>];
  sewingRows = ConstructGeneralSewingAmplitudeRecords[
    leftSpin,
    rightSpins,
    ampDim,
    rightPolarization,
    Sequence @@ Join[
      FilterRules[{opts}, Options[ConstructGeneralSewingAmplitudeRecords]],
      {RightMass -> rightMassData["PhysicalRightMass"], PointCount -> np}
    ]
  ];
  If[sewingRows === $Failed,
    basis = Poly2Singlet[Lookup[cfRows, "ReducedAmp", {}]];
    cfMatrix = SewingCoeffMatrixDataUnion[cfRows, basis];
    sewingMatrix = SewingCoeffMatrixDataUnion[{}, basis];
    joinedMatrix = SewingCoeffMatrixDataUnion[cfRows, basis];
    Return[
      <|
        "Error" -> "Sewing record construction failed before CF comparison.",
        "AmpDim" -> ampDim,
        "CodeDim" -> codeDim,
        "PointCount" -> np,
        "Spins" -> spins,
        "Mass" -> fullMass,
        "RightPolarization" -> rightPolarization,
        "CFPolarizations" -> cfPolarizations,
        "CFRecords" -> cfRows,
        "SewingRecords" -> $Failed,
        "Monomials" -> basis,
        "CFMatrix" -> cfMatrix,
        "SewingMatrix" -> sewingMatrix,
        "JoinedMatrix" -> joinedMatrix,
        "CompleteQ" -> False
      |>
    ]
  ];
  If[TrueQ[OptionValue[FilterSewingByCFPolarization]],
    sewingRows = Select[sewingRows, SewingRecordPolarizationMatchQ[#, cfPolarizations, np, fullMass] &]
  ];
  SewingLog[debug, "Compare.Sewing", <|"SewingRecords" -> Length[sewingRows]|>];
  sewingRows = Append[#, "MetaTerms" -> SewingAmpMetaTerms[#["TotalAmp"], np, fullMass]] & /@ sewingRows;
  cfBasis = Poly2Singlet[Lookup[cfRows, "ReducedAmp", {}]];
  sewingRows = Append[#, "UnprojectedReducedAmp" -> #["ReducedAmp"]] & /@ sewingRows;
  sewingRows = Append[#, "ReducedAmp" -> SewingProjectReducedAmpToBasis[#["ReducedAmp"], cfBasis]] & /@ sewingRows;
  sewingRows = Select[sewingRows, Expand[#["ReducedAmp"]] =!= 0 &];
  basis = Poly2Singlet[Join[Lookup[cfRows, "ReducedAmp", {}], Lookup[sewingRows, "ReducedAmp", {}]]];
  cfMatrix = SewingCoeffMatrixDataUnion[cfRows, basis];
  sewingMatrix = SewingCoeffMatrixDataUnion[sewingRows, basis];
  joinedMatrix = SewingCoeffMatrixDataUnion[Join[cfRows, sewingRows], basis];
  SewingLog[
    debug,
    "Compare.Ranks",
    <|"CFRank" -> cfMatrix["Rank"], "SewingRank" -> sewingMatrix["Rank"], "JoinedRank" -> joinedMatrix["Rank"]|>
  ];
  <|
    "AmpDim" -> ampDim,
    "CodeDim" -> codeDim,
    "PointCount" -> np,
    "Spins" -> spins,
    "Mass" -> fullMass,
    "RightPolarization" -> rightPolarization,
    "CFPolarizations" -> cfPolarizations,
    "CFRecords" -> cfRows,
    "SewingRecords" -> sewingRows,
    "Monomials" -> basis,
    "CFMatrix" -> cfMatrix,
    "SewingMatrix" -> sewingMatrix,
    "JoinedMatrix" -> joinedMatrix,
    "CompleteQ" -> (cfMatrix["Rank"] == sewingMatrix["Rank"] && cfMatrix["Rank"] == joinedMatrix["Rank"])
  |>
];

Options[ConstructIndepSewingBlock] = Join[
  {
    CheckAgainstCF -> False,
    FilterSewingByCFPolarization -> False,
    ReturnRecords -> False,
    SewingOutputForm -> "SymbolForm",
    SewingDebug -> False
  },
  DeleteCases[Options[CompareGeneralSewingToCFBlocks], (FilterSewingByCFPolarization -> _)]
];
ConstructIndepSewingBlock[
  leftSpin_,
  rightSpins_List,
  rightMass_,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := ConstructIndepSewingBlock[
  leftSpin,
  rightSpins,
  ampDim,
  rightPolarization,
  Sequence @@ Join[{RightMass -> rightMass}, {opts}]
];

ConstructIndepSewingBlock[
  leftSpin_,
  rightSpins_List,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := Module[
  {
    records, comparison, np, leftMass, rightMassData, fullMass, leftPolarRange,
    cfPolarizations, block, blockMatrix, blockRows, blockRank, cfRank, debug
  },
  debug = TrueQ[OptionValue[SewingDebug]];
  If[TrueQ[OptionValue[CheckAgainstCF]],
    SewingLog[debug, "Independent.CompareStart", <|"LeftSpin" -> leftSpin, "AmpDim" -> ampDim|>];
    comparison = CompareGeneralSewingToCFBlocks[
      leftSpin,
      rightSpins,
      ampDim,
      rightPolarization,
      Sequence @@ FilterRules[{opts}, Options[CompareGeneralSewingToCFBlocks]]
    ];
    If[! AssociationQ[comparison] || ! TrueQ[Lookup[comparison, "CompleteQ", False]],
      Message[
        ConstructIndepSewingBlock::cfcheck,
        Lookup[Lookup[comparison, "CFMatrix", <|"Rank" -> Missing["Unavailable"]|>], "Rank", Missing["Unavailable"]],
        Lookup[Lookup[comparison, "SewingMatrix", <|"Rank" -> Missing["Unavailable"]|>], "Rank", Missing["Unavailable"]],
        Lookup[Lookup[comparison, "JoinedMatrix", <|"Rank" -> Missing["Unavailable"]|>], "Rank", Missing["Unavailable"]]
      ];
      Return[$Failed]
    ];
    records = SewingSortRecordsForBasis[comparison["SewingRecords"]];
    If[records === $Failed, Return[$Failed]];
    block = SewingIndependentBlockFromRecords[
      records,
      comparison["Monomials"],
      Sequence @@ FilterRules[{opts}, Options[SewingIndependentBlockFromRecords]]
    ];
    cfRank = comparison["CFMatrix"]["Rank"];
    blockMatrix = If[AssociationQ[block], Lookup[block, "Matrix", {}], If[ListQ[block] && Length[block] == 3, block[[2]], {}]];
    blockRows = If[AssociationQ[block], Length[Lookup[block, "Records", {}]], If[ListQ[block] && Length[block] >= 1, Length[block[[1]]], 0]];
    blockRank = If[blockMatrix === {}, 0, MatrixRank[blockMatrix]];
    SewingLog[debug, "Independent.Block", <|"BlockRows" -> blockRows, "BlockRank" -> blockRank, "CFRank" -> cfRank|>];
    If[
      ! (blockRows > 0 && blockRank == blockRows && blockRank == cfRank),
      Message[
        ConstructIndepSewingBlock::indcheck,
        ToString[
          <|
            "BlockRows" -> blockRows,
            "BlockRank" -> blockRank,
            "CFRank" -> cfRank,
            "SewingRank" -> comparison["SewingMatrix"]["Rank"],
            "JoinedRank" -> comparison["JoinedMatrix"]["Rank"]
          |>,
          InputForm
        ]
      ];
      Return[$Failed]
    ];
    Return[block]
  ];
  records = ConstructGeneralSewingAmplitudeRecords[
    leftSpin,
    rightSpins,
    ampDim,
    rightPolarization,
    Sequence @@ FilterRules[{opts}, Options[ConstructGeneralSewingAmplitudeRecords]]
  ];
  If[records === $Failed, Message[ConstructIndepSewingBlock::records]; Return[$Failed]];
  If[TrueQ[OptionValue[FilterSewingByCFPolarization]],
    np = 2 + Length[rightSpins];
    leftMass = OptionValue[LeftMass];
    rightMassData = SewingMassOptionData[leftMass, OptionValue[RightMass], rightSpins];
    fullMass = rightMassData["FullMass"];
    leftPolarRange = Replace[OptionValue[LeftPolarizationRange], Automatic -> Range[0, 2 leftSpin]];
    cfPolarizations = Replace[
      OptionValue[CFPolarizations],
      Automatic -> Flatten[Table[Join[{a, b}, rightPolarization], {a, leftPolarRange}, {b, leftPolarRange}], 1]
    ];
    records = Select[records, SewingRecordPolarizationMatchQ[#, cfPolarizations, np, fullMass] &]
  ];
  records = SewingSortRecordsForBasis[records];
  If[records === $Failed, Return[$Failed]];
  block = SewingIndependentBlockFromRecords[
    records,
    Automatic,
    Sequence @@ FilterRules[{opts}, Options[SewingIndependentBlockFromRecords]]
  ];
  SewingLog[debug, "Independent.Done", <|"InputRecords" -> Length[records], "BlockRows" -> If[ListQ[block] && Length[block] >= 1, Length[block[[1]]], 0]|>];
  block
];

Options[ConstructSewingRelativeChiralBasis] = Join[
  {ReplaceQInFinalSymbolForm -> True},
  Options[ConstructIndepSewingBlock]
];
ConstructSewingRelativeChiralBasis[
  leftSpin_,
  rightSpins_List,
  rightMass_,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := ConstructSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  ampDim,
  rightPolarization,
  Sequence @@ Join[{RightMass -> rightMass}, {opts}]
];

ConstructSewingRelativeChiralBasis[
  leftSpin_,
  rightSpins_List,
  ampDim_Integer,
  rightPolarization_List,
  opts : OptionsPattern[]
] := Module[
  {
    comparison, records, sorted, block, selected, ampsByOrder, outputAmp, cfRank, sewingRank, joinedRank,
    selectedCount, selectedRank, outputCount, debug
  },
  debug = TrueQ[OptionValue[SewingDebug]];
  comparison = CompareGeneralSewingToCFBlocks[
    leftSpin,
    rightSpins,
    ampDim,
    rightPolarization,
    Sequence @@ FilterRules[{opts}, Options[CompareGeneralSewingToCFBlocks]]
  ];
  If[! AssociationQ[comparison] || ! TrueQ[Lookup[comparison, "CompleteQ", False]],
    Message[
      ConstructSewingRelativeChiralBasis::cfcheck,
      Lookup[Lookup[comparison, "CFMatrix", <|"Rank" -> Missing["Unavailable"]|>], "Rank", Missing["Unavailable"]],
      Lookup[Lookup[comparison, "SewingMatrix", <|"Rank" -> Missing["Unavailable"]|>], "Rank", Missing["Unavailable"]],
      Lookup[Lookup[comparison, "JoinedMatrix", <|"Rank" -> Missing["Unavailable"]|>], "Rank", Missing["Unavailable"]]
    ];
    Return[$Failed]
  ];
  records = Lookup[comparison, "SewingRecords", $Failed];
  If[! ListQ[records], Return[$Failed]];
  sorted = SewingSortRecordsByChiralOrder[records];
  If[sorted === $Failed,
    Message[ConstructSewingRelativeChiralBasis::sort];
    Return[$Failed]
  ];
  block = SewingIndependentBlockFromRecords[
    sorted,
    comparison["Monomials"],
    ReturnRecords -> True,
    SewingOutputForm -> "SymbolForm"
  ];
  If[! AssociationQ[block], Return[$Failed]];
  selected = block["Records"];
  outputAmp[rec_Association] := Module[{amp = SewingRecordSymbolForm[rec], replaced},
    If[! TrueQ[OptionValue[ReplaceQInFinalSymbolForm]], Return[amp]];
    replaced = SewingReplaceQInSymbolForm[amp, OptionValue[QReplacement]];
    If[replaced === $Failed, amp, replaced]
  ];
  ampsByOrder = Association @ KeyValueMap[
    #1 -> (outputAmp /@ #2) &,
    GroupBy[selected, SewingRelativeChiralOrder]
  ];
  cfRank = comparison["CFMatrix"]["Rank"];
  sewingRank = comparison["SewingMatrix"]["Rank"];
  joinedRank = comparison["JoinedMatrix"]["Rank"];
  selectedCount = Length[selected];
  selectedRank = If[Lookup[block, "Matrix", {}] === {}, 0, MatrixRank[block["Matrix"]]];
  outputCount = Total[Length /@ Values[ampsByOrder]];
  SewingLog[
    debug,
    "RelativeChiralBasis.Counts",
    <|
      "CFRank" -> cfRank,
      "SewingRank" -> sewingRank,
      "JoinedRank" -> joinedRank,
      "SelectedCount" -> selectedCount,
      "SelectedRank" -> selectedRank,
      "OutputCount" -> outputCount
    |>
  ];
  If[
    ! (cfRank == sewingRank == joinedRank == selectedCount == selectedRank == outputCount),
    Message[
      ConstructSewingRelativeChiralBasis::count,
      ToString[
        <|
          "CFRank" -> cfRank,
          "SewingRank" -> sewingRank,
          "JoinedRank" -> joinedRank,
          "SelectedCount" -> selectedCount,
          "SelectedRank" -> selectedRank,
          "OutputCount" -> outputCount
        |>,
        InputForm
      ]
    ];
    Return[$Failed]
  ];
  KeySort[ampsByOrder]
];
