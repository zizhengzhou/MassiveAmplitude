If[!TrueQ[$HBPTestLoaded],
  If[!StringQ[$HBPTestCodeRoot],
    $HBPTestCodeRoot = DirectoryName[DirectoryName[$InputFileName]]
  ];
  If[!StringQ[$HBPTestLogRoot],
    $HBPTestLogRoot = FileNameJoin[{$HBPTestCodeRoot, "logs"}]
  ];
  SetDirectory[$HBPTestCodeRoot];
  Get[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]];
  Get[FileNameJoin[{$HBPTestCodeRoot, "SoftHeavyFactorization.executable.m"}]];
  $HBPTestLoaded = True;
];

ClearAll[ValidSewingRightRecordQ];
ValidSewingRightRecordQ[rec_Association] := Module[
  {yt, nt, angular, square},
  yt = rec["YTData"];
  nt = rec["SplitColumn"];
  angular = Table[yt[[All, c]], {c, nt}];
  square = Flatten@Table[yt[[r, c]], {r, 2}, {c, nt + 1, Length[yt[[1]]]}];
  And[
    FreeQ[Flatten[angular], 6],
    FreeQ[angular, {1, J} | {J, 1} | {2, J} | {J, 2}],
    And @@ ((FreeQ[#, J] || Length[Intersection[#, {3, 4}]] == 1) & /@ angular),
    FreeQ[square, 1 | 2]
  ]
];

VerificationTest[
  Length /@ ((ConstructLeft3PointOpenBasis[#] &) /@ {0, 1, 2}),
  {2, 4, 4},
  TestID -> "sewing-left-open-basis-counts"
]

VerificationTest[
  Module[{basis = ConstructLeft3PointOpenBasis[2]},
    {
      Length[basis],
      DeleteDuplicates[Lookup[basis, "QComponent"]],
      DeleteDuplicates[Lookup[basis, "ClosedPowers"]],
      And @@ (! FreeQ[#, ab[Q, J] sb[Q, J]] & /@ Lookup[basis, "AmpL"])
    }
  ],
  {
    4,
    {{}},
    {<|"Xhard" -> 0, "Xsoft" -> 0|>},
    True
  },
  TestID -> "sewing-left-open-basis-keeps-Q-unexpanded"
]

VerificationTest[
  Module[{records3, records4, qRecords, b3LikeQ},
    records3 = ConstructSewingAmplitudeRecords[2, 3];
    records4 = ConstructSewingAmplitudeRecords[2, 4];
    b3LikeQ = <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 0, "Square2" -> 1|>;
    qRecords = Select[records4, #["J"] == 2 && #["OpenPowers"] == b3LikeQ &];
    {
      Length[records3],
      Length[records4],
      Sort[Lookup[records3, "OpenPowers"]],
      Sort[Lookup[records4, "OpenPowers"]],
      Length[qRecords],
      DeleteDuplicates[Lookup[qRecords, "YT"]],
      DeleteDuplicates[Lookup[qRecords, "QComponent"]],
      DeleteDuplicates[Lookup[qRecords, "QReplacement"]],
      And @@ (ValidSewingRightRecordQ /@ Join[records3, records4])
    }
  ],
  {
    2,
    3,
    {
      <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 1, "Square2" -> 0|>,
      <|"Angle1" -> 1, "Square1" -> 0, "Angle2" -> 0, "Square2" -> 1|>
    },
    {
      <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 0, "Square2" -> 1|>,
      <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 0, "Square2" -> 1|>,
      <|"Angle1" -> 1, "Square1" -> 0, "Angle2" -> 1, "Square2" -> 0|>
    },
    1,
    {"J|JJJ;4|446"},
    {{"Q2"}},
    {2},
    True
  },
  TestID -> "sewing-records-3col-4col-and-ssyt-filters"
]

VerificationTest[
  Length /@ (ConstructLeft3PointOpenBasis[#, MassiveSpin -> 3/2] & /@ Range[0, 5]),
  {4, 12, 18, 16, 16, 16},
  TestID -> "left-open-basis-spin-three-half-counts"
]

VerificationTest[
  Module[{byJ = ConstructLeft3PointOpenBasis[#, MassiveSpin -> 3/2] & /@ Range[0, 5]},
    DeleteDuplicates /@ (Lookup[#, "ClosedSlots"] & /@ byJ)
  ],
  {{3}, {2}, {1}, {0}, {0}, {0}},
  TestID -> "left-open-basis-spin-three-half-closed-slots"
]

VerificationTest[
  Module[{leftRecords, left, targets, comparison, key, oldKeys, directKeys, auxKeys},
    key[rec_] := {rec["YT"], rec["SplitColumn"], ToString[rec["AmpR"], InputForm]};
    leftRecords = SewingApplyLeftQReplacement[#, {1, 2}] & /@ ConstructLeft3PointOpenBasis[1];
    left = SelectFirst[
      leftRecords,
      #["OpenPowers"] === <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 1, "Square2" -> 0|> &
    ];
    targets = SewingTargetCounts[left, 3];
    comparison = CompareRightResidualBackends[First[targets], 3];
    oldKeys = Sort[key /@ ConstructRightResidualSSYT[left, 3]];
    directKeys = Sort[key /@ comparison["DirectRecords"]];
    auxKeys = Sort[DeleteDuplicates[key /@ comparison["AuxiliaryRecords"]]];
    {
      comparison["EquivalentQ"],
      comparison["DirectKeyCount"],
      comparison["AuxiliaryKeyCount"],
      oldKeys === directKeys,
      directKeys === auxKeys,
      comparison["OnlyDirect"],
      comparison["OnlyAuxiliary"]
    }
  ],
  {True, 1, 1, True, True, {}, {}},
  TestID -> "right-residual-direct-auxiliary-equivalence-3col"
]

VerificationTest[
  Module[{leftRecords, left, targets, comparison, key, oldKeys, directKeys, auxKeys},
    key[rec_] := {rec["YT"], rec["SplitColumn"], ToString[rec["AmpR"], InputForm]};
    leftRecords = SewingApplyLeftQReplacement[#, 1] & /@ ConstructLeft3PointOpenBasis[2];
    left = SelectFirst[
      leftRecords,
      #["OpenPowers"] === <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 0, "Square2" -> 1|> &
    ];
    targets = SewingTargetCounts[left, 4];
    comparison = CompareRightResidualBackends[First[targets], 4];
    oldKeys = Sort[key /@ ConstructRightResidualSSYT[left, 4]];
    directKeys = Sort[key /@ comparison["DirectRecords"]];
    auxKeys = Sort[DeleteDuplicates[key /@ comparison["AuxiliaryRecords"]]];
    {
      comparison["EquivalentQ"],
      comparison["DirectKeyCount"],
      comparison["AuxiliaryKeyCount"],
      oldKeys === directKeys,
      directKeys === auxKeys,
      DeleteDuplicates[Lookup[comparison["AuxiliaryRecords"], "YT"]],
      comparison["OnlyDirect"],
      comparison["OnlyAuxiliary"]
    }
  ],
  {True, 1, 1, True, True, {"J|JJJ;4|446"}, {}, {}},
  TestID -> "right-residual-direct-auxiliary-equivalence-4col"
]

VerificationTest[
  {
    SewingAuxiliaryAmpToFormalJ[ab[1, 3] sb[2, 4]],
    SewingAuxiliaryAmpToFormalJ[ab[1, 2] sb[3, 4]],
    SewingAuxiliaryAmpToFormalJ[ab[1, 3] sb[1, 2]],
    SewingAuxiliaryAmpToFormalJ[ab[3, 4] sb[2, 6]]
  },
  {
    ab[3, J] sb[4, J],
    $Failed,
    $Failed,
    -ab[3, 4] sb[6, J]
  },
  TestID -> "auxiliary-amp-filter-replaces-single-aux-and-rejects-aux-pairs"
]

VerificationTest[
  Module[{leftRecords, left, target, comparison},
    leftRecords = SewingApplyLeftQReplacement[#, 1] & /@ ConstructLeft3PointOpenBasis[2];
    left = SelectFirst[
      leftRecords,
      #["OpenPowers"] === <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 0, "Square2" -> 1|> &
    ];
    target = First[SewingTargetCounts[left, 4]];
    comparison = CompareRightAuxiliaryOnShellToDirectJ[
      target,
      4,
      AuxiliarySpinRange -> Range[-3, 3]/2
    ];
    {
      comparison["EquivalentQ"],
      comparison["DirectKeyCount"],
      comparison["AuxiliaryKeyCount"],
      Sort[DeleteDuplicates[Lookup[comparison["AuxiliaryRecords"], "AuxiliarySpin"]]]
    }
  ],
  {True, 1, 1, {{1/2, 1/2}}},
  TestID -> "balanced-auxiliary-onshell-matches-direct-4col"
]

ClearAll[AuxOnShellFormalKey, AuxOnShellKeySet];
AuxOnShellFormalKey[rec_Association] := ToString[Expand[rec["AmpR"]], InputForm];
AuxOnShellKeySet[records_List] := Sort[DeleteDuplicates[AuxOnShellFormalKey /@ records]];

VerificationTest[
  Module[{balanced, all},
    balanced = ConstructRightAuxiliaryOnShellRecords[
      {1, 1, 1},
      4,
      RightAntispinor -> {1, 0, 0},
      AuxiliarySpinRange -> Range[-4, 4]/2,
      EqualAuxiliarySpin -> True,
      mass -> {3}
    ];
    all = ConstructRightAuxiliaryOnShellRecords[
      {1, 1, 1},
      4,
      RightAntispinor -> {1, 0, 0},
      AuxiliarySpinRange -> Range[-4, 4]/2,
      EqualAuxiliarySpin -> False,
      mass -> {3}
    ];
    {
      Length[balanced] > 0,
      Complement[AuxOnShellKeySet[balanced], AuxOnShellKeySet[all]] === {},
      Length[AuxOnShellKeySet[balanced]],
      Sort[DeleteDuplicates[Lookup[balanced, "AuxiliarySpin"]]]
    }
  ],
  {True, True, 10, {{0, 0}}},
  TestID -> "five-point-balanced-auxiliary-subset-unrestricted-4col"
]

VerificationTest[
  Module[{balanced, all},
    balanced = ConstructRightAuxiliaryOnShellRecords[
      {1, 1, 1},
      5,
      RightAntispinor -> {1, 0, 0},
      AuxiliarySpinRange -> Range[-4, 4]/2,
      EqualAuxiliarySpin -> True,
      mass -> {3}
    ];
    all = ConstructRightAuxiliaryOnShellRecords[
      {1, 1, 1},
      5,
      RightAntispinor -> {1, 0, 0},
      AuxiliarySpinRange -> Range[-4, 4]/2,
      EqualAuxiliarySpin -> False,
      mass -> {3}
    ];
    {
      Length[balanced] > 0,
      Complement[AuxOnShellKeySet[balanced], AuxOnShellKeySet[all]] === {},
      Length[AuxOnShellKeySet[balanced]],
      Sort[DeleteDuplicates[Lookup[balanced, "AuxiliarySpin"]]]
    }
  ],
  {True, True, 60, {{-1/2, -1/2}, {1/2, 1/2}}},
  TestID -> "five-point-balanced-auxiliary-subset-unrestricted-5col-spin111"
]

VerificationTest[
  Module[{balanced, all},
    balanced = ConstructRightAuxiliaryOnShellRecords[
      {1, 1, 0},
      5,
      RightAntispinor -> {1, 0, 0},
      AuxiliarySpinRange -> Range[-4, 4]/2,
      EqualAuxiliarySpin -> True,
      mass -> {3}
    ];
    all = ConstructRightAuxiliaryOnShellRecords[
      {1, 1, 0},
      5,
      RightAntispinor -> {1, 0, 0},
      AuxiliarySpinRange -> Range[-4, 4]/2,
      EqualAuxiliarySpin -> False,
      mass -> {3}
    ];
    {
      Length[balanced] > 0,
      Complement[AuxOnShellKeySet[balanced], AuxOnShellKeySet[all]] === {},
      Length[AuxOnShellKeySet[balanced]],
      Sort[DeleteDuplicates[Lookup[balanced, "AuxiliarySpin"]]]
    }
  ],
  {True, True, 96, {{0, 0}, {1, 1}}},
  TestID -> "five-point-balanced-auxiliary-subset-unrestricted-5col-spin110"
]

VerificationTest[
  Module[{raw, filtered, pairs, np = 4},
    pairs[amp_] := Sort /@ (List @@@ Cases[Prod2List[Expand[amp]], _ab | _sb]);
    raw = ConstructRightAuxiliaryOnShellRecords[
      {1, 0},
      4,
      RightAntispinor -> {1, 0},
      CodeDim -> SewingCodeDimFromAmpDim[4, 4],
      mass -> {0, 0, 1, 0},
      AuxiliarySpinRange -> SewingAutomaticAuxiliarySpinRange[4],
      EqualAuxiliarySpin -> True,
      RejectMasslessSelfColumns -> False
    ];
    filtered = ConstructRightAuxiliaryOnShellRecords[
      {1, 0},
      4,
      RightAntispinor -> {1, 0},
      CodeDim -> SewingCodeDimFromAmpDim[4, 4],
      mass -> {0, 0, 1, 0},
      AuxiliarySpinRange -> SewingAutomaticAuxiliarySpinRange[4],
      EqualAuxiliarySpin -> True,
      RejectMasslessSelfColumns -> True
    ];
    {
      Length[raw] > Length[filtered],
      AllTrue[filtered[[All, "AuxiliaryAmp"]], SewingMasslessSelfColumnFreeQ[#, np] &],
      AnyTrue[raw[[All, "AuxiliaryAmp"]], ! SewingMasslessSelfColumnFreeQ[#, np] &]
    }
  ],
  {True, True, True},
  TestID -> "auxiliary-onshell-rejects-massless-self-columns"
]

VerificationTest[
  Module[{comparison},
    ClearCache[];
    comparison = CompareSewingToCFBlocks[{7, 8}];
    {
      Lookup[comparison, "CodeDim"],
      Lookup[Lookup[comparison, "CFMatrix"], "Rank"],
      Lookup[Lookup[comparison, "SewingMatrix"], "Rank"],
      Lookup[Lookup[comparison, "JoinedMatrix"], "Rank"],
      Lookup[comparison, "CompleteQ"]
    }
  ],
  {
    {7, 8},
    {2, 3},
    {2, 3},
    {2, 3},
    {True, True}
  },
  TestID -> "sewing-cf-block-rank-completeness-ampdim-3-4"
]

VerificationTest[
  Module[{comparison},
    ClearCache[];
    comparison = CompareGeneralSewingToCFBlocks[1/2, {1, 1}, {3}, 4, {1, 0}, JMax -> 2];
    {
      comparison["CodeDim"],
      comparison["Mass"],
      comparison["CFMatrix"]["Rank"],
      comparison["SewingMatrix"]["Rank"],
      comparison["JoinedMatrix"]["Rank"],
      comparison["CompleteQ"],
      Length[comparison["SewingRecords"]]
    }
  ],
  {8, {1, 2, 3}, 3, 3, 3, True, 6},
  TestID -> "general-sewing-four-point-strict-cf-rank-complete"
]

VerificationTest[
  Module[{comparison},
    ClearCache[];
    comparison = CompareGeneralSewingToCFBlocks[1, {1, 1}, {3}, 5, {1, 0}, JMax -> 3];
    {
      comparison["CodeDim"],
      comparison["Mass"],
      comparison["CFMatrix"]["Rank"],
      comparison["SewingMatrix"]["Rank"],
      comparison["JoinedMatrix"]["Rank"],
      comparison["CompleteQ"],
      Length[comparison["CFRecords"]],
      Length[comparison["SewingRecords"]]
    }
  ],
  {9, {1, 2, 3}, 7, 7, 7, True, 7, 15},
  TestID -> "general-sewing-spin-one-closed-polynomial-q-replacement"
]

VerificationTest[
  Module[{summarize},
    ClearCache[];
    summarize[q_] := Module[{comparison},
      comparison = CompareGeneralSewingToCFBlocks[
        1/2, {1, 1}, {3}, 4, {1, 0}, JMax -> 2, QReplacement -> q
      ];
      {
        Length[comparison["CFRecords"]],
        Length[comparison["SewingRecords"]],
        comparison["CFMatrix"]["Rank"],
        comparison["SewingMatrix"]["Rank"],
        comparison["JoinedMatrix"]["Rank"],
        comparison["CompleteQ"],
        DeleteDuplicates[Lookup[comparison["SewingRecords"], "QReplacement"]]
      }
    ];
    {summarize[1], summarize[2], summarize[{1, 2}]}
  ],
  {
    {3, 6, 3, 3, 3, True, {1}},
    {3, 6, 3, 3, 3, True, {2}},
    {3, 6, 3, 3, 3, True, {{1, 2}}}
  },
  TestID -> "general-sewing-Q-replacement-single-vs-sum"
]

VerificationTest[
  Module[{block},
    ClearCache[];
    block = ConstructIndepSewingBlock[1/2, {1, 1}, {3}, 3, {1, 0}, JMax -> 2, CheckAgainstCF -> True];
    {
      Length[block],
      Length[block[[1]]],
      Dimensions[block[[2]]],
      Length[block[[3]]]
    }
  ],
  {3, 2, {2, 2}, 2},
  TestID -> "construct-indep-sewing-block-cf-style-output"
]

VerificationTest[
  Module[{block},
    ClearCache[];
    block = ConstructIndepSewingBlock[
      1/2, {1, 1}, {3}, 4, {1, 0},
      JMax -> 2,
      QReplacement -> {1, 2},
      CheckAgainstCF -> True
    ];
    {Length[block], Length[block[[1]]], Dimensions[block[[2]]], Length[block[[3]]]}
  ],
  {3, 3, {3, 3}, 3},
  TestID -> "construct-indep-sewing-block-cf-check-passes-for-q-sum"
]

VerificationTest[
  Module[{records},
    ClearCache[];
    records = ConstructGeneralSewingAmplitudeRecords[
      1/2, {1, 1}, {3}, 3, {1, 0},
      JMax -> 2,
      Check3Point -> True,
      CheckRight -> True,
      CheckSewing -> True
    ];
    {ListQ[records], Length[records]}
  ],
  {True, 2},
  TestID -> "general-sewing-checks-pass-for-complete-four-point-case"
]

VerificationTest[
  Module[{records},
    ClearCache[];
    records = ConstructGeneralSewingAmplitudeRecords[
      1/2, {1, 0}, {3}, 4, {1, 0},
      JMax -> 2,
      CheckSewing -> True
    ];
    {ListQ[records], Length[records], AllTrue[records, Expand[#ReducedAmp] =!= 0 &]}
  ],
  {True, 10, True},
  TestID -> "general-sewing-checks-filter-zero-reduced-scalar-rows"
]

VerificationTest[
  Module[{comparison},
    ClearCache[];
    comparison = Quiet[
      CompareGeneralSewingToCFBlocks[
        1/2, {1, 0}, {3}, 4, {1, 0},
        JMax -> 2,
        CheckSewing -> True
      ],
      ConstructGeneralSewingAmplitudeRecords::check
    ];
    {
      AssociationQ[comparison],
      Lookup[comparison, "Error", Missing["Error"]],
      Lookup[comparison, "CompleteQ", Missing["CompleteQ"]],
      If[ListQ[Lookup[comparison, "SewingRecords", {}]], Length[comparison["SewingRecords"]], Lookup[comparison, "SewingRecords", Missing["SewingRecords"]]],
      Lookup[Lookup[comparison, "CFMatrix", <||>], "Rank", Missing["CFRank"]],
      Lookup[Lookup[comparison, "SewingMatrix", <||>], "Rank", Missing["SewingRank"]],
      Lookup[Lookup[comparison, "JoinedMatrix", <||>], "Rank", Missing["JoinedRank"]]
    }
  ],
  {
    True,
    Missing["Error"],
    True,
    10,
    4,
    4,
    4
  },
  TestID -> "general-sewing-comparison-completes-after-physical-filter"
]

VerificationTest[
  Module[{records, bad, check},
    ClearCache[];
    records = ConstructGeneralSewingAmplitudeRecords[
      1/2, {1, 0}, {3}, 4, {1, 0},
      JMax -> 2,
      FilterPhysicalSector -> False
    ];
    bad = SelectFirst[records, #["J"] === 2 &];
    check = SewingSewnRecordCheck[
      bad,
      {1, 2, 3},
      Flatten[Table[{a, b, 1, 0}, {a, 0, 1}, {b, 0, 1}], 1]
    ];
    {
      Lookup[check, "ValidQ"],
      MemberQ[Lookup[check, "Issues"][[All, "Check"]], "Sewing.Amp2MetaInfo.Spins"]
    }
  ],
  {False, True},
  TestID -> "general-sewing-checks-reject-wrong-spin-meta"
]

VerificationTest[
  Module[{block},
    ClearCache[];
    block = Quiet[
      ConstructIndepSewingBlock[
        1/2, {1, 0}, {3}, 4, {1, 0},
        JMax -> 2,
        CheckAgainstCF -> True
      ],
      {ConstructIndepSewingBlock::cfcheck, ConstructIndepSewingBlock::indcheck}
    ];
    {Length[block], Length[block[[1]]], Dimensions[block[[2]]], Length[block[[3]]]}
  ],
  {3, 4, {4, 4}, 4},
  TestID -> "construct-indep-sewing-block-cf-check-passes-for-scalar"
]

VerificationTest[
  Module[{records, comparison},
    ClearCache[];
    records = ConstructGeneralSewingAmplitudeRecords[1/2, {1, 1, 1}, {3}, 4, {1, 0, 0}, JMax -> 2];
    comparison = CompareGeneralSewingToCFBlocks[1/2, {1, 1, 1}, {3}, 4, {1, 0, 0}, JMax -> 2];
    {
      FreeQ[records, $Failed],
      Length[records],
      Length[comparison["CFRecords"]],
      Length[comparison["SewingRecords"]],
      DeleteDuplicates[Lookup[records, "J"]],
      DeleteDuplicates[Lookup[records, "LeftDegreeData"]],
      DeleteDuplicates[Lookup[records, "RightAmpDim"]],
      DeleteDuplicates[Lookup[records, "LeftRecord"][[All, "LeftSquareRelabelRule"]]],
      AllTrue[records, SewingBracketDegree[#["TotalAmp"]] === {4} &],
      AllTrue[records, #["RightAmpDim"] == 4 - #["LeftDegreeData"]["NonJ"] &],
      AllTrue[
        Flatten[Lookup[comparison["SewingRecords"], "MetaTerms"], 1],
        MemberQ[comparison["CFPolarizations"], #[[2]]] &
      ],
      comparison["CFMatrix"]["Rank"],
      comparison["SewingMatrix"]["Rank"],
      comparison["JoinedMatrix"]["Rank"],
      comparison["CompleteQ"],
      Dimensions[comparison["CFMatrix"]["Matrix"]],
      Dimensions[comparison["SewingMatrix"]["Matrix"]],
      Dimensions[comparison["JoinedMatrix"]["Matrix"]]
    }
  ],
  {
    True, 4, 4, 4,
    {1},
    {<|"NonJ" -> 0, "J" -> 2, "Total" -> 2|>},
    {4},
    {{8 -> 10, 7 -> 9}},
    True, True, True,
    4, 4, 4, True,
    {4, 6}, {4, 6}, {8, 6}
  },
  TestID -> "general-sewing-five-point-cf-rank-completeness"
]
