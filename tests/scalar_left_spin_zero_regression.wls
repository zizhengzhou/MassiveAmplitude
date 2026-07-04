Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, symbolNameQ, qJFactorQ, massCasesFor, compareScalarZeroCase];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

symbolNameQ[name_String][expr_] := MatchQ[expr, _Symbol] && SymbolName[Unevaluated[expr]] === name;

qJFactorQ[head_][factor_] := MatchQ[factor, _ab | _sb] &&
  Head[factor] === head &&
  AnyTrue[List @@ factor, symbolNameQ["Q"]] &&
  AnyTrue[List @@ factor, symbolNameQ["J"]];

Do[
  records = ConstructLeft3PointOpenBasis[
    j,
    MassiveSpin -> 0,
    PointCount -> 4,
    QReplacement -> Automatic
  ];
  If[! ListQ[records] || Length[records] =!= 1,
    fail["s=0 left current should produce one record for each J", <|"J" -> j, "Records" -> records|>]
  ];
  record = First[records];
  form = record["AmpLSymbolForm"];
  factors = Prod2List[form];
  If[Lookup[record["SortData"], "Xhard", Missing[]] =!= 0 ||
      Lookup[record["SortData"], "Xsoft", Missing[]] =!= 0,
    fail["s=0 left current should not carry Xhard/Xsoft powers", record["SortData"]]
  ];
  If[j == 0,
    If[form =!= 1, fail["s=0,J=0 left current should be 1", form]],
    If[
      Count[factors, _?(qJFactorQ[ab])] =!= j ||
        Count[factors, _?(qJFactorQ[sb])] =!= j ||
        Length[factors] =!= 2 j,
      fail["s=0,J>0 left current should be a pure Q-J pair power", <|"J" -> j, "Form" -> form, "Factors" -> factors|>]
    ]
  ],
  {j, 0, 5}
];

If[SewingContractionTerms[1, 1] =!= {1},
  fail["constant left/right sewing should split to {1}", SewingContractionTerms[1, 1]]
];

If[SymmetricSewContract[1, 1] =!= 1,
  fail["constant left/right symmetric sewing should be 1", SymmetricSewContract[1, 1]]
];

If[Poly2Singlet[1] =!= {1},
  fail["constant reduced amplitudes should contribute monomial basis {1}", Poly2Singlet[1]]
];

meta = Check[Amp2MetaInfo[1, 4, mass -> {1, 2}], $Failed];
If[meta =!= {{0, 0, 0, 0}, {0, 0, 0, 0}},
  fail["constant amplitude metadata should be all-zero without messages", meta]
];

records = ConstructGeneralSewingAmplitudeRecords[
  0,
  {0, 0},
  {},
  0,
  {0, 0},
  JMax -> 0
];

If[! ListQ[records] || Length[records] =!= 1,
  fail["s=0 scalar identity general sewing should produce one record", records]
];

If[First[records]["TotalAmp"] =!= 1 || First[records]["ReducedAmp"] =!= 1,
  fail["s=0 scalar identity sewn record should be the constant amplitude", First[records]]
];

massCasesFor[rightCount_Integer] := Module[
  {labels = Range[3, 2 + rightCount], mixed},
  mixed = Select[labels, OddQ];
  DeleteDuplicates[{{}, labels, mixed}]
];

compareScalarZeroCase[rightCount_Integer, rightMass_List] := Module[
  {rightSpins, rightPolarization, comparison, projected, basisCount},
  rightSpins = ConstantArray[0, rightCount];
  rightPolarization = ConstantArray[0, rightCount];
  comparison = CompareGeneralSewingToCFBlocks[
    0,
    rightSpins,
    rightMass,
    0,
    rightPolarization,
    JMax -> 0
  ];
  If[
    ! AssociationQ[comparison] ||
      ! TrueQ[comparison["CompleteQ"]] ||
      {comparison["CFMatrix"]["Rank"], comparison["SewingMatrix"]["Rank"], comparison["JoinedMatrix"]["Rank"]} =!= {1, 1, 1},
    fail["s=0 scalar identity compare should have rank 1", <|"RightCount" -> rightCount, "RightMass" -> rightMass, "Comparison" -> comparison|>]
  ];
  projected = ConstructProjectedSewingRelativeChiralBasis[
    0,
    rightSpins,
    rightMass,
    0,
    {},
    su3ShapeList -> {},
    ReturnProjectionData -> True,
    JMax -> 0
  ];
  If[! AssociationQ[projected],
    fail["s=0 scalar identity projected calculation should return data", projected]
  ];
  basisCount = Total[Length /@ Values[projected["BasisByRelativeChiralOrder"]]];
  If[basisCount =!= 1 || projected["BasisByRelativeChiralOrder"] =!= <|0 -> {1}|>,
    fail["s=0 scalar identity projected basis should be exactly <|0 -> {1}|>", projected["BasisByRelativeChiralOrder"]]
  ];
];

Do[
  compareScalarZeroCase[rightCount, rightMass],
  {rightCount, Range[2, 5]},
  {rightMass, massCasesFor[rightCount]}
];

compareJ1 = CompareGeneralSewingToCFBlocks[
  0,
  {0, 0},
  {},
  2,
  {0, 0},
  JMax -> 1
];

If[
  ! AssociationQ[compareJ1] ||
    ! TrueQ[compareJ1["CompleteQ"]] ||
    {compareJ1["CFMatrix"]["Rank"], compareJ1["SewingMatrix"]["Rank"], compareJ1["JoinedMatrix"]["Rank"]} =!= {2, 2, 2} ||
    DeleteDuplicates[Lookup[compareJ1["SewingRecords"], "J", {}]] =!= {0, 1},
  fail["s=0 ampDim=2 should need and pass J=0,1 channels", compareJ1]
];

compareJ2 = CompareGeneralSewingToCFBlocks[
  0,
  {0, 0},
  {},
  4,
  {0, 0},
  JMax -> 2
];

If[
  ! AssociationQ[compareJ2] ||
    ! TrueQ[compareJ2["CompleteQ"]] ||
    {compareJ2["CFMatrix"]["Rank"], compareJ2["SewingMatrix"]["Rank"], compareJ2["JoinedMatrix"]["Rank"]} =!= {3, 3, 3} ||
    DeleteDuplicates[Lookup[compareJ2["SewingRecords"], "J", {}]] =!= {0, 1, 2},
  fail["s=0 ampDim=4 should need and pass J=0,1,2 channels", compareJ2]
];

Print["scalar left-spin-zero regression ok"];
