Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[
  fail, totalCount, zeroMatrixQ, normalizedProjectorQ, zeroOneSpectrumQ,
  massiveRuleRows, checkLorentzRepresentation, checkYoungOperator,
  checkSU3DirectProductSector
];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];

zeroMatrixQ[expr_] := Module[{expanded = Expand[expr]},
  If[ListQ[expanded],
    AllTrue[Flatten[expanded], TrueQ[# === 0] &],
    TrueQ[expanded === 0]
  ]
];

normalizedProjectorQ[matrix_] :=
  MatrixQ[matrix] && zeroMatrixQ[matrix . matrix - matrix];

zeroOneSpectrumQ[matrix_] := Module[{dims},
  If[! MatrixQ[matrix], Return[False]];
  dims = Dimensions[matrix];
  If[Length[dims] =!= 2 || dims[[1]] =!= dims[[2]], Return[False]];
  If[dims[[1]] > 12, Return[True]];
  AllTrue[Simplify /@ Eigenvalues[matrix], (# === 0 || # === 1) &]
];

massiveRuleRows[records_List, rule_, pointCount_Integer] := Module[
  {masslessLimitRule},
  masslessLimitRule = Table[2 pointCount + 1 - i -> i, {i, pointCount}];
  ReduceSt[pointCount] /@
    (ReplaceBraNumber[masslessLimitRule] /@
      (ReplaceBraNumber[rule] /@ (SewingRecordAmpForm /@ records)))
];

checkLorentzRepresentation[sector_Association] := Module[
  {
    records, coeffs, basis, pointCount, operatorDict, identicalInfo,
    operatorRuleEntries, matrixForRows, checkOneRule
  },
  If[Length[sector["IdenticalInfo"]] == 0, Return[Null]];
  records = sector["RecordsBeforeIdentical"];
  coeffs = sector["Matrix"];
  basis = sector["CFBasis"];
  pointCount = Length[sector["FullPolarizations"][[1]]];
  operatorDict = sector["LorentzOperatorDictionary"];
  identicalInfo = sector["IdenticalInfo"];
  matrixForRows[rows_] := Table[
    MassiveBasis`Private`SpinorMonomialCoefficient[row, monom],
    {row, rows}, {monom, basis}
  ];
  operatorRuleEntries[id_List] := Module[
    {rules = MassiveBasis`Private`GetMassiveIdenticalRules[id, pointCount], entries, ruleList},
    entries = Normal[Association[operatorDict[id]]];
    ruleList = Which[
      Length[rules] == 1, {{}},
      Length[rules] == 2, {{}, rules[[2]]},
      True, {{}, rules[[2]], rules[[3]]}
    ];
    If[Length[entries] =!= Length[ruleList],
      fail["Lorentz operator dictionary length should match massive identical rule length", <|"Id" -> id, "Entries" -> entries, "Rules" -> rules|>]
    ];
    MapThread[
      <|"Key" -> First[#1], "Matrix" -> Last[#1], "Rule" -> #2|> &,
      {entries, ruleList}
    ]
  ];
  checkOneRule[id_, entry_Association] := Module[
    {op = entry["Matrix"], opKey = entry["Key"], rule = entry["Rule"], targetRows, targetMatrix},
    If[Dimensions[op] =!= {Length[records], Length[records]},
      fail["Lorentz permutation operator has wrong dimensions", <|"Id" -> id, "Key" -> opKey, "Dimensions" -> Dimensions[op], "RecordCount" -> Length[records]|>]
    ];
    If[MatrixRank[op] =!= Length[records],
      fail["Lorentz permutation operator should be full rank", <|"Id" -> id, "Key" -> opKey, "Matrix" -> op|>]
    ];
    targetRows = massiveRuleRows[records, rule, pointCount];
    targetMatrix = matrixForRows[targetRows];
    If[! zeroMatrixQ[op . coeffs - targetMatrix],
      fail["Lorentz permutation representation does not match reduced permuted records", <|"Id" -> id, "Key" -> opKey|>]
    ];
  ];
  Do[
    Scan[checkOneRule[id, #] &, operatorRuleEntries[id]],
    {id, identicalInfo}
  ]
];

checkYoungOperator[operator_, expectedLength_Integer, label_] := Module[{dims},
  If[! MatrixQ[operator], fail["Young operator should be a matrix", label]];
  dims = Dimensions[operator];
  If[dims =!= {expectedLength, expectedLength},
    fail["Young operator dimension should match its basis", <|"Label" -> label, "Dimensions" -> dims, "Expected" -> expectedLength|>]
  ];
  If[! normalizedProjectorQ[operator],
    fail["Young operator should be normalized idempotent", <|"Label" -> label, "Operator" -> operator|>]
  ];
  If[! zeroOneSpectrumQ[operator],
    fail["Young operator should have 0/1 spectrum when checked explicitly", <|"Label" -> label, "Operator" -> operator|>]
  ];
];

checkSU3DirectProductSector[sector_Association] := Module[
  {lorentzBefore, colorCount, directCount, totalOperator, independentPositions},
  lorentzBefore = Length[sector["RecordsBeforeIdentical"]];
  colorCount = Length[sector["ColorData"]["SU3Basis"]];
  directCount = Length[sector["DirectProductItemsBeforeProjection"]];
  If[directCount =!= lorentzBefore colorCount,
    fail[
      "SU3 identical direct product should be built from Bsew before Lorentz-only projection",
      <|"DirectProductCount" -> directCount, "LorentzBeforeProjection" -> lorentzBefore, "ColorCount" -> colorCount|>
    ]
  ];
  totalOperator = sector["TotalYoungOperator"];
  checkYoungOperator[totalOperator, directCount, "total SU3 identical"];
  independentPositions = sector["DirectProductIndependentPositions"];
  If[Length[independentPositions] =!= MatrixRank[totalOperator],
    fail["projected SU3 direct-product count should equal total Young-operator rank", <|"Rank" -> MatrixRank[totalOperator], "Positions" -> independentPositions|>]
  ];
  If[Length[sector["ProjectedItems"]] =!= Length[independentPositions],
    fail["projected SU3 item count should match independent positions", <|"ProjectedItems" -> sector["ProjectedItems"], "Positions" -> independentPositions|>]
  ];
];

lorentzOnly = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3, 4},
  6,
  {{3, 4}},
  su3ShapeList -> {},
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
];

If[! AssociationQ[lorentzOnly], fail["Lorentz-only identical constructor failed", lorentzOnly]];
If[totalCount[lorentzOnly["BasisByRelativeChiralOrder"]] == 0,
  fail["Lorentz-only identical result should not be empty", lorentzOnly]
];

lorentzSectors = Select[lorentzOnly["SectorResults"], Length[#["IdenticalInfo"]] > 0 &];
If[Length[lorentzSectors] == 0, fail["expected at least one Lorentz identical sector", lorentzOnly]];
Scan[checkLorentzRepresentation, lorentzSectors];
Scan[checkYoungOperator[#["LorentzYoungOperator"], Length[#["RecordsBeforeIdentical"]], "Lorentz identical"] &, lorentzSectors];

su3Identical = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3, 4},
  6,
  {{3, 4}},
  su3ShapeList -> {"", "", "g", "g"},
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
];

If[! AssociationQ[su3Identical], fail["SU3 identical constructor failed", su3Identical]];
If[totalCount[su3Identical["BasisByRelativeChiralOrder"]] == 0,
  fail["SU3 identical result should not be empty", su3Identical]
];

su3Sectors = Select[
  su3Identical["SectorResults"],
  Length[#["IdenticalInfo"]] > 0 && TrueQ[#["ColorData"]["HasSU3"]] &
];
If[Length[su3Sectors] == 0, fail["expected at least one SU3 identical sector", su3Identical]];
If[! AnyTrue[su3Sectors, Length[#["RecordsBeforeIdentical"]] > Length[#["Records"]] &],
  fail["regression case should include a sector where Lorentz projection lowers the basis dimension", su3Sectors]
];
Scan[checkLorentzRepresentation, su3Sectors];
Scan[checkSU3DirectProductSector, su3Sectors];

Print["projected identical projection regression ok"];
