Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, qSymbolQ, auxiliaryLeakQ, j0ClosedQRows];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

qSymbolQ[expr_] := ! FreeQ[
  expr,
  s_Symbol /; SymbolName[Unevaluated[s]] === "Q"
];

auxiliaryLeakQ[expr_] := ! FreeQ[
  expr,
  f : (_ab | _sb) /; ! FreeQ[List @@ f, 1 | 2]
];

ClearCache[];
records = ConstructGeneralSewingAmplitudeRecords[
  1/2,
  {1, 1},
  {3},
  4,
  {1, 0},
  Check3Point -> True,
  CheckRight -> True
];

If[! ListQ[records] || Length[records] == 0,
  fail["BBuf sewing records should be nonempty", records]
];

If[AnyTrue[Lookup[records, "AmpR"], qSymbolQ],
  fail["right residual AmpR must not contain formal Q", Select[records, qSymbolQ[#["AmpR"]] &]]
];

j0ClosedQRows = Select[
  records,
  #["J"] === 0 &&
    Lookup[#["SortData"], "Xhard", 0] + Lookup[#["SortData"], "Xsoft", 0] == 1 &&
    qSymbolQ[#["AmpLSymbolForm"]] &&
    ! qSymbolQ[#["AmpR"]] &&
    qSymbolQ[#["SewingSymForm"]] &
];

If[Length[j0ClosedQRows] =!= 0,
  fail["closed J=0 Xhard/Xsoft rows should not acquire an extra Q pair", j0ClosedQRows]
];

If[AnyTrue[Lookup[records, "AmpR"], auxiliaryLeakQ],
  fail["right residual should not leak auxiliary labels 1 or 2", Lookup[records, "AmpR"]]
];

basisData = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {},
  su3ShapeList -> {},
  RightPolarizationFilter -> <|3 -> 1|>,
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
];

If[! AssociationQ[basisData],
  fail["projected BBuf filtered case should return projection data", basisData]
];

flatBasis = Flatten[Values[basisData["BasisByRelativeChiralOrder"]], 1];
If[
  AnyTrue[
    flatBasis,
    MatchQ[
      #,
      Xhard*ab[2, 3]*sb[2, 4]*sb[4, 6] |
        Xsoft*ab[2, 3]*sb[2, 4]*sb[4, 6] |
        Xhard*ab[3, Q]*sb[4, 6]*sb[4, Q] |
        Xsoft*ab[3, Q]*sb[4, 6]*sb[4, Q]
    ] &
  ],
  fail["projected output should not contain closed J=0 auxiliary or Q-pair rows", flatBasis]
];

If[
  ! KeyExistsQ[basisData["BasisByRelativeChiralOrder"], 2] ||
    ! KeyExistsQ[basisData["BasisByRelativeChiralOrder"], 3],
  fail["projected output should contain the corrected open J=2 and J=1 orders", basisData["BasisByRelativeChiralOrder"]]
];

Print["bbuf right residual no-Q regression ok"];
