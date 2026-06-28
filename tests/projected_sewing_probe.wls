Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, totalCount, legacyCount];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];
legacyCount[leftSpin_, rightSpins_List, rightMass_List, ampDim_Integer, identical_List] := Module[
  {spins = Join[{leftSpin, leftSpin}, rightSpins], fullMass, basis},
  fullMass = MassOption[Join[{1, 2}, rightMass], Length[spins]];
  basis = Quiet @ Check[
    Block[{Print = (Null &)},
      MassiveBasis`Private`ConstructGeneralBasis[spins, ampDim, identical, mass -> fullMass]
    ],
    $Failed
  ];
  If[ListQ[basis], Length[basis], $Failed]
];

plain = ConstructProjectedSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {},
  ReturnProjectionData -> True,
  SewingDebug -> False
];

If[! AssociationQ[plain], fail["projected constructor should return association data", plain]];
If[! KeyExistsQ[plain, "BasisByRelativeChiralOrder"], fail["missing grouped basis", plain]];
plainLegacyCount = legacyCount[1/2, {1, 1}, {3}, 4, {}];
If[
  ! IntegerQ[plainLegacyCount] ||
    totalCount[plain["BasisByRelativeChiralOrder"]] =!= plainLegacyCount,
  fail[
    "no-identical projected constructor should match ConstructGeneralBasis at the same ampDim",
    <|"Projected" -> plain["BasisByRelativeChiralOrder"], "LegacyCount" -> plainLegacyCount|>
  ]
];

identical = ConstructProjectedSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {{3, 4}},
  ReturnProjectionData -> True,
  SewingDebug -> False
];

If[! AssociationQ[identical], fail["identical projected constructor should return association data", identical]];
If[! AllTrue[
    Flatten[Lookup[identical["SectorResults"], "JBlockDiagnostics", <||>] /. a_Association :> Values[a], Infinity],
    ! AssociationQ[#] || And @@ Cases[#, Rule[_, value_] :> TrueQ[value], Infinity] &
  ],
  fail["Lorentz permutation diagnostics should be block diagonal by J", identical["SectorResults"]]
];
If[! AllTrue[
    Lookup[Lookup[identical["SectorResults"], "TotalJBlockDiagnostics", <||>], "TotalYoungOperatorBlockDiagonalByJ", True],
    TrueQ
  ],
  fail["total Young operators should be block diagonal by J", identical["SectorResults"]]
];

Print["projected sewing probe ok"];
