Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[fail, totalCount];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];

plain = ConstructProjectedSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {},
  ReturnProjectionData -> True,
  SewingDebug -> False
];

If[! AssociationQ[plain], fail["projected constructor should return association data", plain]];
If[! KeyExistsQ[plain, "BasisByRelativeChiralOrder"], fail["missing grouped basis", plain]];
If[totalCount[plain["BasisByRelativeChiralOrder"]] != 4,
  fail["no-identical projected constructor should match the full-polarization CF survivor count", plain["BasisByRelativeChiralOrder"]]
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
