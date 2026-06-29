Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, totalCount];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];

result = ConstructProjectedSewingRelativeChiralBasis[
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

If[! AssociationQ[result],
  fail["projected right-sector deduplication case should return data", result]
];

basis = Flatten[Values[result["BasisByRelativeChiralOrder"]], 1];

If[Length[basis] =!= Length[DeleteDuplicates[basis]],
  fail["projected output should not duplicate basis elements across left-heavy polarizations", result["BasisByRelativeChiralOrder"]]
];

If[Length[result["RightPolarizationGroups"]] =!= 1,
  fail["right polarization filter should produce one right-sector group", result["RightPolarizationGroups"]]
];

If[Length[First[result["RightPolarizationGroups"]]] =!= 4,
  fail["one right-sector group should retain all four left-heavy polarization witnesses", result["RightPolarizationGroups"]]
];

If[Lookup[result["SectorResults"], "RightPolarization", {}] =!= {{1, 0}},
  fail["sector results should be keyed by right-side polarization only", Lookup[result["SectorResults"], "RightPolarization", {}]]
];

indep = ConstructIndepSewingBlock[
  1/2,
  {1, 1},
  {3},
  4,
  {1, 0},
  CheckAgainstCF -> True,
  ReturnRecords -> True,
  SewingOutputForm -> "SymbolForm"
];

If[! AssociationQ[indep],
  fail["fixed-right-polarization sewing block should be independently constructible", indep]
];

If[Length[indep["Records"]] =!= totalCount[result["BasisByRelativeChiralOrder"]],
  fail[
    "projected no-identical right-sector output should match fixed-right-polarization sewing block count",
    <|"Projected" -> result["BasisByRelativeChiralOrder"], "IndependentBlockCount" -> Length[indep["Records"]]|>
  ]
];

Print["projected right-sector dedup regression ok counts=", InputForm[Length /@ result["BasisByRelativeChiralOrder"]]];
