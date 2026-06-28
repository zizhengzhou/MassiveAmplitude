Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, totalCount, fullPolarizations, fullMassFromLabels, legacyCount];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];
fullPolarizations[data_Association, key_String] := data[key][[All, 2]];
fullMassFromLabels[np_Integer?Positive, labels_List] := MassOption[Join[{1, 2}, labels], np];
legacyCount[leftSpin_, rightSpins_List, rightMass_List, ampDim_Integer, identical_List] := Module[
  {spins = Join[{leftSpin, leftSpin}, rightSpins], fullMass, basis},
  fullMass = fullMassFromLabels[2 + Length[rightSpins], rightMass];
  basis = Quiet @ Check[
    Block[{Print = (Null &)},
      MassiveBasis`Private`ConstructGeneralBasis[spins, ampDim, identical, mass -> fullMass]
    ],
    $Failed
  ];
  If[ListQ[basis], Length[basis], $Failed]
];

plain = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1, 0},
  {3, 4},
  4,
  {{3, 4}},
  ReturnProjectionData -> True
];

filtered = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1, 0},
  {3, 4},
  4,
  {{3, 4}},
  RightPolarizationFilter -> <|3 -> 2|>,
  ReturnProjectionData -> True,
  SewingPerformanceTrace -> True
];

multiFiltered = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1, 0},
  {3, 4},
  4,
  {{3, 4}},
  RightPolarizationFilter -> <|3 -> {0, 1}, 5 -> All|>,
  ReturnProjectionData -> True
];

invalidKey = Quiet @ ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1, 0},
  {3, 4},
  4,
  {{3, 4}},
  RightPolarizationFilter -> <|2 -> 1|>
];

invalidValue = Quiet @ ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1, 0},
  {3, 4},
  4,
  {{3, 4}},
  RightPolarizationFilter -> <|3 -> "bad"|>
];

If[! AssociationQ[plain] || ! AssociationQ[filtered] || ! AssociationQ[multiFiltered],
  fail["right polarization filter cases should return projection data"]
];

baselineLegacyCount = legacyCount[1/2, {1, 1, 0}, {3, 4}, 4, {{3, 4}}];
If[
  ! IntegerQ[baselineLegacyCount] ||
    totalCount[plain["BasisByRelativeChiralOrder"]] =!= baselineLegacyCount,
  fail[
    "baseline target example should match ConstructGeneralBasis count at the same ampDim",
    <|"Projected" -> plain["BasisByRelativeChiralOrder"], "LegacyCount" -> baselineLegacyCount|>
  ]
];

If[! AllTrue[fullPolarizations[filtered, "PhysicalBlocks"], #[[3]] == 2 &],
  fail["physical blocks should satisfy particle-3 polarization filter after identical reduction", filtered["PhysicalBlocks"]]
];

If[Length[filtered["PhysicalBlocks"]] == 0,
  fail["nonempty particle-3 polarization filter should keep at least one physical block"]
];

If[Length[filtered["PhysicalBlocks"]] >= Length[filtered["UnfilteredPhysicalBlocks"]],
  fail["single-polarization filter should remove at least one identical-representative physical block"]
];

If[! AllTrue[fullPolarizations[multiFiltered, "PhysicalBlocks"], MemberQ[{0, 1}, #[[3]]] &],
  fail["list-valued right polarization filter should keep only listed particle-3 polarizations", multiFiltered["PhysicalBlocks"]]
];

If[invalidKey =!= $Failed,
  fail["left-label key in RightPolarizationFilter should fail", invalidKey]
];

If[invalidValue =!= $Failed,
  fail["invalid RightPolarizationFilter value should fail", invalidValue]
];

If[! KeyExistsQ[filtered["PerformanceSummary"], "Projected.RightPolarizationFilter"],
  fail["performance trace should include right polarization filter stage", filtered["PerformanceSummary"]]
];

Print["projected right polarization filter ok"];
