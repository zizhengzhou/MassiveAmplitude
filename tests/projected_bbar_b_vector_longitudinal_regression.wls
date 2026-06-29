Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, countByOrder, formalSymbolContexts, rightLongitudinalQ];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

countByOrder[assoc_Association] := Association[KeyValueMap[#1 -> Length[#2] &, assoc]];

formalSymbolContexts[expr_] := DeleteDuplicates @ Cases[
  expr,
  s_Symbol /; MemberQ[{"Q", "Xhard", "Xsoft"}, SymbolName[Unevaluated[s]]] :> Context[s],
  Infinity
];

rightLongitudinalQ[block_] := block[[2, 3 ;; 4]] === {1, 1};

fullMass = MassOption[{1, 2, 3, 4}, 4];
spins = {1/2, 1/2, 1, 1};
candidateBlocks = GenerateNeedCFBlocks[spins, 4, mass -> fullMass];
longLongBlocks = Select[candidateBlocks, rightLongitudinalQ];

If[Length[candidateBlocks] =!= 36,
  fail["all-polarization CF block enumeration should include every massive sector", candidateBlocks]
];

If[
  Sort[longLongBlocks] =!= Sort[{{8, {0, 0, 1, 1}}, {8, {0, 1, 1, 1}}, {8, {1, 0, 1, 1}}, {8, {1, 1, 1, 1}}}],
  fail["CF block enumeration should retain the right long-long sectors", longLongBlocks]
];

localLongLongCF = ConstructIndepCFBlock[spins, 8, {0, 1, 1, 1}, mass -> fullMass];
If[! ListQ[localLongLongCF] || Length[localLongLongCF] < 3 || Length[localLongLongCF[[1]]] == 0,
  fail["right long-long CF block should be nonzero", localLongLongCF]
];

allData = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3, 4},
  4,
  {{3, 4}},
  su3ShapeList -> {},
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
];

If[! AssociationQ[allData],
  fail["projected Bbar B uu case should return data", allData]
];

If[Length[Select[allData["PhysicalBlocks"], rightLongitudinalQ]] =!= 4,
  fail["projected candidate blocks should keep all right long-long left-polarization sectors", allData["PhysicalBlocks"]]
];

If[! MemberQ[Lookup[allData["SectorResults"], "RightPolarization", {}], {1, 1}],
  fail["projected sector results should include a nonzero right long-long sector", Lookup[allData["SectorResults"], "RightPolarization", {}]]
];

contexts = formalSymbolContexts[allData["BasisByRelativeChiralOrder"]];
If[! SubsetQ[contexts, {"MassiveBasis`"}],
  fail["formal Q/Xhard/Xsoft symbols should be public MassiveBasis symbols", contexts]
];

filteredData = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3, 4},
  4,
  {{3, 4}},
  su3ShapeList -> {},
  RightPolarizationFilter -> <|3 -> 1, 4 -> 1|>,
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> False
];

If[! AssociationQ[filteredData],
  fail["right long-long filtered projected case should return data", filteredData]
];

If[Total[Values[countByOrder[filteredData["BasisByRelativeChiralOrder"]]]] == 0,
  fail["right long-long filtered projected case should produce nonzero basis elements", filteredData]
];

If[! AllTrue[filteredData["PhysicalBlocks"], rightLongitudinalQ],
  fail["right long-long filter should keep only right long-long CF blocks", filteredData["PhysicalBlocks"]]
];

If[! AllTrue[Lookup[filteredData["SectorResults"], "RightPolarization", {}], # === {1, 1} &],
  fail["right long-long filter should keep only right long-long nonzero sectors", Lookup[filteredData["SectorResults"], "RightPolarization", {}]]
];

q2Data = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3, 4},
  4,
  {{3, 4}},
  su3ShapeList -> {},
  RightPolarizationFilter -> <|3 -> 1, 4 -> 1|>,
  ReturnProjectionData -> True,
  ReplaceQInFinalSymbolForm -> 2
];

If[! AssociationQ[q2Data],
  fail["ReplaceQInFinalSymbolForm -> 2 projected case should return data", q2Data]
];

If[! FreeQ[q2Data["BasisByRelativeChiralOrder"], s_Symbol /; SymbolName[Unevaluated[s]] === "Q"],
  fail["ReplaceQInFinalSymbolForm -> 2 should replace formal Q in final projected output", q2Data["BasisByRelativeChiralOrder"]]
];

invalidMass = Quiet @ ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {1, 3},
  4,
  {},
  su3ShapeList -> {}
];

If[invalidMass =!= $Failed,
  fail["projected right mass labels below 3 should be rejected", invalidMass]
];

Print[
  "projected Bbar B vector longitudinal regression ok counts=",
  InputForm[countByOrder[filteredData["BasisByRelativeChiralOrder"]]]
];
