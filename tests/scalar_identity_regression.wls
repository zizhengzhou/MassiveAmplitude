Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, totalBasisCount, allSectorCompleteQ];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalBasisCount[basis_Association] := Total[Length /@ Values[basis]];
allSectorCompleteQ[sectors_List] := And @@ (TrueQ[Lookup[#, "CompleteQ", False]] & /@ sectors);

identity2 = ConstructIndepCFBlock[{0, 0}, 2, {0, 0}, mass -> {}];
If[identity2 =!= {{1}, {{1}}, {1}},
  fail["two-scalar lowest CF block should be the identity amplitude", identity2]
];

identity4 = ConstructIndepCFBlock[{0, 0, 0, 0}, 4, {0, 0, 0, 0}, mass -> {}];
If[identity4 =!= {{1}, {{1}}, {1}},
  fail["four-scalar lowest CF block should be the identity amplitude", identity4]
];

higherDim2 = ConstructIndepCFBlock[{0, 0}, 3, {0, 0}, mass -> {}];
If[higherDim2 === {{1}, {{1}}, {1}},
  fail["non-minimal scalar CF block should not be replaced by the identity shortcut", higherDim2]
];

comparison32 = CompareGeneralSewingToCFBlocks[
  3/2,
  {0, 0},
  {},
  3,
  {0, 0},
  JMax -> 0
];

If[! AssociationQ[comparison32],
  fail["3/2 scalar identity comparison should return an association", comparison32]
];

If[
  ! TrueQ[comparison32["CompleteQ"]] ||
    comparison32["CFMatrix"]["Rank"] =!= 4 ||
    comparison32["SewingMatrix"]["Rank"] =!= 4 ||
    comparison32["JoinedMatrix"]["Rank"] =!= 4,
  fail["3/2 scalar identity sewing span should match the CF span", comparison32]
];

relative32 = ConstructSewingRelativeChiralBasis[
  3/2,
  {0, 0},
  {},
  3,
  {0, 0},
  JMax -> 0
];

If[! AssociationQ[relative32] || totalBasisCount[relative32] == 0,
  fail["3/2 scalar identity relative chiral basis should be nonempty", relative32]
];

projected32 = ConstructProjectedSewingRelativeChiralBasis[
  3/2,
  {0, 0},
  {},
  3,
  {},
  su3ShapeList -> {},
  ReturnProjectionData -> True
];

If[! AssociationQ[projected32],
  fail["3/2 scalar identity projected basis should return detailed data", projected32]
];

If[totalBasisCount[projected32["BasisByRelativeChiralOrder"]] == 0,
  fail["3/2 scalar identity projected basis should be nonempty", projected32["BasisByRelativeChiralOrder"]]
];

If[! allSectorCompleteQ[projected32["SectorResults"]],
  fail["3/2 scalar identity projected sectors should pass CF completeness checks", projected32["SectorResults"]]
];

comparison12 = CompareGeneralSewingToCFBlocks[
  1/2,
  {0, 0},
  {},
  1,
  {0, 0},
  JMax -> 0
];

If[! AssociationQ[comparison12],
  fail["1/2 scalar identity comparison should return an association", comparison12]
];

If[
  ! TrueQ[comparison12["CompleteQ"]] ||
    comparison12["CFMatrix"]["Rank"] =!= 2 ||
    comparison12["SewingMatrix"]["Rank"] =!= 2 ||
    comparison12["JoinedMatrix"]["Rank"] =!= 2,
  fail["1/2 scalar identity sewing span should match the CF span", comparison12]
];

projected12 = ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {0, 0},
  {},
  1,
  {},
  su3ShapeList -> {},
  ReturnProjectionData -> True
];

If[! AssociationQ[projected12],
  fail["1/2 scalar identity projected basis should return detailed data", projected12]
];

If[totalBasisCount[projected12["BasisByRelativeChiralOrder"]] =!= 2,
  fail["1/2 scalar identity projected basis should contain two left-current structures", projected12["BasisByRelativeChiralOrder"]]
];

If[! allSectorCompleteQ[projected12["SectorResults"]],
  fail["1/2 scalar identity projected sectors should pass CF completeness checks", projected12["SectorResults"]]
];

Print["scalar identity regression ok"];
