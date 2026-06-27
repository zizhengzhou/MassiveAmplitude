Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, totalCount];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];

result = ConstructProjectedSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {},
  su3ShapeList -> {"", "", "q", "aq"},
  ReturnProjectionData -> True,
  SewingDebug -> False
];

If[! AssociationQ[result], fail["projected SU3 constructor should return association data", result]];
If[totalCount[result["BasisByRelativeChiralOrder"]] == 0,
  fail["projected SU3 basis should not vanish for q aq color singlet", result]
];
items = Flatten[Values[result["BasisByRelativeChiralOrder"]], 1];
If[! AllTrue[items, AssociationQ],
  fail["SU3 projected output should use association items to preserve direct-product structure", items]
];
If[! AllTrue[items, KeyExistsQ[#, "SU3IndexDictionary"] && KeyExistsQ[#, "SU3Basis"] && KeyExistsQ[#, "LorentzSymbolForm"] &],
  fail["SU3 projected output should preserve Lorentz, color basis, and su3IndDict", items]
];
If[! AllTrue[items, MatchQ[#["DirectProduct"], {_ , _}] &],
  fail["SU3 projected output should represent Lorentz/color as direct-product pairs", items]
];
If[result["SU3IndexDictionaries"] === {} || result["SU3IndexDictionaries"] === {<||>},
  fail["SU3 index dictionary should be propagated in detailed output", result["SU3IndexDictionaries"]]
];

Print["projected sewing SU3 probe ok"];
