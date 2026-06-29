Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, displaySymbolQ, totalCount];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

displaySymbolQ[expr_] := ! FreeQ[
  expr,
  s_Symbol /; MemberQ[{"Xhard", "Xsoft", "Q"}, SymbolName[Unevaluated[s]]]
];
qSymbolQ[expr_] := ! FreeQ[
  expr,
  s_Symbol /; SymbolName[Unevaluated[s]] === "Q"
];
totalCount[assoc_Association] := Total[Length /@ Values[assoc]];

result = ConstructSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {1, 0},
  SewingDebug -> False
];

If[! AssociationQ[result],
  fail["relative chiral basis should return an association", result]
];
If[Keys[result] =!= {2, 3},
  fail["ampDim=4 interface should group the independent basis by relative chiral order", result]
];
If[totalCount[result] =!= 3,
  fail["ampDim=4 interface should return exactly the CF-equivalent independent count", result]
];
If[Length[result[2]] =!= 2 || Length[result[3]] =!= 1,
  fail["ampDim=4 interface should reproduce the expected relative-order split", result]
];
If[AnyTrue[Flatten[Values[result]], qSymbolQ],
  fail["relative chiral basis should replace Q in final output by default", result]
];

qResult = ConstructSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {1, 0},
  ReplaceQInFinalSymbolForm -> False,
  SewingDebug -> False
];
If[! AnyTrue[Flatten[Values[qResult]], qSymbolQ],
  fail["relative chiral basis should allow retaining Q in final output", qResult]
];

explicitJResult = ConstructSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {1, 0},
  JMax -> 3,
  SewingDebug -> False
];
If[explicitJResult =!= result,
  fail["automatic J scan should agree with explicit sufficient JMax for this example", <|"Automatic" -> result, "Explicit" -> explicitJResult|>]
];

comparison = CompareGeneralSewingToCFBlocks[
  1/2, {1, 1}, {3}, 4, {1, 0},
  SewingDebug -> False
];
If[
  ! TrueQ[comparison["CompleteQ"]] ||
    comparison["CFMatrix"]["Rank"] =!= totalCount[result] ||
    comparison["SewingMatrix"]["Rank"] =!= totalCount[result] ||
    comparison["JoinedMatrix"]["Rank"] =!= totalCount[result],
  fail["relative chiral basis should pass explicit CF/sewing/count equality", <|"Result" -> result, "Comparison" -> KeyTake[comparison, {"CFMatrix", "SewingMatrix", "JoinedMatrix", "CompleteQ"}]|>]
];

resultWithMass = ConstructSewingRelativeChiralBasis[
  1/2, {1, 1}, Automatic, 4, {1, 0},
  SewingDebug -> False
];
If[resultWithMass =!= result,
  fail["rightMass overload should agree with the option-based default for this example", resultWithMass]
];

Print["sewing relative chiral basis interface ok"];
