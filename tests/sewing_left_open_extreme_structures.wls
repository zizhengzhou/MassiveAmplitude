ClearAll[fail, rankValue];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

leftJ1 = ConstructLeft3PointOpenBasis[
  1,
  MassiveSpin -> 1/2,
  PointCount -> 5,
  QReplacement -> {1, -2}
];

If[Length[leftJ1] =!= 4,
  fail["spin-1/2 J=1 left three-point basis should keep all four open structures", Length[leftJ1]]
];

If[! AnyTrue[leftJ1, #["OpenPowers"] === <|"Angle1" -> 0, "Square1" -> 1, "Angle2" -> 0, "Square2" -> 1|> &],
  fail["spin-1/2 J=1 left three-point basis is missing the pure-square [1'J][2'J] structure"]
];

If[! AnyTrue[leftJ1, #["OpenPowers"] === <|"Angle1" -> 1, "Square1" -> 0, "Angle2" -> 1, "Square2" -> 0|> &],
  fail["spin-1/2 J=1 left three-point basis is missing the pure-angle <1J><2J> structure"]
];

ClearCache[];
cmp = CompareGeneralSewingToCFBlocks[
  1/2, {0, 0, 0}, {3}, 3, {0, 0, 0},
  JMax -> 4,
  SewingDebug -> False
];

If[! AssociationQ[cmp],
  fail["5-point scalar one-mass comparison did not return an association", cmp]
];

rankValue[assoc_, key_] := Lookup[Lookup[assoc, key, <||>], "Rank", Missing["NoRank"]];

If[
  ! TrueQ[cmp["CompleteQ"]] ||
    rankValue[cmp, "CFMatrix"] =!= 12 ||
    rankValue[cmp, "SewingMatrix"] =!= 12 ||
    rankValue[cmp, "JoinedMatrix"] =!= 12,
  fail[
    "5-point scalar one-mass sewing should reproduce the full CF span after pure open structures are retained",
    <|
      "CFRecords" -> Length[Lookup[cmp, "CFRecords", {}]],
      "SewingRecords" -> Length[Lookup[cmp, "SewingRecords", {}]],
      "CFRank" -> rankValue[cmp, "CFMatrix"],
      "SewingRank" -> rankValue[cmp, "SewingMatrix"],
      "JoinedRank" -> rankValue[cmp, "JoinedMatrix"],
      "CompleteQ" -> Lookup[cmp, "CompleteQ", Missing["NoCompleteQ"]],
      "JValues" -> DeleteDuplicates[Lookup[Lookup[cmp, "SewingRecords", {}], "J", Missing["NoJ"]]]
    |>
  ]
];

If[! MemberQ[DeleteDuplicates[Lookup[cmp["SewingRecords"], "J", Missing["NoJ"]]], 1],
  fail["5-point scalar one-mass sewing should include J=1 sewn records"]
];

Print["left open extreme structures ok"];
