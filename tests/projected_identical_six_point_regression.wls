Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[fail, totalCount, checkCase];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];

checkCase[name_String, identical_List] := Module[
  {result, outputCount, projectedCount, jDiagnostics},
  result = ConstructProjectedSewingRelativeChiralBasis[
    1/2,
    {0, 0, 0, 0},
    {3},
    3,
    identical,
    ReturnProjectionData -> True,
    SewingPerformanceTrace -> True
  ];
  If[! AssociationQ[result], fail["six-point identical projected constructor failed", name]];
  outputCount = totalCount[result["BasisByRelativeChiralOrder"]];
  projectedCount = Total[Length /@ Lookup[result["SectorResults"], "ProjectedItems", {}]];
  If[outputCount =!= projectedCount,
    fail[
      "six-point identical output count should equal selected projected item count",
      <|"Name" -> name, "OutputCount" -> outputCount, "ProjectedCount" -> projectedCount|>
    ]
  ];
  jDiagnostics = DeleteDuplicates[
    Lookup[
      Lookup[result["SectorResults"], "TotalJBlockDiagnostics", {}],
      "PtotalBlockDiagonalByJ",
      Missing["NoDiagnostic"]
    ]
  ];
  If[! MemberQ[jDiagnostics, True],
    fail["six-point identical J-block diagnostic should be true", <|"Name" -> name, "Diagnostics" -> jDiagnostics|>]
  ];
  If[Length[result["PerformanceSummary"]] == 0,
    fail["six-point identical trace summary should be nonempty", name]
  ];
  Print["six-point identical case ok: ", name, " count=", outputCount]
];

checkCase["single-pair", {{3, 4}}];
checkCase["triple", {{4, 5, 6}}];
checkCase["two-pairs", {{3, 4}, {5, 6}}];

Print["projected identical six-point regression ok"];
