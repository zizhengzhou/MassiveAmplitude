Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[fail, totalCount];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

totalCount[assoc_Association] := Total[Length /@ Values[assoc]];

plain = ConstructProjectedSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {},
  ReturnProjectionData -> True
];

If[! AssociationQ[plain] || KeyExistsQ[plain, "PerformanceSummary"] && plain["PerformanceSummary"] =!= <||>,
  fail["performance trace should be disabled by default", KeyTake[plain, {"PerformanceTrace", "PerformanceSummary"}]]
];

traced = ConstructProjectedSewingRelativeChiralBasis[
  1/2, {1, 1}, {3}, 4, {},
  ReturnProjectionData -> True,
  SewingPerformanceTrace -> True
];

If[! AssociationQ[traced], fail["traced projected constructor should return detailed association", traced]];
If[totalCount[traced["BasisByRelativeChiralOrder"]] != totalCount[plain["BasisByRelativeChiralOrder"]],
  fail["tracing should not change basis count", <|"Plain" -> plain["BasisByRelativeChiralOrder"], "Traced" -> traced["BasisByRelativeChiralOrder"]|>]
];
If[! ListQ[traced["PerformanceTrace"]] || Length[traced["PerformanceTrace"]] == 0,
  fail["performance trace should contain stage events", traced]
];
If[! AssociationQ[traced["PerformanceSummary"]] || Length[traced["PerformanceSummary"]] == 0,
  fail["performance summary should be nonempty", traced["PerformanceSummary"]]
];
requiredStages = {
  "Projected.GenerateNeedCFBlocks",
  "Projected.ConstructIndepCFBlock",
  "Projected.GeneralSewingRecords",
  "General.RightAuxiliaryRawRecords",
  "Project.FilterByPolarization",
  "Project.SewingCoeffMatrix",
  "Projected.GroupByRelativeChiralOrder"
};
missingStages = Select[requiredStages, ! KeyExistsQ[traced["PerformanceSummary"], #] &];
If[missingStages =!= {}, fail["performance summary missed required stages", missingStages]];

cacheSummary = Lookup[traced["PerformanceSummary"], "Cache.RightPolarizationRecords", <||>];
If[! AssociationQ[cacheSummary] || Lookup[cacheSummary, "CacheMisses", 0] == 0,
  fail["right-polarization local cache should record misses", cacheSummary]
];

rawCacheSummary = Lookup[traced["PerformanceSummary"], "Cache.GeneralRightAuxiliaryRawRecords", <||>];
If[! AssociationQ[rawCacheSummary] || Lookup[rawCacheSummary, "CacheHits", 0] == 0 || Lookup[rawCacheSummary, "CacheMisses", 0] == 0,
  fail["general right auxiliary raw-record cache should record hits and misses", rawCacheSummary]
];

leftCacheSummary = Lookup[traced["PerformanceSummary"], "Cache.GeneralLeft3Point", <||>];
If[! AssociationQ[leftCacheSummary] || Lookup[leftCacheSummary, "CacheHits", 0] == 0 || Lookup[leftCacheSummary, "CacheMisses", 0] == 0,
  fail["projected left 3pt cache should record hits and misses", leftCacheSummary]
];

Print["projected performance trace smoke ok"];
