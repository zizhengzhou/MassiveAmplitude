cwd = Directory[];
codeRoot = If[
  FileNameTake[cwd] === "MassiveAmplitude-Code",
  cwd,
  FileNameJoin[{cwd, "Codes", "MassiveAmplitude-Code"}]
];
testDir = FileNameJoin[{codeRoot, "Test"}];
SetDirectory[codeRoot];

$HBPTestCodeRoot = codeRoot;
$HBPTestLogRoot = FileNameJoin[{codeRoot, "logs"}];
If[!DirectoryQ[$HBPTestLogRoot],
  CreateDirectory[$HBPTestLogRoot, CreateIntermediateDirectories -> True]
];

testFiles = FileNames["*.wlt", testDir];
report = TestReport[testFiles];
Print[report];

reportData = report /. TestReportObject[data_] :> data;
failedKeys = Join[
  Lookup[reportData, "TestsFailedWrongResultsKeys", {}],
  Lookup[reportData, "TestsFailedWithMessagesKeys", {}],
  Lookup[reportData, "TestsNotEvaluatedKeys", {}],
  Keys @ Lookup[reportData, "FailureResults", <||>]
];

If[!TrueQ[Lookup[reportData, "Aborted", False]] && Length[failedKeys] == 0,
  Exit[0],
  Exit[1]
];
