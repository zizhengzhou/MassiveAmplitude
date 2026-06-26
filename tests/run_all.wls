ClearAll[fail, runScript];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

If[! DirectoryQ[FileNameJoin[{Directory[], "src", "Package"}]],
  fail["run_all.wls must be run from the sewing-method-code repository root", Directory[]]
];

scripts = {
  "package_smoke.wls",
  "usage_audit.wls",
  "section_5_2_bbuf_reproduce.wls",
  "section_5_2_split_sum_independent_counts.wls",
  "section_5_2_chiral_order_reproduce.wls"
};

runScript[name_String] := Module[{path, exitCode},
  path = FileNameJoin[{"tests", name}];
  If[! FileExistsQ[path], fail["missing test script", path]];
  Print["RUN ", path];
  exitCode = RunProcess[{$SystemShell, "/c", "wolframscript", "-file", path}, "ExitCode"];
  If[exitCode =!= 0, fail["test script failed", <|"Script" -> path, "ExitCode" -> exitCode|>]];
  Print["OK ", path]
];

Scan[runScript, scripts];
Print["all maintained sewing-method-code regression scripts passed"];
