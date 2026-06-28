ClearAll[fail, runScript];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

If[! DirectoryQ[FileNameJoin[{Directory[], "Package"}]],
  fail["run_all.wls must be run from the MassiveAmplitude chiral-HBP repository root", Directory[]]
];

scripts = {
  "package_smoke.wls",
  "usage_audit.wls",
  "sewing_symbol_amp_form_separation.wls",
  "sewing_left_open_extreme_structures.wls",
  "sewing_relative_chiral_basis_interface.wls",
  "projected_sewing_probe.wls",
  "projected_right_polarization_filter.wls",
  "projected_right_polarization_filter_equivalence.wls",
  "projected_sewing_su3_probe.wls",
  "projected_identical_six_point_regression.wls",
  "projected_performance_trace_smoke.wls",
  "performance_benchmark_smoke.wls",
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
Print["all maintained chiral-HBP regression scripts passed"];
