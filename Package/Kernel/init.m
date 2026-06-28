(* ::Package:: *)
$DEBUG = False;

Print["initializing..."];
If[$DEBUG =!= True, $DEBUG = False;];
$MassiveDir = If[
  FileExistsQ[FileNameJoin[{Directory[], "src", "Package", "MassiveBasis.m"}]],
  FileNameJoin[{Directory[], "src", "Package"}],
  FileNameDrop[If[$InputFileName === "", NotebookFileName[], $InputFileName], -2]
];
$CodeFiles = FileNameJoin[{$MassiveDir, "Codes", #}] & /@ {
  "Tools.m",
  "SSYT.m",
  "Permutation.m",
  "SU3.m",
  "Amplitude.m",
  "CFblocks.m",
  "Operator.m",
  "FormatOutput.m",
  "Sewing.m",
  "Cache.m"
};
$CodeFiles = Select[$CodeFiles, FileExistsQ];

Print["Codes Files:", $CodeFiles];
Get[FileNameJoin[{$MassiveDir, "MassiveBasis.m"}]]
