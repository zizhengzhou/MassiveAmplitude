Get[FileNameJoin[{"Package", "Kernel", "init.m"}]];

ClearAll[
  fail, countByOrder, projectedItemsWithSector, itemFullPolarizations,
  normalizeFilter, polarizationAllowedQ, itemAllowedByFilterQ,
  formatItem, groupItemsByRelativeOrder, manualFilteredBasis,
  compareFilterFromAll, generatedFiltersForData, physicalCaseKey,
  runCase, runGeneratedCase
];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

countByOrder[assoc_Association] := Association[KeyValueMap[#1 -> Length[#2] &, assoc]];
projectedItemsWithSector[data_Association] := Flatten[
  Table[
    Append[#, "ManualFullPolarization" -> sector["FullPolarization"]] & /@
      Lookup[sector, "ProjectedItems", {}],
    {sector, data["SectorResults"]}
  ],
  1
];

normalizeFilter[All, _Integer?Positive] := All;
normalizeFilter[filter_Association, pointCount_Integer?Positive] := Module[
  {normalizeValue, pairs},
  normalizeValue[All] := All;
  normalizeValue[value_Integer] := {value};
  normalizeValue[values_List] /; AllTrue[values, IntegerQ] := DeleteDuplicates[values];
  normalizeValue[_] := $Failed;
  pairs = KeyValueMap[
    Function[{label, value},
      If[! IntegerQ[label] || label < 3 || label > pointCount,
        Return[$Failed, Module]
      ];
      With[{normalizedValue = normalizeValue[value]},
        If[normalizedValue === $Failed,
          Return[$Failed, Module]
        ];
        label -> normalizedValue
      ]
    ],
    filter
  ];
  Association[pairs]
];
normalizeFilter[_, _Integer?Positive] := $Failed;

polarizationAllowedQ[_List, All] := True;
polarizationAllowedQ[fullPolarization_List, filter_Association] := AllTrue[
  Normal[filter],
  Function[rule,
    rule[[2]] === All || MemberQ[rule[[2]], fullPolarization[[rule[[1]]]]]
  ]
];

itemFullPolarizations[item_Association, pointCount_Integer, masses_List] := Module[
  {record, amp, terms, metas, rightSpins},
  record = item["LorentzRecord"];
  amp = Lookup[item["LorentzRecord"], "TotalAmp", Lookup[item["LorentzRecord"], "SewingAmpForm", 0]];
  terms = Sum2List[Expand[amp]];
  metas = Amp2MetaInfo[#, pointCount, mass -> masses] & /@ terms;
  rightSpins = Lookup[record, "RightSpins", {}];
  DeleteDuplicates @ Cases[
    metas,
    meta_ /; ListQ[meta] && Length[meta] >= 2 && Drop[meta[[1]], 2] === rightSpins :> meta[[2]]
  ]
];

itemAllowedByFilterQ[item_Association, filter_, pointCount_Integer, masses_List] := Module[
  {polarizations},
  polarizations = itemFullPolarizations[item, pointCount, masses];
  AnyTrue[polarizations, polarizationAllowedQ[#, filter] &]
];

formatItem[item_Association] := Module[
  {lorentz = item["LorentzSymbolForm"], replaced},
  replaced = SewingReplaceQInSymbolForm[lorentz, {1, -2}];
  If[replaced === $Failed, replaced = lorentz];
  If[KeyExistsQ[item, "SU3Basis"],
    KeyDrop[Append[item, "LorentzSymbolForm" -> replaced], {"LorentzRecord"}],
    replaced
  ]
];

groupItemsByRelativeOrder[items_List] := KeySort @ Merge[
  (<|#["RelativeChiralOrder"] -> {formatItem[#]}|> &) /@ items,
  Apply[Join, #] &
];

manualFilteredBasis[data_Association, filterSpec_] := Module[
  {pointCount, filter, items, selected},
  pointCount = Length[data["Spins"]];
  filter = normalizeFilter[filterSpec, pointCount];
  If[filter === $Failed, Return[$Failed]];
  items = projectedItemsWithSector[data];
  selected = Select[
    items,
    itemAllowedByFilterQ[#, filter, pointCount, data["Mass"]] &
  ];
  groupItemsByRelativeOrder[selected]
];

compareFilterFromAll[case_Association, allData_Association, filterSpec_, label_] := Module[
  {filteredData, manualBasis, optionBasis},
  Print["FILTER-EQUIV RUN ", case["Name"], " / ", label];
  filteredData = ConstructProjectedSewingRelativeChiralBasis[
    case["LeftSpin"],
    case["RightSpins"],
    case["RightMass"],
    case["AmpDim"],
    case["Identical"],
    RightPolarizationFilter -> filterSpec,
    ReturnProjectionData -> True
  ];
  If[! AssociationQ[filteredData],
    fail["filtered projected run failed", case]
  ];
  manualBasis = manualFilteredBasis[allData, filterSpec];
  optionBasis = filteredData["BasisByRelativeChiralOrder"];
  If[manualBasis =!= optionBasis,
    fail[
      "RightPolarizationFilter output should match Amp2MetaInfo manual filtering",
      <|
        "Case" -> case["Name"],
        "Filter" -> filterSpec,
        "OptionCounts" -> countByOrder[optionBasis],
        "ManualCounts" -> countByOrder[manualBasis],
        "OptionBasis" -> optionBasis,
        "ManualBasis" -> manualBasis
      |>
    ]
  ];
  Print[
    "FILTER-EQUIV OK ",
    case["Name"],
    " / ",
    label,
    " counts=",
    InputForm[countByOrder[optionBasis]]
  ]
];

generatedFiltersForData[data_Association] := Module[
  {
    pointCount, rightLabels, items, polarizations, valuesByLabel,
    activeLabels, singleFilters, listFilters, pairFilters, allMixedFilters,
    emptyFilters, pairLabels, firstLabel, secondLabel
  },
  pointCount = Length[data["Spins"]];
  rightLabels = Range[3, pointCount];
  items = projectedItemsWithSector[data];
  polarizations = DeleteDuplicates @ Flatten[
    itemFullPolarizations[#, pointCount, data["Mass"]] & /@ items,
    1
  ];
  If[polarizations === {}, Return[{}]];
  valuesByLabel = Association @ Table[
    label -> Sort @ DeleteDuplicates[polarizations[[All, label]]],
    {label, rightLabels}
  ];
  activeLabels = Select[rightLabels, Lookup[valuesByLabel, #, {}] =!= {} &];
  singleFilters = Table[
    <|
      "Label" -> "single-p" <> ToString[label],
      "Filter" -> Association[label -> First[valuesByLabel[label]]]
    |>,
    {label, activeLabels}
  ];
  listFilters = Table[
    If[Length[valuesByLabel[label]] >= 2,
      <|
        "Label" -> "list-p" <> ToString[label],
        "Filter" -> Association[label -> Take[valuesByLabel[label], UpTo[2]]]
      |>,
      Nothing
    ],
    {label, activeLabels}
  ];
  pairLabels = Take[activeLabels, UpTo[2]];
  pairFilters = If[Length[pairLabels] >= 2,
    {
      <|
        "Label" -> "pair-first-two",
        "Filter" -> Association[
          pairLabels[[1]] -> First[valuesByLabel[pairLabels[[1]]]],
          pairLabels[[2]] -> First[valuesByLabel[pairLabels[[2]]]]
        ]
      |>
    },
    {}
  ];
  allMixedFilters = If[Length[pairLabels] >= 2,
    firstLabel = pairLabels[[1]];
    secondLabel = pairLabels[[2]];
    {
      <|
        "Label" -> "all-plus-single",
        "Filter" -> Association[
          firstLabel -> All,
          secondLabel -> First[valuesByLabel[secondLabel]]
        ]
      |>
    },
    {}
  ];
  emptyFilters = Table[
    <|
      "Label" -> "empty-p" <> ToString[label],
      "Filter" -> Association[label -> Max[valuesByLabel[label]] + 1]
    |>,
    {label, Take[activeLabels, UpTo[2]]}
  ];
  Take[
    Join[singleFilters, listFilters, pairFilters, allMixedFilters, emptyFilters],
    UpTo[8]
  ]
];

runCase[case_Association] := Module[
  {allData},
  allData = ConstructProjectedSewingRelativeChiralBasis[
    case["LeftSpin"],
    case["RightSpins"],
    case["RightMass"],
    case["AmpDim"],
    case["Identical"],
    ReturnProjectionData -> True
  ];
  If[! AssociationQ[allData],
    fail["all-sector projected run failed", case]
  ];
  compareFilterFromAll[case, allData, case["Filter"], "explicit"]
];

runGeneratedCase[case_Association] := Module[
  {allData, generatedFilters},
  Print["FILTER-EQUIV GENERATED BASE ", case["Name"]];
  allData = ConstructProjectedSewingRelativeChiralBasis[
    case["LeftSpin"],
    case["RightSpins"],
    case["RightMass"],
    case["AmpDim"],
    case["Identical"],
    ReturnProjectionData -> True
  ];
  If[! AssociationQ[allData],
    fail["all-sector projected generated run failed", case]
  ];
  generatedFilters = generatedFiltersForData[allData];
  If[generatedFilters === {},
    fail["generated filter list should not be empty", case]
  ];
  Scan[
    compareFilterFromAll[case, allData, #["Filter"], #["Label"]] &,
    generatedFilters
  ]
];

physicalCaseKey[case_Association] := Lookup[
  case,
  {"LeftSpin", "RightSpins", "RightMass", "AmpDim", "Identical"}
];

cases = {
  <|"Name" -> "4pt-vector-p3-pol2", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "Filter" -> <|3 -> 2|>|>,
  <|"Name" -> "4pt-vector-p4-pol0", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {}, "Filter" -> <|4 -> 0|>|>,
  <|"Name" -> "4pt-identical-p3-pol2", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "Identical" -> {{3, 4}}, "Filter" -> <|3 -> 2|>|>,
  <|"Name" -> "4pt-identical-empty-pol1", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1}, "RightMass" -> {3, 4}, "AmpDim" -> 6, "Identical" -> {{3, 4}}, "Filter" -> <|3 -> 1|>|>,
  <|"Name" -> "5pt-target-vector-vector-scalar", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 0}, "RightMass" -> {3, 4}, "AmpDim" -> 4, "Identical" -> {{3, 4}}, "Filter" -> <|3 -> 2|>|>,
  <|"Name" -> "5pt-target-list-and-all", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 0}, "RightMass" -> {3, 4}, "AmpDim" -> 4, "Identical" -> {{3, 4}}, "Filter" -> <|3 -> {0, 2}, 5 -> All|>|>,
  <|"Name" -> "5pt-scalar-pair", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {{4, 5}}, "Filter" -> <|3 -> 0|>|>,
  <|"Name" -> "6pt-scalar-two-pairs", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{3, 4}, {5, 6}}, "Filter" -> <|3 -> 0, 5 -> 0|>|>,
  <|"Name" -> "6pt-scalar-triple", "LeftSpin" -> 1/2, "RightSpins" -> {0, 0, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 4, "Identical" -> {{4, 5, 6}}, "Filter" -> <|4 -> 0|>|>,
  <|"Name" -> "6pt-mixed-spin-list", "LeftSpin" -> 1/2, "RightSpins" -> {1, 1, 0, 0}, "RightMass" -> {3}, "AmpDim" -> 5, "Identical" -> {{4, 5}}, "Filter" -> <|3 -> {0, 2}, 6 -> 0|>|>
};

Scan[runCase, cases];

generatedCases = DeleteDuplicatesBy[KeyDrop[#, "Filter"] & /@ cases, physicalCaseKey];

Scan[runGeneratedCase, generatedCases];

Print["projected right polarization filter equivalence ok"];
