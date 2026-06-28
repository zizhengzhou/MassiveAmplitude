If[!ValueQ[$HBPTestLoaded],
  If[!StringQ[$HBPTestCodeRoot],
    $HBPTestCodeRoot = DirectoryName[DirectoryName[$InputFileName]]
  ];
  SetDirectory[$HBPTestCodeRoot];
  Get[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]];
  $HBPTestLoaded = True;
];

VerificationTest[
  {
    FreeQ[FileNameTake /@ $CodeFiles, "Sewing-ZZZNoteBook.m"],
    MemberQ[Options[ConstructLeft3PointOpenBasis][[All, 1]], PointCount]
  },
  {True, True},
  TestID -> "sewing-package-loads-authoritative-file-not-notebook-export"
]

VerificationTest[
  Module[
    {left},
    left = ConstructLeft3PointOpenBasis[0, MassiveSpin -> 3/2, PointCount -> 4];
    Lookup[left, "SortData"]
  ],
  {
    <|"J" -> 0, "Xhard" -> 3, "Xsoft" -> 0|>,
    <|"J" -> 0, "Xhard" -> 2, "Xsoft" -> 1|>,
    <|"J" -> 0, "Xhard" -> 1, "Xsoft" -> 2|>,
    <|"J" -> 0, "Xhard" -> 0, "Xsoft" -> 3|>
  },
  TestID -> "sewing-left-three-point-records-sort-data-for-spin-three-halves-J0"
]

VerificationTest[
  Module[
    {left, sorted},
    left = Join[
      ConstructLeft3PointOpenBasis[0, MassiveSpin -> 3/2, PointCount -> 4],
      ConstructLeft3PointOpenBasis[1, MassiveSpin -> 3/2, PointCount -> 4]
    ];
    sorted = SewingSortRecordsForBasis[left];
    Lookup[Take[sorted, 8], "SortData"]
  ],
  {
    <|"J" -> 0, "Xhard" -> 0, "Xsoft" -> 3|>,
    <|"J" -> 0, "Xhard" -> 1, "Xsoft" -> 2|>,
    <|"J" -> 0, "Xhard" -> 2, "Xsoft" -> 1|>,
    <|"J" -> 0, "Xhard" -> 3, "Xsoft" -> 0|>,
    <|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 2|>,
    <|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 2|>,
    <|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 2|>,
    <|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 2|>
  },
  TestID -> "sewing-sort-orders-actual-left-records-low-J-soft-hard"
]

VerificationTest[
  Module[
    {records, sorted},
    records = {
      <|"SortData" -> <|"J" -> 0, "Xhard" -> 2, "Xsoft" -> 0|>, "AmpL" -> sb[3, J]^100, "AmpR" -> 3|>,
      <|"SortData" -> <|"J" -> 0, "Xhard" -> 1, "Xsoft" -> 1|>, "AmpL" -> 1, "AmpR" -> 2|>,
      <|"SortData" -> <|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 10|>, "AmpL" -> 1, "AmpR" -> 1|>
    };
    sorted = SewingSortRecordsForBasis[records];
    Lookup[sorted, "SortData"]
  ],
  {
    <|"J" -> 0, "Xhard" -> 1, "Xsoft" -> 1|>,
    <|"J" -> 0, "Xhard" -> 2, "Xsoft" -> 0|>,
    <|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 10|>
  },
  TestID -> "sewing-sort-uses-sort-data-not-expression-J-counts"
]

VerificationTest[
  Module[
    {records},
    ClearCache[];
    records = ConstructGeneralSewingAmplitudeRecords[
      1/2, {1, 1}, {3}, 3, {1, 0},
      JRange -> {1},
      FilterPhysicalSector -> False
    ];
    {
      Length[records],
      DeleteDuplicates[Lookup[records, "SortData"]],
      DeleteDuplicates[Lookup[Lookup[records, "LeftRecord"], "SortData"]],
      AllTrue[records, #["SortData"] === #["LeftRecord"]["SortData"] &]
    }
  ],
  {
    2,
    {<|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 0|>},
    {<|"J" -> 1, "Xhard" -> 0, "Xsoft" -> 0|>},
    True
  },
  TestID -> "sewing-general-records-inherit-sort-data-from-left-record"
]

VerificationTest[
  Quiet[
    SewingSortRecordsForBasis[
      {
        <|"SortData" -> <|"J" -> 0, "Xhard" -> 0, "Xsoft" -> 1|>|>,
        <|"J" -> 0, "AmpL" -> sb[3, J]^100|>
      }
    ],
    {SewingSortRecordsForBasis::sortdata}
  ],
  $Failed,
  TestID -> "sewing-sort-rejects-missing-sort-data"
]
