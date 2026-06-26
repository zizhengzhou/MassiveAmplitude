ClearAll[HBPFindRoot];
HBPFindRoot[start_] := Module[{dir, parents},
  dir = If[StringQ[start] && start =!= "", If[DirectoryQ[start], start, DirectoryName[start]], $Failed];
  If[dir === $Failed, Return[Missing["NotFound"]]];
  parents = NestList[DirectoryName, dir, 8];
  SelectFirst[
    parents,
    FileExistsQ[FileNameJoin[{#, "Package", "Kernel", "init.m"}]] &,
    Missing["NotFound"]
  ]
];

If[!TrueQ[$HBPTestLoaded],
  If[!StringQ[$HBPTestCodeRoot] || !FileExistsQ[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]],
    $HBPTestCodeRoot = SelectFirst[
      DeleteCases[{HBPFindRoot[$InputFileName], HBPFindRoot[Directory[]]}, Missing["NotFound"]],
      StringQ,
      $Failed
    ]
  ];
  If[!StringQ[$HBPTestLogRoot],
    $HBPTestLogRoot = FileNameJoin[{$HBPTestCodeRoot, "logs"}]
  ];
  SetDirectory[$HBPTestCodeRoot];
  Get[FileNameJoin[{$HBPTestCodeRoot, "Package", "Kernel", "init.m"}]];
  Get[FileNameJoin[{$HBPTestCodeRoot, "SoftHeavyFactorization.executable.m"}]];
  $HBPTestLoaded = True;
];

ClearAll[leftSampleSummary];
leftSampleSummary[spin_, np_] := Table[
  Module[{rec = ConstructLeft3PointOpenBasis[j, MassiveSpin -> spin, PointCount -> np, QReplacement -> 2]},
    {
      Length[rec],
      AllTrue[SewingLeftRecordCheck /@ rec, TrueQ[#["ValidQ"]] &],
      ToString[rec[[1, "AmpL"]], InputForm]
    }
  ],
  {j, 0, 5}
];

VerificationTest[
  leftSampleSummary[1/2, 4],
  {
    {2, True, "-ab[1, 2] - sb[7, 8]"},
    {4, True, "sb[7, J]*sb[8, J]"},
    {4, True, "ab[2, J]*sb[2, J]*sb[7, J]*sb[8, J]"},
    {4, True, "ab[2, J]^2*sb[2, J]^2*sb[7, J]*sb[8, J]"},
    {4, True, "ab[2, J]^3*sb[2, J]^3*sb[7, J]*sb[8, J]"},
    {4, True, "ab[2, J]^4*sb[2, J]^4*sb[7, J]*sb[8, J]"}
  },
  TestID -> "left-pointcount-s12-n4"
]

VerificationTest[
  leftSampleSummary[1/2, 5],
  {
    {2, True, "-ab[1, 2] - sb[9, 10]"},
    {4, True, "sb[9, J]*sb[10, J]"},
    {4, True, "ab[2, J]*sb[2, J]*sb[9, J]*sb[10, J]"},
    {4, True, "ab[2, J]^2*sb[2, J]^2*sb[9, J]*sb[10, J]"},
    {4, True, "ab[2, J]^3*sb[2, J]^3*sb[9, J]*sb[10, J]"},
    {4, True, "ab[2, J]^4*sb[2, J]^4*sb[9, J]*sb[10, J]"}
  },
  TestID -> "left-pointcount-s12-n5"
]

VerificationTest[
  ToString[
    ConstructLeft3PointOpenBasis[2, MassiveSpin -> 1/2, PointCount -> 5, QReplacement -> {1, -2}][[1, "AmpL"]],
    InputForm
  ],
  "ab[1, J]*sb[1, J]*sb[9, J]*sb[10, J] - ab[2, J]*sb[2, J]*sb[9, J]*sb[10, J]",
  TestID -> "left-qreplacement-signed-list"
]

VerificationTest[
  leftSampleSummary[3/2, 4][[All, 1]],
  {4, 12, 18, 16, 16, 16},
  TestID -> "left-pointcount-s32-n4-counts"
]

VerificationTest[
  leftSampleSummary[3/2, 5][[All, 1]],
  {4, 12, 18, 16, 16, 16},
  TestID -> "left-pointcount-s32-n5-counts"
]

VerificationTest[
  Module[{cmp = CompareGeneralSewingToCFBlocks[1/2, {1, 1}, {3}, 4, {1, 0}, JMax -> 2, QReplacement -> 2]},
    {cmp["CFMatrix"]["Rank"], cmp["SewingMatrix"]["Rank"], cmp["JoinedMatrix"]["Rank"], cmp["CompleteQ"]}
  ],
  {3, 3, 3, True},
  TestID -> "sewing-cf-complete-n4-d4"
]

VerificationTest[
  Table[
    Module[{cmp = CompareGeneralSewingToCFBlocks[1/2, {1, 1}, {3}, d, {1, 0}, JMax -> 2, QReplacement -> 2]},
      {cmp["CFMatrix"]["Rank"], cmp["SewingMatrix"]["Rank"], cmp["JoinedMatrix"]["Rank"], cmp["CompleteQ"]}
    ],
    {d, 3, 5}
  ],
  {{2, 2, 2, True}, {3, 3, 3, True}, {4, 4, 4, True}},
  TestID -> "sewing-cf-complete-n3to5"
]
