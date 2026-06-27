Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];

ClearAll[
  fail, records, splitRecords, block, badMaps, symTerms, ampTerms,
  displaySymbolQ, symbolNameQ, containsBracketLabelQ
];

fail[msg_, data_: None] := (
  Print[msg, If[data === None, "", ": " <> ToString[data, InputForm]]];
  Exit[1]
);

displaySymbolQ[expr_] := ! FreeQ[
  expr,
  s_Symbol /; MemberQ[{"Xhard", "Xsoft", "Q"}, SymbolName[Unevaluated[s]]]
];
symbolNameQ[x_, name_String] := MatchQ[x, _Symbol] && SymbolName[Unevaluated[x]] === name;
containsBracketLabelQ[expr_, head_, labels_List] := ! FreeQ[
  expr,
  b_ /; Head[b] === head && AnyTrue[List @@ b, MemberQ[labels, #] &]
];

If[! MatchQ[Unevaluated[SewingDisplayForm[sb[L1, 4]]], _SewingDisplayForm],
  fail["SewingDisplayForm should require an explicit point count"]
];

records = ConstructGeneralSewingAmplitudeRecords[
  1/2, {1, 1}, {3}, 4, {1, 0},
  JRange -> {2},
  SewingDebug -> False
];

If[! ListQ[records] || Length[records] == 0,
  fail["expected nonempty sewing records"]
];

If[! AllTrue[records, KeyExistsQ[#, "SewingSymForm"] && KeyExistsQ[#, "SewingAmpForm"] && KeyExistsQ[#, "FormMap"] &],
  fail["records should carry symbol/amp form mapping", KeyTake[First[records], {"SewingSymForm", "SewingAmpForm", "FormMap"}]]
];

badMaps = Select[
  records,
  Expand[SewingSymbolToAmpForm[#["SewingSymForm"], #["PointCount"], #["QReplacement"]] - #["FormMap"]["AmpFormRaw"]] =!= 0 ||
    Expand[SewingSymbolToAmpForm[#["SewingDisplayForm"], #["PointCount"], #["QReplacement"]] - #["FormMap"]["AmpFormRaw"]] =!= 0 ||
    Expand[#["SewingAmpForm"] - #["FormMap"]["WorkingAmpForm"]] =!= 0 &
];
If[badMaps =!= {},
  fail["symbol/display forms should map to AmpFormRaw and working amp form should be explicit", KeyTake[First[badMaps], {"SewingSymForm", "SewingDisplayForm", "SewingAmpForm", "FormMap", "QReplacement"}]]
];

splitRecords = Select[records, #["ContractionMode"] === "Split" && #["ContractionTermCount"] > 1 &];
If[splitRecords === {},
  fail["expected at least one split symmetric contraction record"]
];

If[
  ! AnyTrue[splitRecords[[All, "SewingSymForm"]], displaySymbolQ],
  fail["split symbolic records should retain Xhard/Xsoft/Q factors before amp-form expansion"]
];

If[
  ! AnyTrue[
    splitRecords[[All, "SewingDisplayForm"]],
    containsBracketLabelQ[#, sb, {7, 8}] &&
      ! containsBracketLabelQ[#, sb, {1, 2}] &&
      ! containsBracketLabelQ[#, ab, {7, 8}] &
  ],
  fail["display symbolic records should keep massive square labels on square brackets only", splitRecords[[All, "SewingDisplayForm"]]]
];

If[
  ! AnyTrue[
    splitRecords,
    (! FreeQ[#["SewingDisplayForm"], s_Symbol /; symbolNameQ[s, "Q"]]) &&
      Expand[
        SewingSymbolToAmpForm[#["SewingDisplayForm"], #["PointCount"], Automatic] -
          #["SewingAmpForm"]
      ] === 0 &
  ],
  fail["Q-bearing display form should map to amp form with Q = p1-p2 and massive square labels intact"]
];

symTerms = SewingContractionTerms[
  First[splitRecords]["LeftRecord"]["AmpLSymbolForm"],
  First[splitRecords]["RightRecord"]["AmpR"]
];
ampTerms = SewingSymbolToAmpForm[#, First[splitRecords]["PointCount"], First[splitRecords]["QReplacement"]] & /@ symTerms;
If[
  Length[symTerms] != First[splitRecords]["ContractionTermCount"] ||
    Expand[Total[ampTerms] - SymmetricSewContract[First[splitRecords]["LeftRecord"]["AmpL"], First[splitRecords]["RightRecord"]["AmpR"]]] =!= 0,
  fail["split symbolic contraction terms should sum to amp-form symmetric contraction"]
];

block = ConstructIndepSewingBlock[
  1/2, {1, 1}, {3}, 4, {1, 0},
  JMax -> 3,
  QReplacement -> 2,
  CheckAgainstCF -> True,
  SewingDebug -> False
];
If[! (ListQ[block] && Length[block] == 3 && Length[block[[1]]] == 3),
  fail["expected independent block with three symbolic basis amplitudes", block]
];
If[! AnyTrue[block[[1]], displaySymbolQ],
  fail["default independent block output should use symbolic form", block[[1]]]
];

blockRecords = ConstructIndepSewingBlock[
  1/2, {1, 1}, {3}, 4, {1, 0},
  JMax -> 3,
  QReplacement -> 2,
  CheckAgainstCF -> True,
  ReturnRecords -> True,
  SewingDebug -> False
];
If[
  ! AssociationQ[blockRecords] ||
    blockRecords["Amplitudes"] =!= SewingRecordSymbolForm /@ blockRecords["Records"] ||
    MatrixRank[blockRecords["Matrix"]] =!= Length[blockRecords["Records"]],
  fail["independent block should select records by reduced amp matrix and return the same records' symbol forms", blockRecords]
];

block = ConstructIndepSewingBlock[
  1/2, {1, 1}, {3}, 4, {1, 0},
  JMax -> 3,
  QReplacement -> 2,
  CheckAgainstCF -> True,
  SewingOutputForm -> "AmpForm",
  SewingDebug -> False
];
If[AnyTrue[block[[1]], displaySymbolQ],
  fail["AmpForm independent block output should not contain Xhard/Xsoft/Q", block[[1]]]
];

Print["sewing symbol/amp form separation ok"];
