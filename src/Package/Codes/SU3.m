(* ::Package:: *)

LogPri["SU3 Loaded"];
(*Now only for SU3, to be expanded to SUN*)


(* ::Section:: *)
(*Step1 Specify indices and construct basis*)
(*Input: identical blocks shape, particle amount*)
(*Output: all particle indices dict*)


(*for gluon, convention tableaux is {{1,2},{3}}*)
su3ShapeDict = <|"" -> {}, "q" -> {1}, "aq" -> {1, 1}, "g" -> {2, 1}|>;

GetColorIndDict[shapes_List] := Module[{indAmountList, indDict, lastInd = 0
},
  indAmountList = Transpose@{Range[Length@shapes], Total /@ shapes} // SortBy[#, Last]&;
  indDict = Do[
    If[e[[2]] != 0 ,
      Sow[e[[1]] -> lastInd + Range[e[[2]]]];
      lastInd = lastInd + e[[2]];]
    , {e, indAmountList}] // Reap // Last // First // Association;
  Return[indDict];
];

ConstructColorBasis[nColumn_Integer] := GenerateStandardTableaux[ConstantArray[nColumn, 3]];



(* ::Section:: *)
(*Step2 Permute particles to form new young tableaux*)


GetPermuteColorIdenticalRules[identicalParticleList_List, colorIndDict_Association] := Module[
  {particleReplaceRules = GetMasslessIdenticalRules[identicalParticleList],
    ReplaceParticle2ColorRule},
  ReplaceParticle2ColorRule[n1_ -> n2_] := MapThread[#1 -> #2&, {colorIndDict[n1], colorIndDict[n2]}];
  Return[(ReplaceParticle2ColorRule /@ # // Flatten)& /@ particleReplaceRules]
];

(*Only used for generate the necessary operator names and replace rules. Not imply any identical condition.*)
GetPermuteColorInnerRules[colorIndDict_Association] := Module[
  {permutationColorRuleDict, GenColorRule},
  (*extra tail for reusage of function for identical symm.*)
  GenColorRule[inds_] := GetMasslessIdenticalRules@Switch[Length@inds, 1, {}, _, inds ~ Append ~ {"S"}];
  permutationColorRuleDict = GenColorRule /@ colorIndDict;
  Return[permutationColorRuleDict];
];
ReplaceColorTableauxNumber[rule_] := # /. rule&;



(* ::Section:: *)
(*Step3 Reduce any YT to standard YT*)


defaultYTHead = IYT;
WarpTableauxWithHead[tableaux_List, head_] := head[tableaux];
WarpTableauxWithHead[head_] := WarpTableauxWithHead[#, head]&;
WarpTableauxWithHead[] := WarpTableauxWithHead[defaultYTHead];
ReduceSU3YT[tableaux_List, h_ : defaultYTHead] := ReduceSU3YT[WarpTableauxWithHead[tableaux, h], h];
ReduceSU3YT[constant_, h_ : defaultYTHead] /; NumberQ@constant := constant;
ReduceSU3YT[expr_Plus, h_ : defaultYTHead] := ReduceSU3YT[#, h]& /@ Sum2List[expr] // Total;
ReduceSU3YT[expr_Times, h_ : defaultYTHead] := Times @@ (ReduceSU3YT[#, h]& /@ Prod2List[expr]);
ReduceSU3YT[warpedTableaux_, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    Module[
      {n = Length@warpedTableaux[[1]][[1]], totalFactor, tableaux, reduceAllOnce, lastExpr, result},
      {totalFactor, tableaux} = (YTSortColumnsFirst[#, h]&) @ (YTSortColumnInner[#, h]&)@warpedTableaux;
      reduceAllOnce = tableaux;
      While[lastExpr =!= reduceAllOnce,
        lastExpr = reduceAllOnce;
        Do[
          reduceAllOnce = YTSU3RepeatedShortenId[reduceAllOnce, {column1, column2} , h] // Expand;,
          {column1, 1, n}, {column2, column1 + 1 , n}
        ];
      ];
      result = totalFactor * reduceAllOnce // Return;
    ];
YTSortColumnsFirst[constant_, h_ : defaultYTHead] /; NumberQ@constant := constant;
YTSortColumnsFirst[factoredTableaux_List, h_ : defaultYTHead] /; NumberQ@factoredTableaux[[1]] :=
    YTSortColumnsFirst[#, h]& /@ factoredTableaux;
YTSortColumnsFirst[tableaux_List] := Transpose@SortBy[Transpose@tableaux, First];
YTSortColumnsFirst[warpedTableaux_, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    h[ YTSortColumnsFirst[warpedTableaux[[1]]] ];
YTSortColumnInner[tableaux_List, columnNumbers_List] := Module[
  {tTableaux = Transpose@tableaux, factor = 1},
  Do[
    factor *= Signature[tTableaux[[c]]];
    tTableaux[[c]] = Sort[tTableaux[[c]]];
    , {c, columnNumbers}];
  Return[{factor, Transpose@tTableaux}];
];
YTSortColumnInner[tableaux_List] := YTSortColumnInner[tableaux, Range@Length@tableaux[[1]]];
YTSortColumnInner[{{}}] := {{}};
YTSortColumnInner[warpedTableaux_, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    {#[[1]], h@#[[2]]}&@YTSortColumnInner[warpedTableaux[[1]]];
YTSortColumnInner[warpedTableaux_, columnNumbers_List , h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    {#[[1]], h@#[[2]]}&@YTSortColumnInner[warpedTableaux[[1]], columnNumbers];
YTSortUseShortenId[warpedTableaux_, {column1_Integer, column2_Integer}, selectedReserve_Integer, h_ : defaultYTHead] /; Head@warpedTableaux === h :=
    YTSortUseShortenId[warpedTableaux[[1]], {column1, column2}, selectedReserve, h];
YTSortUseShortenId[tableaux_List, {column1_Integer, column2_Integer}, selectedReserve_Integer, h_ : defaultYTHead] := Module[
  {tTableaux = Transpose@tableaux, allPossibleTerms, allTableaux, factors, sortInnerResult},
  {factors, allPossibleTerms} = YTSortUseShortenId[tTableaux[[column1]], tTableaux[[column2]], selectedReserve];
  allTableaux = Transpose /@ MapThread[(tTableaux[[column1]] = #1;tTableaux[[column2]] = #2;tTableaux)&,
    Transpose @ allPossibleTerms];
  sortInnerResult = YTSortColumnInner[#, {column1, column2}]& /@ allTableaux // Transpose;
  MapThread[#1 * h[#2]&, {sortInnerResult[[1]] * factors, YTSortColumnsFirst /@ sortInnerResult[[2]]}] // Total //
      Return;
];
YTSortUseShortenId[column1List_List, column2List_List, selectedReserve_Integer] := Module[
  {leftTerms = Drop[column1List, {selectedReserve}],
    needPermutedTerms = Join[{column1List[[selectedReserve]]}, column2List], permuted,
    permutedResult, factors},
  If[Length@column1List != Length@column2List || Length@column1List < 2, Throw["Wrong shape"]];
  permuted = NestList[Permute[#, Cycles[{Range[Length@needPermutedTerms]}]] &, needPermutedTerms,
    Length@needPermutedTerms - 1][[2 ;; -1]];
  permutedResult = {leftTerms ~ Append ~ #[[1]], #[[2 ;; -1]]}& /@ permuted;
  factors = -1 * Signature[leftTerms ~ Append ~ column1List[[selectedReserve]]] * Signature[column1List]
      * Signature@needPermutedTerms * Signature /@ permuted;
  Return[{factors, permutedResult}];
];
YTSU3RepeatedShortenId[warpedTableaux_, {column1_Integer, column2_Integer}, h_ : defaultYTHead] := Module[
  {tTableaux = Transpose@warpedTableaux[[1]], a, b, c, d, e, f, temp, factors, exprs},
  {a, b, c} = tTableaux[[column1]];
  {d, e, f} = tTableaux[[column2]];
  If[b < e && c < f, Return[warpedTableaux]];
  If[b < e && c > f, Return@YTSortUseShortenId[warpedTableaux, {column1, column2}, 3, h]];
  If[b > e && c > f, Return@YTSortUseShortenId[warpedTableaux, {column1, column2}, 1, h]];
  If[b > e && c < f,
    temp = Prod2List /@ Sum2List@YTSortUseShortenId[warpedTableaux, {column1, column2}, 2, h];
    {factors, exprs} = If[Length@# == 1, {1} ~ Join ~ #, #]& /@ temp // Transpose;
    factors * (YTSU3RepeatedShortenId[#, {column1, column2}, h]& /@ exprs) // Total // Return;
  ];
];
YTSU3RepeatedShortenId[constant_, {column1_Integer, column2_Integer}, h_ : defaultYTHead] /; NumberQ@constant :=
    constant;
YTSU3RepeatedShortenId[expr_Plus, {column1_Integer, column2_Integer}, h_ : defaultYTHead] :=
    YTSU3RepeatedShortenId[#, {column1, column2}, h]& /@ Sum2List[expr] // Total;
YTSU3RepeatedShortenId[expr_Times, {column1_Integer, column2_Integer}, h_ : defaultYTHead] :=
    Times @@ (YTSU3RepeatedShortenId[#, {column1, column2}, h]& /@ Prod2List[expr]);

FindColorCor[warpedTableaux_List, warpedBasis_List] := FindColorCor[#, warpedBasis]& /@ warpedTableaux;
FindColorCor[warpedBasis_List] := FindColorCor[#, warpedBasis]&;
FindColorCor[warpedTableaux_, warpedBasis_List] := Coefficient[warpedTableaux, #] & /@ warpedBasis;



(* ::Section:: *)
(*Step4 Get Color Operators*)


GetColorIdenticalPermutedOperatorDict[identicalParticleLists_List, colorIndDict_Association, genCoorsByRule_] :=
    Module[{operatorDict, rules, coors, PFirst, PAll},
      operatorDict = Table[identicalParticleList -> Null, {identicalParticleList, identicalParticleLists}] // Association;
      Do[
        rules = GetPermuteColorIdenticalRules[identicalParticleList, colorIndDict];
        coors = genCoorsByRule /@ rules;
        PFirst = coors[[2]];
        PAll = coors[[-1]];
        operatorDict[identicalParticleList] = {
          1 -> IdentityMatrix[Length@coors[[-1]]],
          symPermuteFirst -> PFirst,
          symPermuteAll[-1 + Length@identicalParticleList] -> PAll
        } // DeleteDuplicates;
        , {identicalParticleList, identicalParticleLists}];
      Return[operatorDict];
    ];

GetColorInnerPermutedOperatorDict[colorIndDict_Association, genCoorsByRule_] :=
    Module[{operatorDict, allRules, rules, coors, PFirst, PAll},
      operatorDict = <||>;
      allRules = GetPermuteColorInnerRules[colorIndDict];
      Do[
        rules = allRules[coloredParticle];
        coors = genCoorsByRule /@ rules;
        If[Length@coors != 1,
          PFirst = coors[[2]];
          PAll = coors[[-1]];
          AssociateTo[operatorDict,
            coloredParticle -> {
              1 -> IdentityMatrix[Length@coors[[1]]],
              symPermuteFirst -> PFirst
            } ~ Join ~
                If[Length@colorIndDict[coloredParticle] > 2,
                  {symPermuteAll[Length@colorIndDict[coloredParticle]] -> PAll},
                  {}
                ]
          ]
        ];
        , {coloredParticle, Keys@colorIndDict}];
      Return[operatorDict];
    ];

GetProjectInnerColorOp[colorYTshapes_,colorIndDict_Association, <||>] := {{1}};
GetProjectInnerColorOp[colorYTshapes_,colorIndDict_Association, operatorDict_Association] := Module[
  {polyDict, yt, poly},
  polyDict = <||>;
  Do[
    yt = colorYTshapes[[particle]];
    (*By convention*)
    poly = GetPermutedPolyFromYT[yt] // First;
    AssociateTo[polyDict, particle -> poly];
    , {particle, Keys@operatorDict}];
    Dot @@ Table[polyDict[p] /. operatorDict[p], {p, Keys@polyDict}]// Return;
];


(* ::Section:: *)
(*Step5 Combine all*)


Options[AuxConstructIdenticalColorBasis] := {log -> False};
AuxConstructIdenticalColorBasis[su3ShapeList_, identicalParm_, h_, OptionsPattern[]] := Module[
  {colorYTshapes, colorIndDict, identicalList = {}, maxInd,
    colorBasis, rulesIdentical, rulesInnerDict, ParaFindRuleMatrix,
    ruleIdenticalCoorsDict,
    ruleInnerCoorsDict, colorIdenticalOpDict, colorInnerOpDict, independentPosList,
    projectionOp, proL, proR, metricInvG},
  If[Sort@Keys@su3ShapeDict =!=
      Sort@DeleteDuplicates[su3ShapeList ~ Join ~ Keys@su3ShapeDict],
    Print["No such SU3 type"]; Return[{}]];
  colorYTshapes=su3ShapeDict[#]& /@ su3ShapeList;
  colorIndDict = GetColorIndDict[colorYTshapes];
  Do[
    If[SubsetQ[Keys@colorIndDict, e[[;; -2]]],
      identicalList ~ AppendTo ~ e;
    ];
    , {e, identicalParm}];

  maxInd = colorIndDict // Values // Max;
  If[Mod[maxInd, 3] != 0, Throw["no SU3 singlet"]];
  colorBasis = WarpTableauxWithHead[h] /@ ConstructColorBasis[maxInd / 3];
  rulesIdentical = GetPermuteColorIdenticalRules[#, colorIndDict]& /@ identicalList // Flatten[#, 1]& //
      DeleteDuplicates;
  rulesInnerDict = GetPermuteColorInnerRules[colorIndDict];

  ParaFindRuleMatrix[paraRule_] := Map[
    FindColorCor[colorBasis]@ReduceSU3YT@#&,
    ReplaceColorTableauxNumber[paraRule] /@ colorBasis];
  ParaFindRuleMatrix[paraRule_, L_, R_, InvG_] := InvG . L . Map[
    ((FindColorCor[colorBasis]@ReduceSU3YT@#))&,
    ReplaceColorTableauxNumber[paraRule] /@ colorBasis
  ] . R;
  ParaFindRuleMatrix[{}] := IdentityMatrix[Length@colorBasis];
  ParaFindRuleMatrix[{}, L_, R_, InvG_] := IdentityMatrix[Length@InvG];

  ruleInnerCoorsDict = Table[
    rule -> ParaFindRuleMatrix[rule],
    {rule, rulesInnerDict // Values // Flatten[#, 1]& //
        DeleteDuplicates}] // Association
      // AbsoluteTiming // (If[OptionValue@log, LogPri["Reduce color projection cost ", #[[1]]]];#[[2]])&;

  (
    colorInnerOpDict = GetColorInnerPermutedOperatorDict[colorIndDict, ruleInnerCoorsDict[#]&];
    projectionOp = GetProjectInnerColorOp[colorYTshapes, colorIndDict, colorInnerOpDict];
    If[projectionOp==={{1}},projectionOp=IdentityMatrix[Length@colorBasis]];
    independentPosList = FindIndependentBasisPos[projectionOp];
    If[Length@independentPosList == 0, Return@{colorIndDict, {}, <||>}];
    proL = projectionOp[[independentPosList, ;;]];
    proR = Transpose @ proL;
    metricInvG = Inverse[proL . proR];
  ) // AbsoluteTiming // (If[OptionValue@log, LogPri["project color basis cost ", #[[1]]]];)&;

  ruleIdenticalCoorsDict = Table[
    rule -> ParaFindRuleMatrix[rule, proL, proR, metricInvG],
    {rule, rulesIdentical}] // Association
      // AbsoluteTiming // (If[OptionValue@log, LogPri["Reduce color identical cost ", #[[1]]]];#[[2]])&;

  colorIdenticalOpDict = GetColorIdenticalPermutedOperatorDict[identicalList, colorIndDict,
    ruleIdenticalCoorsDict[#]&];

  Return[{colorIndDict, colorBasis[[independentPosList]], colorIdenticalOpDict}]
];

(* ::Section:: *)
(*Trace-basis SU(3) flavor invariants*)

ClearAll[
  TrX, checkCanoicalTrX, CanonicalizeTrace, CanonicalizeMonomial,
  GeneratePhysicalBasis1, GeneratePhysicalBasis, GetCoreCHOperator,
  GetSchoutenMatrixOp, GenerateTypeAAccumulation, GenerateTypeBDoubleCH,
  GenerateTypeCScalarProduct, GenerateTypeDMatrixSchouten, GetRawCHMatrix,
  ToWord, TrW, FTraceId, SetPartitionsK, HoldWord,
  GroupInto4UnlabeledOrdered, Pick4SinglesHoldWithRestTr, ApplyFOnGroupings,
  WeightedFTraceFromGroupingList, WeightedFTraceFromElems, Dtype,
  BasisDoubleDF2, DoubleDFCheck, BasisSingleDF2, SingleDFCheck,
  BasisSingleDD, SingleDD, BasisDoubleDD, DoubleDD,
  ApplyP10bar, ApplyP101bar, ApplyP10, ApplyP101, P10Op, P10Opbar,
  P10Matrix, P10barMatrix, genPerm, PIdentityPatricle,
  PIdentityPatricleMatrix, AssignSU3Indices, ConstructSU3Tr,
  ConstructSU3TrCached, ClearConstructSU3TrCache
];

CanonicalizeTrace[cycle_List] := RotateLeft[cycle, FirstPosition[cycle, Min[cycle]][[1]] - 1];
CanonicalizeMonomial[cycles_List] := SortBy[CanonicalizeTrace /@ cycles, {Length, Identity}];

GeneratePhysicalBasis1[n_Integer] := Module[
  {perms, rawCycles, validStructure, finalBasis},
  perms = Permutations[Range[n]];
  rawCycles = Apply[List, #][[1]] & /@ (PermutationCycles /@ perms);
  validStructure = Select[rawCycles, AllTrue[#, Length[#] >= 2 &] &];
  validStructure = Select[validStructure, Total[Length /@ #] == n &];
  finalBasis = DeleteDuplicates[CanonicalizeMonomial /@ validStructure];
  Times @@ (TrX @@@ #) & /@ finalBasis
];

GeneratePhysicalBasis[n_Integer] := Module[
  {perms, rawCycles, validStructure},
  perms = Permutations[Range[n]];
  rawCycles = Apply[List, #][[1]] & /@ (PermutationCycles /@ perms);
  validStructure = Select[rawCycles, AllTrue[#, Length[#] >= 2 &] &];
  validStructure = Select[validStructure, Total[Length /@ #] == n &];
  DeleteDuplicates[CanonicalizeMonomial /@ validStructure]
];

GetCoreCHOperator[a_, b_, c_] := Module[{lhs, rhs},
  lhs = Map[{1, #, {}} &, Permutations[{a, b, c}]];
  rhs = {
    {-1, {a}, {{b, c}}},
    {-1, {b}, {{a, c}}},
    {-1, {c}, {{a, b}}},
    {-1, {}, {{a, b, c}}},
    {-1, {}, {{a, c, b}}}
  };
  Join[lhs, rhs]
];

GetSchoutenMatrixOp[a_, b_, c_, d_] :=
  ({Signature[#], #, {}} & /@ Permutations[{a, b, c, d}]);

GenerateTypeAAccumulation[n_Integer] := Module[
  {constraints = {}, subsets, others, coreOp, currentEq, finalEq, particle, side},
  subsets = Subsets[Range[n], {3}];
  Do[
    others = Complement[Range[n], sub];
    coreOp = GetCoreCHOperator @@ sub;
    Do[
      Do[
        currentEq = coreOp;
        Do[
          particle = p[[i]];
          side = pat[[i]];
          currentEq = Map[
            {#[[1]], If[side == 0, Join[{particle}, #[[2]]], Join[#[[2]], {particle}]], #[[3]]} &,
            currentEq
          ],
          {i, Length[p]}
        ];
        finalEq = Map[
          If[Length[#[[2]]] > 0,
            {#[[1]], CanonicalizeMonomial[Append[#[[3]], #[[2]]]]},
            {#[[1]]*3, CanonicalizeMonomial[#[[3]]]}
          ] &,
          currentEq
        ];
        AppendTo[constraints, ({Total[#[[All, 1]]], #[[1, 2]]} & /@ GatherBy[finalEq, Last])],
        {pat, Tuples[{0, 1}, Length[others]]}
      ],
      {p, Permutations[others]}
    ],
    {sub, subsets}
  ];
  constraints
];

GenerateTypeBDoubleCH[n_Integer] := Module[
  {constraints = {}, subsets, set1, set2, op1, op2, combinedEq},
  If[n >= 6,
    subsets = Subsets[Range[n], {3}];
    Do[
      set1 = sub;
      set2 = Complement[Range[n], sub];
      If[Length[set2] == 3,
        op1 = GetCoreCHOperator @@ set1;
        op2 = GetCoreCHOperator @@ set2;
        combinedEq = Flatten[
          Table[
            Module[{cNew = t1[[1]]*t2[[1]], mNew = Join[t1[[2]], t2[[2]]],
              sNew = Join[t1[[3]], t2[[3]]]},
              If[Length[mNew] > 0,
                {cNew, CanonicalizeMonomial[Append[sNew, mNew]]},
                {cNew*3, CanonicalizeMonomial[sNew]}
              ]
            ],
            {t1, op1}, {t2, op2}
          ],
          1
        ];
        AppendTo[constraints, ({Total[#[[All, 1]]], #[[1, 2]]} & /@ GatherBy[combinedEq, Last])];
        combinedEq = Flatten[
          Table[
            Module[{cNew = t2[[1]]*t1[[1]], mNew = Join[t2[[2]], t1[[2]]],
              sNew = Join[t2[[3]], t1[[3]]]},
              If[Length[mNew] > 0,
                {cNew, CanonicalizeMonomial[Append[sNew, mNew]]},
                {cNew*3, CanonicalizeMonomial[sNew]}
              ]
            ],
            {t2, op2}, {t1, op1}
          ],
          1
        ];
        AppendTo[constraints, ({Total[#[[All, 1]]], #[[1, 2]]} & /@ GatherBy[combinedEq, Last])]
      ],
      {sub, subsets}
    ]
  ];
  constraints
];

GenerateTypeCScalarProduct[n_Integer] := Module[
  {constraints = {}, subsets4, setRest, sub3, d, scalarPart, traceRest, finalEq},
  If[n >= 4,
    subsets4 = Subsets[Range[n], {4}];
    Do[
      setRest = Complement[Range[n], sub];
      traceRest = If[Length[setRest] > 0, CanonicalizeTrace[setRest], {}];
      Do[
        sub3 = take;
        d = Complement[sub, sub3][[1]];
        scalarPart = Map[
          {#[[1]], CanonicalizeMonomial[Append[#[[3]], Join[#[[2]], {d}]]]} &,
          GetCoreCHOperator @@ sub3
        ];
        finalEq = Map[
          {#[[1]], CanonicalizeMonomial[If[Length[traceRest] > 0, Append[#[[2]], traceRest], #[[2]]]]} &,
          scalarPart
        ];
        AppendTo[constraints, ({Total[#[[All, 1]]], #[[1, 2]]} & /@ GatherBy[finalEq, Last])],
        {take, Subsets[sub, {3}]}
      ],
      {sub, subsets4}
    ]
  ];
  constraints
];

GenerateTypeDMatrixSchouten[n_Integer] := Module[
  {constraints = {}, subsets, others, coreOp, currentEq, finalEq, particle, side},
  If[n == 6,
    subsets = Subsets[Range[n], {4}];
    Do[
      others = Complement[Range[n], sub];
      coreOp = GetSchoutenMatrixOp @@ sub;
      Do[
        Do[
          currentEq = coreOp;
          Do[
            particle = p[[i]];
            side = pat[[i]];
            currentEq = Map[
              {#[[1]], If[side == 0, Join[{particle}, #[[2]]], Join[#[[2]], {particle}]], #[[3]]} &,
              currentEq
            ],
            {i, Length[p]}
          ];
          finalEq = Map[
            If[Length[#[[2]]] > 0,
              {#[[1]], CanonicalizeMonomial[Append[#[[3]], #[[2]]]]},
              {#[[1]]*3, CanonicalizeMonomial[#[[3]]]}
            ] &,
            currentEq
          ];
          AppendTo[constraints, ({Total[#[[All, 1]]], #[[1, 2]]} & /@ GatherBy[finalEq, Last])],
          {pat, Tuples[{0, 1}, Length[others]]}
        ],
        {p, Permutations[others]}
      ],
      {sub, subsets}
    ]
  ];
  constraints
];

SetAttributes[ToWord, HoldAll];
ToWord[h_] := Flatten@{ReleaseHold[h]};
SetAttributes[TrW, HoldAll];
TrW[hs__] := TrX @@ Flatten[ToWord /@ {hs}];

SetAttributes[FTraceId, HoldAll];
FTraceId[Ah_, Bh_, Ch_, Dh_] := Module[
  {tA, tB, tC, tD, tAB, tAC, tAD, tBC, tBD, tCD, tABC, tACB, tABD,
    tADB, tACD, tADC, tBCD, tBDC, tABCD, tABDC, tACBD, tACDB, tADBC, tADCB},
  tA = TrW[Ah]; tB = TrW[Bh]; tC = TrW[Ch]; tD = TrW[Dh];
  tAB = TrW[Ah, Bh]; tAC = TrW[Ah, Ch]; tAD = TrW[Ah, Dh];
  tBC = TrW[Bh, Ch]; tBD = TrW[Bh, Dh]; tCD = TrW[Ch, Dh];
  tABC = TrW[Ah, Bh, Ch]; tACB = TrW[Ah, Ch, Bh];
  tABD = TrW[Ah, Bh, Dh]; tADB = TrW[Ah, Dh, Bh];
  tACD = TrW[Ah, Ch, Dh]; tADC = TrW[Ah, Dh, Ch];
  tBCD = TrW[Bh, Ch, Dh]; tBDC = TrW[Bh, Dh, Ch];
  tABCD = TrW[Ah, Bh, Ch, Dh]; tABDC = TrW[Ah, Bh, Dh, Ch];
  tACBD = TrW[Ah, Ch, Bh, Dh]; tACDB = TrW[Ah, Ch, Dh, Bh];
  tADBC = TrW[Ah, Dh, Bh, Ch]; tADCB = TrW[Ah, Dh, Ch, Bh];
  tA tB tC tD - (tAB tC tD + tAC tB tD + tAD tB tC + tBC tA tD + tBD tA tC + tCD tA tB) +
    (tAB tCD + tAC tBD + tAD tBC) +
    (tABC tD + tACB tD + tABD tC + tADB tC + tACD tB + tADC tB + tBCD tA + tBDC tA) -
    (tABCD + tABDC + tACBD + tACDB + tADBC + tADCB)
];

SetPartitionsK[set_List, k_Integer?Positive] := Module[{n = Length[set], first, rest},
  If[k == 1, Return[{{set}}]];
  If[n < k, Return[{}]];
  first = First[set]; rest = Rest[set];
  Flatten[
    Table[
      With[{choices = Subsets[rest, {s - 1}]},
        Table[
          With[{block = Join[{first}, choice], remaining = Complement[set, Join[{first}, choice]]},
            Join[{block}, #] & /@ SetPartitionsK[remaining, k - 1]
          ],
          {choice, choices}
        ]
      ],
      {s, 1, n - k + 1}
    ],
    2
  ]
];

HoldWord[list_List] /; list =!= {} := Hold @@ list;

GroupInto4UnlabeledOrdered[elems_List] := Module[{parts, expanded},
  If[Length[elems] < 4, Return[{}]];
  parts = SetPartitionsK[elems, 4];
  expanded = Flatten[Tuples[Permutations /@ #] & /@ parts, 1];
  (HoldWord /@ #) & /@ DeleteDuplicates[SortBy[#, {Length, Identity}] & /@ expanded]
];

Pick4SinglesHoldWithRestTr[elems_List] := Module[{subs},
  subs = Subsets[elems, {4}];
  Table[
    With[{rest = Select[elems, FreeQ[s, #] &]},
      {Sequence @@ (Hold /@ s), If[rest === {}, 1, TrX @@ rest]}
    ],
    {s, subs}
  ]
];

ApplyFOnGroupings[elems_List] := FTraceId @@@ GroupInto4UnlabeledOrdered[elems];
WeightedFTraceFromGroupingList[groupings_List] :=
  Map[# [[5]]*(FTraceId @@ #[[1 ;; 4]]) &, groupings];
WeightedFTraceFromElems[elems_List] := WeightedFTraceFromGroupingList @ Pick4SinglesHoldWithRestTr[elems];

Dtype[n_Integer] := Module[{n1, g1, g2, g3, c1},
  n1 = Range[n];
  c1 = GeneratePhysicalBasis1[n];
  g1 = ApplyFOnGroupings[n1];
  g2 = WeightedFTraceFromElems[n1];
  g3 = Join[g1, g2] // Expand;
  Table[Coefficient[g3[[i]], c1], {i, Length[g3]}]
];

GetRawCHMatrix[n_Integer] := Module[
  {basis, constraints, constraintMatrix = {}, rowVec, pos},
  basis = GeneratePhysicalBasis[n];
  constraints = Join[GenerateTypeAAccumulation[n], GenerateTypeBDoubleCH[n], GenerateTypeCScalarProduct[n]];
  Do[
    rowVec = ConstantArray[0, Length[basis]];
    Do[
      If[NoneTrue[term[[2]], Length[#] == 1 &],
        pos = Position[basis, term[[2]]];
        If[Length[pos] > 0, rowVec[[pos[[1, 1]]]] += term[[1]]]
      ],
      {term, eq}
    ];
    If[AnyTrue[rowVec, # != 0 &], AppendTo[constraintMatrix, rowVec]],
    {eq, constraints}
  ];
  {basis, Join[constraintMatrix, Dtype[n]]}
];

checkCanoicalTrX[a_, b__] := (a /. (e_List :> First@e)) < Min[Hold[b] /. e_List :> First@e // ReleaseHold];
TrX[x_] := 0;
TrX[a_, b__] /; ! checkCanoicalTrX[a, b] := Module[{current = {a, b}, canonical},
  canonical = SelectFirst[checkCanoicalTrX @@ # &] @ Table[RotateLeft[current, i], {i, Length[current]}];
  TrX @@ canonical
];
TrX /: TrX[l___, Commutator[a_, b_], r___] := TrX[l, a, b, r] - TrX[l, b, a, r];
TrX /: TrX[l___, AntiCommutator[a_, b_], r___] := TrX[l, a, b, r] + TrX[l, b, a, r];
TrX[Identity] := 3;
TrX[l__, Identity, r___] := TrX[l, r];
TrX[l___, Identity, r__] := TrX[l, r];

BasisDoubleDF2[A_, B_, X_, Y_] := Expand[
  (I/2) (TrX[B, X // ReleaseHold, A, Y // ReleaseHold] - TrX[A, X // ReleaseHold, B, Y // ReleaseHold]) +
    (I/2) (TrX[B, A, X // ReleaseHold, Y // ReleaseHold] - TrX[A, B, Y // ReleaseHold, X // ReleaseHold]) +
    (I/3) TrX[X // ReleaseHold] TrX[Commutator[A, B], Y // ReleaseHold]
];

DoubleDFCheck[Amp_, Pos_] := Module[{amp, A1, B1, X1, Y1, c0},
  amp = If[
    MatchQ[Amp, c___*TrX[a1___, Pos[[1]], c1___] TrX[b1___, Pos[[2]], d1___]],
    Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> {Pos[[1]], Pos[[1]]}, Pos[[2]] -> {Pos[[2]], Pos[[2]]}}),
    Return[0]
  ];
  {c0, A1, B1, X1, Y1} = amp /. (c___*TrX[l1___, {T1_, Pos[[1]]}, r1___] TrX[l2___, {T2_, Pos[[2]]}, r2___]) :>
    {c // Times, T1, T2, If[Length[{r1, l1}] == 0, Identity, Hold@Sequence[r1, l1]],
      If[Length[{r2, l2}] == 0, Identity, Hold@Sequence[r2, l2]]};
  {c0, A1, B1, X1, Y1}
];

BasisSingleDF2[A_, B_, X_, Y_] := Expand[
  -I/2 TrX[X // ReleaseHold] TrX[A, B, Y // ReleaseHold] +
    I/2 TrX[Y // ReleaseHold] TrX[B, A, X // ReleaseHold] -
    I/2 TrX[A, X // ReleaseHold] TrX[B, Y // ReleaseHold] +
    I/2 TrX[B, X // ReleaseHold] TrX[A, Y // ReleaseHold] +
    I/3 TrX[X // ReleaseHold, Commutator[A, B], Y // ReleaseHold]
];

SingleDFCheck[Amp_, Pos_] := Module[{amp, A1, B1, X1, Y1, c0},
  amp = If[
    MatchQ[Amp, c_. TrX[a1___, Pos[[1]], c1___, Pos[[2]], d1___] |
      c_. TrX[a1___, Pos[[2]], c1___, Pos[[1]], d1___]],
    Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> {Pos[[1]], Pos[[1]]}, Pos[[2]] -> {Pos[[2]], Pos[[2]]}}),
    Return[0]
  ];
  {c0, A1, B1, X1, Y1} = amp /.
    cc_. TrX[l___, {T1_, Pos[[1]]}, m___, {T2_, Pos[[2]]}, r___] :>
      {cc, T1, T2, If[Length[{m}] == 0, Identity, Hold@Sequence[m]],
        If[Length[{r, l}] == 0, Identity, Hold@Sequence[r, l]]} /.
    cc_. TrX[l___, {T2_, Pos[[2]]}, m___, {T1_, Pos[[1]]}, r___] :>
      {cc, T1, T2, If[Length[{r, l}] == 0, Identity, Hold@Sequence[r, l]],
        If[Length[{m}] == 0, Identity, Hold@Sequence[m]]};
  {c0, A1, B1, X1, Y1}
];

BasisSingleDD[A_, B_, X_, Y_] := Expand[
  1/2 (TrX[A, X // ReleaseHold] TrX[B, Y // ReleaseHold] + TrX[B, X // ReleaseHold] TrX[A, Y // ReleaseHold]) +
    1/2 (TrX[X // ReleaseHold] TrX[A, B, Y // ReleaseHold] + TrX[Y // ReleaseHold] TrX[B, A, X // ReleaseHold]) -
    1/3 TrX[AntiCommutator[A, B], AntiCommutator[X, Y]] -
    2/3 TrX[A, X // ReleaseHold, B, Y // ReleaseHold] +
    2/9 TrX[A, B] TrX[X // ReleaseHold, Y // ReleaseHold]
];

SingleDD[Amp_, Pos_] := Module[{amp, A1, B1, X1, Y1, c0},
  amp = If[
    MatchQ[Amp, c1_. TrX[a1___, Pos[[1]], e1___, Pos[[2]], d1___] |
      c1_. TrX[a1___, Pos[[2]], e1___, Pos[[1]], d1___]],
    Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> {Pos[[1]], Pos[[1]]}, Pos[[2]] -> {Pos[[2]], Pos[[2]]}}),
    Return[0]
  ];
  {c0, A1, B1, X1, Y1} = amp /.
    cc_. TrX[l___, {T1_, Pos[[1]]}, m___, {T2_, Pos[[2]]}, r___] :>
      {cc // Times, T1, T2, If[Length[{m}] == 0, Identity, Hold@Sequence[m]],
        If[Length[{r, l}] == 0, Identity, Hold@Sequence[r, l]]} /.
    cc_. TrX[l___, {T2_, Pos[[2]]}, m___, {T1_, Pos[[1]]}, r___] :>
      {cc, T1, T2, If[Length[{r, l}] == 0, Identity, Hold@Sequence[r, l]],
        If[Length[{m}] == 0, Identity, Hold@Sequence[m]]};
  c0*BasisSingleDD[A1, B1, X1, Y1]
];

BasisDoubleDD[A_, B_, X_, Y_] := Expand[
  1/2 TrX[AntiCommutator[A, X], AntiCommutator[B, Y]] -
    1/3 TrX[AntiCommutator[A, B], X // ReleaseHold] TrX[Y // ReleaseHold] -
    1/3 TrX[AntiCommutator[B, A], Y] TrX[X // ReleaseHold] -
    2/3 TrX[A, X // ReleaseHold] TrX[B, Y // ReleaseHold] +
    2/9 TrX[Y // ReleaseHold] TrX[X // ReleaseHold] TrX[A, B]
];

DoubleDD[Amp_, Pos_] := Module[{amp, A1, B1, X1, Y1, c0},
  amp = If[
    MatchQ[Amp, c_. TrX[a1___, Pos[[1]], c1___] TrX[b1___, Pos[[2]], d1___]],
    Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> {Pos[[1]], Pos[[1]]}, Pos[[2]] -> {Pos[[2]], Pos[[2]]}}),
    Return[0]
  ];
  {c0, A1, B1, X1, Y1} = amp /. (c___*TrX[l1___, {T1_, Pos[[1]]}, r1___] TrX[l2___, {T2_, Pos[[2]]}, r2___]) :>
    {c // Times, T1, T2, If[Length[{r1, l1}] == 0, Identity, Hold@Sequence[r1, l1]],
      If[Length[{r2, l2}] == 0, Identity, Hold@Sequence[r2, l2]]};
  Expand[c0*BasisDoubleDD[A1, B1, X1, Y1]]
];

ApplyP10bar[Amp_, Pos_] := Module[{c1, A, B, X, Y, DD, DF, ID},
  {c1, A, B, X, Y} = DoubleDFCheck[Amp, Pos];
  DD = (-1/6) ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) -
      ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) /.
        HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})));
  DF = (I/4) (BasisDoubleDF2[A, B, X, Y] + BasisDoubleDF2[B, A, Y, X])*c1;
  ID = (Amp - (Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})))*(5/36);
  DD + ID + DF
];

ApplyP101bar[Amp_, Pos_] := Module[{c1, A, B, X, Y, DD, DF, ID},
  {c1, A, B, X, Y} = SingleDFCheck[Amp, Pos];
  DD = (-1/6) ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) -
      ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) /.
        HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})));
  DF = (I/4) (BasisSingleDF2[A, B, X, Y] + BasisSingleDF2[B, A, Y, X])*c1;
  ID = (Amp - (Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})))*(5/36);
  DD + ID + DF
];

ApplyP10[Amp_, Pos_] := Module[{c1, A, B, X, Y, DD, DF, ID},
  {c1, A, B, X, Y} = DoubleDFCheck[Amp, Pos];
  DD = (-1/6) ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) -
      ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) /.
        HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})));
  DF = (-I/4) (BasisDoubleDF2[A, B, X, Y] + BasisDoubleDF2[B, A, Y, X])*c1;
  ID = (Amp - (Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})))*(5/36);
  DD + ID + DF
];

ApplyP101[Amp_, Pos_] := Module[{c1, A, B, X, Y, DD, DF, ID},
  {c1, A, B, X, Y} = SingleDFCheck[Amp, Pos];
  DD = (-1/6) ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) -
      ((DoubleDD[Amp, Pos] + SingleDD[Amp, Pos]) /.
        HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})));
  DF = (-I/4) (BasisSingleDF2[A, B, X, Y] + BasisSingleDF2[B, A, Y, X])*c1;
  ID = (Amp - (Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. {Pos[[1]] -> Pos[[2]], Pos[[2]] -> Pos[[1]]})))*(5/36);
  DD + ID + DF
];

P10Op[Amp_, Pos_] := If[
  MatchQ[Amp, c1_. TrX[a1___, Pos[[1]], e1___, Pos[[2]], d1___] |
    c1_. TrX[a1___, Pos[[2]], e1___, Pos[[1]], d1___]],
  ApplyP101[Amp, Pos],
  ApplyP10[Amp, Pos]
];

P10Opbar[Amp_, Pos_] := If[
  MatchQ[Amp, c1_. TrX[a1___, Pos[[1]], e1___, Pos[[2]], d1___] |
    c1_. TrX[a1___, Pos[[2]], e1___, Pos[[1]], d1___]],
  ApplyP101bar[Amp, Pos],
  ApplyP10bar[Amp, Pos]
];

P10Matrix[Basis_List, Pos_] := Module[{pj},
  pj = P10Op[#, Pos] & /@ Basis;
  Table[Coefficient[pj[[i]], Basis], {i, Length[Basis]}]
];

P10barMatrix[Basis_List, Pos_] := Module[{pj},
  pj = P10Opbar[#, Pos] & /@ Basis;
  Table[Coefficient[pj[[i]], Basis], {i, Length[Basis]}]
];

genPerm[list_List] := Switch[
  Length[list],
  2, {Reverse[list]},
  3, {RotateRight[list]},
  _, Message[genPerm::len, list]; $Failed
];

PIdentityPatricle[Amp_, IdPos_] := Module[{rules, perm},
  perm = genPerm[IdPos];
  rules = Thread[IdPos :> #] & /@ perm;
  Expand @ Total[
    Table[
      Amp /. HoldPattern[TrX[a___]] :> TrX @@ ({a} /. rules[[i]]),
      {i, Length[rules]}
    ]
  ]
];

PIdentityPatricleMatrix[Basis_List, IdPos_] := Module[{pj},
  pj = PIdentityPatricle[#, IdPos] & /@ Basis;
  Table[Coefficient[pj[[i]], Basis], {i, Length[Basis]}]
];

AssignSU3Indices[inputList_List] := Module[
  {currentIdx = 1, occupancy, fullResult, particleToSlots, singletPositions},
  occupancy = <|"10" -> 2, "10bar" -> 2, "8" -> 1, "1" -> 0|>;
  particleToSlots = Table[
    Module[{count, indices},
      count = Lookup[occupancy, inputList[[i]], 0];
      indices = Range[currentIdx, currentIdx + count - 1];
      currentIdx += count;
      indices
    ],
    {i, Length[inputList]}
  ];
  fullResult = Cases[Transpose[{inputList, particleToSlots}], {rep : ("10" | "10bar"), slots_} :> {rep, slots}];
  singletPositions = Flatten @ Position[inputList, "1"];
  <|
    "DecupletStructures" -> fullResult,
    "OctetSlotLength" -> currentIdx - 1,
    "ParticleToSlots" -> particleToSlots,
    "SingletPositions" -> singletPositions
  |>
];

ConstructSU3Tr::mixedsinglet =
  "Identical group `1` mixes SU(3) singlet and non-singlet particles; this is not a valid flavor-identical group.";
ConstructSU3Tr::unsupported =
  "ConstructSU3Tr supports SU(3) representations 1, 8, 10 and 10bar, but received `1`.";

ConstructSU3Tr[su3list_, IdenList_] := Module[
  {normalizedSU3List, Basis1, length, structure, parsed, CH, CHSpace, PCH, Mat, P10,
    tolerance = 10^-8, eigenvals, eigenvecs, singlets, pos, PTrans, singlets0, IDen,
    PID1, PIDNew, IndexOccupa, PIDGeneratorKeys, WrapPIDNewAsAssociation, PIDNewAssoc,
    TakeBlocksJoinByIndex, NormalizeIdenInput, idenlist, InvG, CH10, particleToSlots,
    singletPositions, singletFactor, projectedPID, rawIdenList},

  normalizedSU3List = Replace[su3list, {"g" -> "8", "" -> "1", 1 -> "1", 8 -> "8"}, {1}];
  If[! AllTrue[normalizedSU3List, MemberQ[{"1", "8", "10", "10bar"}, #] &],
    Message[ConstructSU3Tr::unsupported, normalizedSU3List];
    Return[$Failed]
  ];

  parsed = AssignSU3Indices[normalizedSU3List];
  structure = parsed["DecupletStructures"];
  length = parsed["OctetSlotLength"];
  particleToSlots = parsed["ParticleToSlots"];
  singletPositions = parsed["SingletPositions"];

  PIDGeneratorKeys[n_Integer] := Join[
    {1},
    If[n >= 2, {symPermuteFirst}, {}],
    If[n >= 3, Table[symPermuteAll[k], {k, 3, n}], {}]
  ];

  WrapPIDNewAsAssociation[iden_, pid_List] := Module[{keys, values, dim},
    If[iden === {} || pid === {} || pid === Null, Return[<||>]];
    keys = PIDGeneratorKeys[Length[iden]];
    values = pid;
    If[Length[values] < Length[keys] && Length[values] > 0,
      dim = Length[values[[1]]];
      values = Join[values, Table[IdentityMatrix[dim], {Length[keys] - Length[values]}]]
    ];
    <|Join[iden, {"S"}] -> Thread[keys -> Take[values, UpTo[Length[keys]]]]|>
  ];

  IndexOccupa = particleToSlots;
  TakeBlocksJoinByIndex[J_List, idx_List] := Join @@ J[[idx]];
  NormalizeIdenInput[id_] := Which[
    id === {}, {},
    MatchQ[id, {__Integer}], id,
    MatchQ[id, {{__Integer}}], First[id],
    True, id
  ];

  rawIdenList = NormalizeIdenInput[IdenList];
  idenlist = If[rawIdenList === {}, {}, TakeBlocksJoinByIndex[IndexOccupa, rawIdenList]];
  If[rawIdenList =!= {} && idenlist =!= {} && Length[idenlist] < Length[rawIdenList],
    Message[ConstructSU3Tr::mixedsinglet, rawIdenList];
    Return[$Failed]
  ];
  IDen = If[Length[idenlist] == 2 || Length[idenlist] == 0, {idenlist}, {Drop[idenlist, {3}], idenlist}];

  Basis1 = Switch[
    length,
    0 | 1, {1},
    2, {TrX[1, 2]},
    3, {TrX[1, 2, 3], TrX[1, 3, 2]},
    _, GeneratePhysicalBasis1[length]
  ];

  PCH = If[
    length <= 3,
    IdentityMatrix[Length[Basis1]],
    CH = GetRawCHMatrix[length][[2]];
    CHSpace = Orthogonalize[NullSpace[CH]];
    Transpose[CHSpace].CHSpace
  ];

  PID1 = If[
    rawIdenList === {},
    Null,
    If[
      idenlist === {},
      Table[IdentityMatrix[Length[Basis1]], {1}],
      Table[PIdentityPatricleMatrix[Basis1, IDen[[i]]], {i, Length[IDen]}]
    ]
  ];

  P10 = structure /. {{"10", list1_} :> P10Matrix[Basis1, list1], {"10bar", list2_} :> P10barMatrix[Basis1, list2]};
  Mat = Dot @@ DeleteCases[Join[{PCH}, P10], Null];

  {eigenvals, eigenvecs} = Eigensystem[N[Mat]];
  pos = Position[eigenvals, x_ /; Abs[x - 1] < tolerance];
  If[Length[pos] == 0, Return[$Failed]];

  singlets0 = RowReduce[Chop[Normalize /@ eigenvecs[[Flatten[pos]]], tolerance]];
  CH10 = Orthogonalize[Normalize /@ eigenvecs[[Flatten[pos]]]];
  Mat = Transpose[CH10].CH10;

  singlets = Basis1[[FindIndependentBasisPos[Transpose[singlets0]]]];
  singletFactor = Times @@ (TrS /@ singletPositions);
  singlets = Expand[singletFactor #] & /@ singlets;

  PTrans = If[idenlist === {}, {}, Mat[[FindIndependentBasisPos[Transpose[singlets0]]]]];
  InvG = If[PTrans === {}, {}, Inverse[PTrans.Transpose[PTrans]]];
  projectedPID = If[
    rawIdenList =!= {} && idenlist === {},
    Table[IdentityMatrix[Length[singlets]], {Max[Length[PIDGeneratorKeys[Length[rawIdenList]]] - 1, 0]}],
    If[PTrans === {}, {}, Table[Rationalize[InvG.PTrans.PID1[[i]].Transpose[PTrans], tolerance], {i, Length[IDen]}]]
  ];
  PIDNew = If[rawIdenList === {}, {IdentityMatrix[Length[singlets]]}, Join[{IdentityMatrix[Length[singlets]]}, projectedPID]];
  PIDNewAssoc = WrapPIDNewAsAssociation[rawIdenList, PIDNew];

  {IndexOccupa, singlets, PIDNewAssoc}
];

$ConstructSU3TrCache = <||>;
ConstructSU3TrCached[su3list_, IdenList_] := Module[{key = HoldComplete[su3list, IdenList]},
  If[KeyExistsQ[$ConstructSU3TrCache, key],
    $ConstructSU3TrCache[key],
    $ConstructSU3TrCache[key] = ConstructSU3Tr[su3list, IdenList]
  ]
];
ClearConstructSU3TrCache[] := ($ConstructSU3TrCache = <||>;);
