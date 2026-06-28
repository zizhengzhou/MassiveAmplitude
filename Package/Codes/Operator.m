(* ::Package:: *)

LogPri["Operator Loaded"];



(* ::Subsection:: *)
(*Amp2BrasList*)


Amp2BrasList[amp_] :=
    Module[ {factor, totalFactor = 1, bras},
      {factor, bras} = GroupBy[Prod2List@amp, MatchQ[_sb | _ab]][#]& /@ {False, True};
      If[!ListQ[factor], factor = {}];
      totalFactor = Times @@ factor;
      {bras, factor} = # /. Times[c_, b_ab | b_sb] :> (Sow[c];b)& /@ bras // Reap;
      totalFactor *= Times @@ Flatten @ factor;
      Return[{totalFactor, bras}]
    ];
BreakBracket[bra_] := {bra[[0]], bra[[1]], bra[[2]]};
(*Free sb = spin*2-antispinor*)
(*Free ab = antispinor*)
(*TODO change massless dealing*)
Options[Amp2MetaInfo] = {mass -> All};
Amp2MetaInfo[amp_, np_Integer, OptionsPattern[]] := Module[
  {masses, rule, braList , fun, particleList, massiveParticleList, spins, antispinors},
  masses = MassOption[OptionValue@mass, np];
  braList = BreakBracket /@ Amp2BrasList[amp][[2]];
  rule[type_, ind_] := {type, ind, _} | {type, _, ind};
  particleList = Table[{Count[braList, rule[sb, i]] , Count[braList, rule[ab, i]]}, {i, np}];
  massiveParticleList = Table[Count[braList, rule[sb, i]], {i, Range[2 * np, np + 1, -1]}];
  fun[particleList : {nSb_, nAb_}, nMassive_, thisMass_] :=
      If[thisMass === 0,
        {(nSb - nAb) / 2, 0},
        {(nMassive + nAb - nSb) / 2, nAb - nSb}
      ];
  {spins, antispinors} = Transpose@MapThread[fun, {particleList, massiveParticleList, masses}];
  If[Count[spins, Negative] + Count[antispinors, Negative] > 0, Return[Null]];
  Return[{spins , antispinors}];
];



(* ::Subsection:: *)
(*FindPsiChain*)


Options[FindPsiChain] = {mass -> All};
FindPsiChain[amp_, np_Integer, OptionsPattern[]] := Module[
  {
    masses, GenLeftExternalNumber, PopStack, EmptyStackQ,
    spins, antispinors,
    extSbStack, extAbStack,
    FindNextHeadTarget, ExistNextTargetQ, ConsumeNextTarget, ExtendChainStep,
    FactorMatchQ,
    target, targetParticle = Null, targetBraType = Null,
    targetParticle2 = Null, targetBraType2 = Null,
    circleHead,
    chains = {},
    bras, factor, sigmas
  },
  masses = MassOption[OptionValue@mass, np];
  {factor, bras} = Amp2BrasList[amp];
  {spins, antispinors} = Amp2MetaInfo[amp, np, mass -> OptionValue@mass];
  bras = BreakBracket /@ bras;
  If[Length@bras < 2,
    Return[{factor, {Append[bras[[1]], bras[[1]][[1]]]}, {1}}];
  ];
  FactorMatchQ[bra_, matchrule_] :=
      If[ MatchQ[bra, matchrule],
        True,
        If[ MatchQ[{bra[[1]], bra[[3]], bra[[2]]}, matchrule],
          Sow[-1];
          True,
          False
        ]
      ];

  (*maintain left external field amounts by stacks*)
  (*{sbs,abs}*)
  GenLeftExternalNumber[index_] :=
      If[masses[[index]] === 0,
        If[spins[[index]] > 0,
          {ConstantArray[index, spins[[index]] * 2], {}}
          ,
          {{}, ConstantArray[index, spins[[index]] * -2]}
        ]
        ,
        {ConstantArray[2 * np + 1 - index, spins[[index]] * 2 - antispinors[[index]]],
          {ConstantArray[index, antispinors[[index]]]}}
      ];
  EmptyStackQ[stack_] := stack[[1]] == Length@stack[[2]];
  PopStack[stack_] := stack[[2]][[++stack[[1]]]];
  SetAttributes[PopStack, HoldFirst];
  {extSbStack, extAbStack} = Flatten /@ (Transpose @ (GenLeftExternalNumber /@ Range[1, np]));
  extSbStack = {0, extSbStack}; extAbStack = {0, extAbStack};
  (*  Print["leftExternal:", "\n", extSbStack, "\n", extAbStack];*)
  FindNextHeadTarget[] :=
      With[{},
        While[True,
          If[!EmptyStackQ[extSbStack],
            targetBraType = sb;
            targetParticle = PopStack[extSbStack];
            ,
            If[!EmptyStackQ[extAbStack],
              targetBraType = ab;
              targetParticle = PopStack[extAbStack];
              ,
              targetBraType = targetParticle = Null;
              targetBraType2 = targetParticle2 = Null;
              Return[False];
            ]
          ];
          If[ExistNextTargetQ[targetBraType, targetParticle],
            chains ~ AppendTo ~ {targetBraType};
            Return[True];
          ]
        ]
      ];

  (*test whether exists next target bra, no side effect*)
  ExistNextTargetQ[targetBraTypeInner_, targetParticleInner_] := Block[{targetInner, rule, factorList},
    rule = {targetBraTypeInner, targetParticleInner, _};
    {targetInner, factorList} = SelectFirst[bras, FactorMatchQ[#, rule]&, Null] // Reap;
    Return[targetInner =!= Null];
  ];

  (*consume expected next target bra, change bras List and factor*)
  ConsumeNextTarget[targetBraTypeInner_, targetParticleInner_] := Block[{rule, factorList},
    rule = {targetBraTypeInner, targetParticleInner, _};
    {target, factorList} = SelectFirst[bras, FactorMatchQ[#, rule]&, Null] // Reap;
    If[target == Null, Return[False]];
    factor *= Times @@ Flatten @ factorList;
    bras = Drop[bras,
      FirstPosition[bras, target, Null, 1]
    ];
    Return[True];
  ];

  (*extend a head to tail*)
  ExtendChainStep[] :=
      If[ConsumeNextTarget[targetBraType, targetParticle],
        chains[[-1]] ~ AppendTo ~ targetParticle;
        targetBraType2 = targetBraType;
        targetBraType = Cases[{ab, sb}, Except[targetBraType2]][[1]];
        targetParticle = Cases[target, Except[targetBraType2 | targetParticle]][[1]];
        Return[True];
        ,
        chains[[-1]] ~ AppendTo ~ targetParticle;
        chains[[-1]] ~ AppendTo ~ targetBraType2;
        Return[False];
      ];

  (*All chain structure*)
  While[FindNextHeadTarget[],
    While[ExtendChainStep[]];
  ];

  While[Length@bras > 0,
    chains ~ AppendTo ~ {"circle"};
    targetBraType = bras[[1]][[1]];
    targetParticle = bras[[1]][[2]];
    circleHead = targetParticle;
    While[True,
      If[Length@bras == 0, Break[]];
      ExtendChainStep[];
      If[targetParticle == circleHead,
        Break[];
      ];
    ];
  ];

  (*Build sigma*)
  sigmas = Table[0, Length[chains]];
  Do[
    Switch[chains[[i]][[1]],
      ab, sigmas[[i]] = Length[chains[[i]]] - 4;,
      sb, sigmas[[i]] = -(Length[chains[[i]]] - 4);,
      "circle", sigmas[[i]] = (Length[chains[[i]]] - 1);,
      _, Throw[{chains[[i]][[1]], "Find Chain Error"}]
    ]
    , {i, Length[chains]}
  ];
  Return[{factor, chains, sigmas}]
];
FindPsiChain[np_Integer, opts : OptionsPattern[]] := FindPsiChain[#, np, Sequence @@ FilterRules[{opts}, Options[FindPsiChain]]]&;


(* ::Section:: *)
(*Translation *)


(* ::Subsection:: *)
(*ToolFun*)


ClearAll[ComplementMultiSet];
ComplementMultiSet::usage = "Define the Complement for Multiset. Preserve Order";
ComplementMultiSet[listAll_List, listsToRemove__List] := Fold[
  DeleteCases[#, #2, 1] &,
  listAll,
  DeleteDuplicates[Join@@{listsToRemove}]
]
ClearAll[IsFieldString];
IsFieldString[s_String]:=MemberQ[{"\[Phi]","\[Psi]","F+","F-","A"},s];


(* ::Subsection:: *)
(*Ds & Label gen*)


ClearAll@GetIndiceGen;
GetIndiceGen[label_String:""]:=Module[{a=1,Gen},Gen[]:=Symbol[label<>"$"<>ToString[a++]];
Return[Gen];]
ClearAll@DtranslateAll;
DtranslateAll[Lorgen_][psiChains_List]:=Module[{circledChains,circledWithDs,filteredChains,reChains,others,GetGenDInChain,genfun,chainsWithDs,allDs},
GetGenDInChain[start_]:=Module[{s,Gen},
s=Switch[start,ab,0,sb,1,_,Print["error GetGenDInChain"];Abort[]];
Gen[n_]:=Module[{lor=Lorgen[]},{{"D",n,lor},{If[EvenQ[s++],"\[Sigma]","\[Sigma]Bar"],lor}}];
Return[Gen];];

circledChains=Cases[psiChains,{"circle",__}];
circledWithDs=Table[genfun=GetGenDInChain[ab];
Join[{{"Tr"}},chain/.{{"circle",ds__}:>{Sequence@@Flatten[genfun/@{ds},1]}}],{chain,circledChains}];
filteredChains=Select[psiChains,Count[#,_Integer]>2&];
others=ComplementMultiSet[psiChains,filteredChains,circledChains];
chainsWithDs=Table[genfun=GetGenDInChain[chain[[1]]];
chain/.{{hL_,i_,ds__,j_,hR_}:>{hL,i,Sequence@@Flatten[genfun/@{ds},1],j,hR}},{chain,filteredChains}];
reChains=Join[chainsWithDs,circledWithDs];
allDs=Cases[reChains,{"D",n_,lor_},Infinity]//SortBy[#[[2]]&];
Join[reChains/.{"D",n_,lor_}:>Sequence[],others,allDs]];


(* ::Subsection:: *)
(*Append Field & Phi*)


(* ::Text:: *)
(*insert field assuming the spin of particle n match the fomula.*)


ClearAll[TranslateAppendField, TranslatePhi];
TranslateAppendField[fieldObj_List, n_Integer, chain_List] := Module[{dpos},
   dpos = Flatten@Position[chain, {"D", n, ___}];
   If[Length@dpos == 0, Return[Insert[chain, fieldObj, -1]]];
   Insert[chain, fieldObj, dpos[[-1]] + 1]
   ];
TranslatePhi[n_Integer][chain_List] := TranslateAppendField[{"\[Phi]", n}, n, chain];


(* ::Subsection:: *)
(*Psi*)


ClearAll[TranslatePsi];
TranslatePsi[n_Integer][chain_List]:=
chain/. {{ab,n,o___}:>{{"\[Psi]",n,ab},o},{sb,n,o___}:>{{"\[Psi]",n,sb},o},{o___,n,ab}:>{o,{"\[Psi]",n,ab}},{o___,n,sb}:>{o,{"\[Psi]",n,sb}}
};


(* ::Subsection:: *)
(*PsiChain Operate Fun*)


(* ::Subsubsection:: *)
(*ReversePsiChain*)


ClearAll@ReversePsiChain;
ReversePsiChain[chain_List] := Reverse[chain /. {"\[Sigma]" -> "\[Sigma]Bar", "\[Sigma]Bar" -> "\[Sigma]"}];


(* ::Subsubsection:: *)
(*ChainToCircle*)


(* ::Text:: *)
(*Assuming chain can be glued as circle. i,j will be indices in sigma or sigmabar*)
(*return as {new chain objs, used indices list, sigma/sigmabar/None}*)


ClearAll[ChainToCircleSame,ChainToCircleFlip];
ChainToCircleSame[Lorgen_][chain_List,n_Integer] := Module[{test,extra, others, flag, i, j},
test=Length@chain>4&&chain[[;;2]]===chain[[{-1,-2}]]&&chain[[2]]==n;
  If[!test, Return[{chain, {}, None}]];
  i = Lorgen[];
  j = Lorgen[];
  flag = Switch[chain[[1]], ab, "\[Sigma]", sb, "\[Sigma]Bar", _, Print["error ChainToCircle: mismatched chain head", chain[[1]]]; Abort[]];
  extra = {flag, i, j};
  others = chain[[3 ;; -3]];
  others = Switch[Length@others, 0, {}, 1, {others[[1]]}, _, others];
  Return@{{{"Tr"},extra, Sequence @@ others}, {i, j}, flag};
  ];
ChainToCircleFlip[Lorgen_][chain_List,n_Integer] := Module[{test, extra, others,flag, i},
  test=Length@chain>4
  &&chain[[2]]===chain[[-2]]&&chain[[2]]==n
  &&Length@Complement[{ab,sb},{chain[[1]],chain[[-1]]}]==0;
  If[!test, Return[{chain, {}, None}]];
  i = Lorgen[];
  flag = Switch[chain[[-1]], ab, "\[Sigma]", sb, "\[Sigma]Bar", _, Print["error ChainToCircle: mismatched chain head", chain[[1]]]; Abort[]];
  extra = {flag, i};
  others = chain[[3 ;; -3]];
  others = Switch[Length@others, 0, {}, 1, {others[[1]]}, _, others];
  Return@{{{"Tr"},extra, Sequence @@ others}, {i}, flag};
  ];


(* ::Subsubsection:: *)
(*ChainGlued *)


ClearAll@ChainGluedSame;
ChainGluedSame[Lorgen_][chainA_List, chainB_List, n_] := Module[{chainA2, chainB2, flag,i, j, aL, aR, bL, bR, gl, dealFun, extra},
   aL = chainA[[;; 2]];
   aR = chainA[[{-1, -2}]];
   bL = chainB[[;; 2]];
   bR = chainB[[{-1, -2}]];
   dealFun["aL==bL"] := Block[{},
     gl = aL[[1]];
     chainA2 = ReversePsiChain@chainA[[3 ;;]];
     chainB2 = chainB[[3 ;;]];
     ];
   dealFun["aL==bR"] := Block[{},
     gl = aL[[1]];
     chainA2 = chainB[[;; -3]];
     chainB2 = chainA[[3 ;;]];
     ];
   dealFun["aR==bL"] := Block[{},
     gl = aR[[1]];
     chainA2 = chainA[[;; -3]];
     chainB2 = chainB[[3 ;;]];
     ];
   dealFun["aR==bR"] := Block[{},
     gl = aR[[1]];
     chainA2 = chainA[[;; -3]];
     chainB2 = ReversePsiChain@chainB[[;; -3]];
     ];
   Which[
    aL === bL && aL[[2]] == n, dealFun["aL==bL"],
    aL === bR && aL[[2]] == n, dealFun["aL==bR"],
    aR === bL && aR[[2]] == n, dealFun["aR==bL"],
    aR === bR && aR[[2]] == n, dealFun["aR==bR"],
    True, Return[{{chainA, chainB}, {}, None}];];
   i = Lorgen[];
   j = Lorgen[];
   flag = Switch[gl, ab, "\[Sigma]", sb, "\[Sigma]Bar", _, Print["error ChainGluedSame: mismatched chain head:", gl,"at:\n",chainA,"\nand\n",chainB]; Abort[]];
   extra = {flag, i, j};
   chainA2 = Switch[Length@chainA2, 0, {}, 1, {chainA2[[1]]}, _, chainA2];
   chainB2 = Switch[Length@chainB2, 0, {}, 1, {chainB2[[1]]}, _, chainB2];
   Return@{{Sequence @@ chainA2, extra, Sequence @@ chainB2}, {i, j}, flag}
   ];

ClearAll@ChainGluedFlip;
ChainGluedFlip[Lorgen_][chainA_List, chainB_List, n_] := Module[{chainA2, chainB2,flag,CheckConnectAble, i,  aL, aR, bL, bR, gl, dealFun, extra},
   aL = chainA[[;; 2]];
   aR = chainA[[{-1, -2}]];
   bL = chainB[[;; 2]];
   bR = chainB[[{-1, -2}]];
   CheckConnectAble[{lH_,ln_},{rH_,rn_}]:=ln==n&&rn==n&&Length@Complement[{ab,sb},{lH,rH}]==0;
   dealFun["aL&bL"] := Block[{},
     gl = {aL[[1]],bL[[1]]};
     chainA2 = ReversePsiChain@chainA[[3 ;;]];
     chainB2 = chainB[[3 ;;]];
     ];
   dealFun["aL&bR"] := Block[{},
     gl = {aL[[1]],bR[[1]]};
     chainA2 = chainB[[;; -3]];
     chainB2 = chainA[[3 ;;]];
     ];
   dealFun["aR&bL"] := Block[{},
      gl = {aR[[1]],bL[[1]]};
     chainA2 = chainA[[;; -3]];
     chainB2 = chainB[[3 ;;]];
     ];
   dealFun["aR&bR"] := Block[{},
      gl = {aR[[1]],bR[[1]]};
     chainA2 = chainA[[;; -3]];
     chainB2 = ReversePsiChain@chainB[[;; -3]];
     ];
   Which[
    CheckConnectAble[aL,bL], dealFun["aL&bL"],
    CheckConnectAble[aL,bR], dealFun["aL&bR"],
    CheckConnectAble[aR,bL], dealFun["aR&bL"],
    CheckConnectAble[aR,bR], dealFun["aR&bR"],
    True, Return[{{chainA, chainB}, {}, None}];];
   i = Lorgen[];
   flag = Switch[gl, {ab,sb}, "\[Sigma]", {sb,ab}, "\[Sigma]Bar", _, Print["error ChainGluedFlip: mismatched chain head:", gl,"at:\n",chainA,"\nand\n",chainB];  Abort[]];
   extra = {flag, i};
   chainA2 = Switch[Length@chainA2, 0, {}, 1, {chainA2[[1]]}, _, chainA2];
   chainB2 = Switch[Length@chainB2, 0, {}, 1, {chainB2[[1]]}, _, chainB2];
   Return@{{Sequence @@ chainA2, extra, Sequence @@ chainB2}, {i}, flag}
   ];


(* ::Subsection:: *)
(*Vector 1*)


(* ::Code::Initialization::"Tags"-><|"UppercaseVariable" -> <||>, "UppercasePattern" -> <||>|>:: *)
ClearAll[TranslateVector];
TranslateVector[Lorgen_,n_Integer][chains_List]:=Module[{relatedChains,circleTest,otherChains,DealWithChains,DealWithCircle,changedChain,rulesDealField,appendedFieldObj},
(*classify chains*)
relatedChains=Cases[chains,({hL_,n,___}/;MemberQ[{ab,sb},hL])|({___,n,hR_}/;MemberQ[{ab,sb},hR])];
otherChains=ComplementMultiSet[chains,relatedChains];
(*1chain indicate circle, 2 indicate 2chains, others wrong*)
circleTest=Switch[Length@relatedChains,1,True,2,False,_,Print["error TranslateVector:mismatched wave function spinors"];Abort[]];
(*def two cases*)
DealWithCircle[]:=Module[{temp1},
temp1=ChainToCircleSame[Lorgen][relatedChains[[1]],n];
If[Length@temp1[[2]]==0,temp1=ChainToCircleFlip[Lorgen][relatedChains[[1]],n];];
If[Length@temp1[[2]]==0,Print["error TranslateVector:at ",n," for:\n",chains];Abort[]];
changedChain=temp1[[1]];
appendedFieldObj=temp1[[{2,3}]];
];
DealWithChains[]:=Module[{temp1},
temp1=ChainGluedSame[Lorgen][relatedChains[[1]],relatedChains[[2]],n];
If[Length@temp1[[2]]==0,
temp1=ChainGluedFlip[Lorgen][relatedChains[[1]],relatedChains[[2]],n];];
If[Length@temp1[[2]]==0,Print["error TranslateVector:at ",n," for:\n",chains];Abort[]];
changedChain=temp1[[1]];
appendedFieldObj=temp1[[{2,3}]];
];
(*exec*)
If[circleTest,DealWithCircle[],DealWithChains[]];
rulesDealField={
{{i_,j_},"\[Sigma]"}:>{"F-",n,i,j},
{{i_,j_},"\[Sigma]Bar"}:>{"F+",n,i,j},
{{i_},"\[Sigma]"|"\[Sigma]Bar"}:>{"A",n,i}};
appendedFieldObj = appendedFieldObj /.rulesDealField;
TranslateAppendField[appendedFieldObj,n,Join[{changedChain},otherChains]]
];


(* ::Subsection:: *)
(*Gravitino 3/2  *)


ClearAll[TranslateGravitino];
TranslateGravitino[Lorgen_, n_Integer][chains_List] := Module[{
  isLongMode, relatedChains, circleTest, otherChains, remainChains, chainsForConnect, fieldType,
  ClassifyChains, DealWithChain, DealWithCircle, changedChain, appendedInd, reChains},
  (*classify chains*)
  relatedChains = Cases[chains, ({hL_, n, ___} /; MemberQ[{ab, sb}, hL]) | ({___, n, hR_} /; MemberQ[{ab, sb}, hR])];
  otherChains = ComplementMultiSet[chains, relatedChains];
  (*2chain indicate circle+line, 3 indicate Y type, others wrong*)
  circleTest = Switch[Length@relatedChains, 2, True, 3, False, _, Print["error TranslateGravitino::at ", n, " circleTest mismatched wave function spinors"]; Abort[]];
  (*ab3->3 ab2sb1->2 ab1sb2->1 ab0sb3->0*)
  fieldType = Count[relatedChains, {ab, n, ___}] + Count[relatedChains, {___, n, ab} ];
  (* Print["relatedChains", relatedChains]; *)
  (* Print["fieldType", fieldType]; *)
  isLongMode = Switch[fieldType, 0|3, False, 1|2, True, _, Print["error TranslateGravitino::at ", n, " ab|sb count illegal"]; Abort[] ];
  (*For 3|0 we have 2 cases:
    a -- a, a -- o.
    a--o, a--o, a--o.
    For 2|1 we have 3 cases:
    a -- s, a -- o.
    a -- a, s -- o.
    a -- o, a -- o, s -- o.
  *)
  ClassifyChains[] := Module[{ah, sh, tempAX, tempSO, tempAS},
    ah = Switch[fieldType, 2|3, ab, 1|0, sb];
    sh = Switch[fieldType, 2|3, sb, 1|0, ab];
    Switch[fieldType,
    3|0,
    (*2 cases*)
    If[

        circleTest,

        (*a -- a, a -- o.*)
        chainsForConnect = Cases[relatedChains, {ah, n, ___, n, ah}];
        remainChains = If[chainsForConnect[[1]] === First@relatedChains, {Last@relatedChains}, {First@relatedChains}];
        ,

        (*a--o, a--o, a--o.*)
        tempAX = SortBy[Length]@relatedChains;
        chainsForConnect = tempAX[[{1,2}]];
        remainChains = {tempAX[[3]]}
      ],
    2|1,
    (*3 cases*)
    (*maybe a -- s or a -- a or a--o *)
    tempAX = SortBy[Length]@Cases[relatedChains, {ah, n, ___} | {___,n, ah} ];
    (*only a -- s*)
    tempAS = Cases[tempAX, {sh, n, ___} | {___,n, sh} ];
    (*only s -- o*)
    tempSO = ComplementMultiSet[relatedChains, tempAX];
    Which[
      (*a -- o, a -- o, s -- o.*)
      !circleTest && Length@tempSO == 1,
      chainsForConnect = {tempSO[[1]], tempAX[[1]]};
      remainChains = {tempAX[[2]]},

      (*a -- s, a -- o.*)
      circleTest && Length@tempAS == 1,
      chainsForConnect = {tempAS[[1]]};
      remainChains = If[chainsForConnect[[1]] === tempAX[[1]], {tempAX[[2]]}, {tempAX[[1]]}],

      (*a -- a, s -- o.*)
      circleTest && Length@tempSO == 1,
      chainsForConnect = {tempSO[[1]], tempAX[[1]]};
      remainChains = {},

      (*others*)
      _, Print["error TranslateGravitino::at ", n, " no such topological chains structure.\n", chains]; Abort[]
      ];
    ];
  ];
  (*def two cases*)
  DealWithCircle[] := Module[{circledChain, temp1},
  (* Print["conn c", chainsForConnect]; *)
    circledChain = chainsForConnect[[1]];
    temp1 = If[isLongMode, ChainToCircleFlip, ChainToCircleSame][Lorgen][circledChain, n];
    If[Length@temp1[[2]] == 0, Print["error TranslateGravitino:connect at ", n, " for:\n", chainsForConnect]; Abort[]];
    changedChain = temp1[[1]];
    appendedInd = temp1[[2]];
    ];
  DealWithChain[] := Module[{selectedMergeChains, temp1},
    (* Print["conn l", chainsForConnect]; *)
    selectedMergeChains = chainsForConnect;
    temp1 = If[isLongMode, ChainGluedFlip ,ChainGluedSame][Lorgen][selectedMergeChains[[1]], selectedMergeChains[[2]], n];
    If[Length@temp1[[2]] == 0, Print["error TranslateGravitino:connect at ", n, " for:\n", chainsForConnect]; Abort[]];
    changedChain = temp1[[1]];
    appendedInd = temp1[[2]];
    ];
  (*exec*)
  ClassifyChains[];
  (* Print["chainsForConnect",chainsForConnect]; *)
  (* Print["remainChains", remainChains]; *)
  If[Length@chainsForConnect==1, DealWithCircle[], DealWithChain[] ];
  If[Length@appendedInd > 2 || Length@appendedInd < 1, Print["error TranslateGravitino:ind new at", n, " for:\n", chains]; Abort[];];
  (* Print["changedChain", changedChain, appendedInd]; *)
  (* Print["remainChains", remainChains]; *)
  changedChain = Join[{changedChain}, remainChains];
  (* Print["changedChain", changedChain]; *)
  changedChain = TranslatePsi[n][changedChain] /. {{"\[Psi]", n, o___} :> {"\[Psi]", n, o, appendedInd[[-1]]}};
  (* Print["changedChain", changedChain]; *)
  reChains = Join[changedChain, otherChains];
  (* Print["reChains", reChains]; *)
  Return@If[
    Length@appendedInd > 1,
    TranslateAppendField[{"D", n, appendedInd[[1]]}, n, reChains],
    reChains
    ];
  ];


(* ::Subsection:: *)
(*Gauge*)


ClearAll[AppendChainsWithGaugeIndices]

(*
  AppendChainsWithGaugeIndices:
  Appends gauge symmetry indices to relevant elements within chains based on a gauge label and particle gauge index dictionary.

  Parameters:
  - gaugeLabel_String: The label used to generate gauge indices.
  - particleGaugeIndDict_Association: An association mapping integers to gauge index identifiers.

  Returns:
  - A function that takes IYT data and chains, and returns the combined list of epsilon objects and updated chains.
*)
AppendChainsWithGaugeIndices[gaugeLabel_String, particleGaugeIndDict_Association][IYT[iytData_List], chains_List] := Module[
  {
    gaugeIndiceGenerator,
    gaugeIndexReplaceRules,
    epsilonObjects,
    particleGaugeSymDict,
    UpdateFieldElement,
    updatedChains
  },

  (* Generate a gauge index generator based on the provided gauge label *)
  gaugeIndiceGenerator = GetIndiceGen[gaugeLabel];

  (* Create replacement rules for gauge indices from number to symbol *)
  gaugeIndexReplaceRules = Dispatch[
    Table[
      id -> gaugeIndiceGenerator[],
      {id, Sort@Flatten@Values@particleGaugeIndDict}
    ]
  ];

  (* Generate epsilon objects by replacing indices in iytData *)
  epsilonObjects = ReplaceAll[gaugeIndexReplaceRules] /@ Flatten[{"\[Epsilon]", ##}] & /@ Transpose@iytData;

  (* Create a dictionary for particle gauge symmetries *)
  particleGaugeSymDict = ReplaceAll[gaugeIndexReplaceRules] /@ particleGaugeIndDict;

  (* Define a local function to update each field object *)
  UpdateFieldElement = Function[element,
    Which[
      MatchQ[element, {field_?IsFieldString, n_Integer, ___}],
        Join[element, Lookup[particleGaugeSymDict,element[[2]], {}]],
      True,
        element
    ]
  ];

  (* Apply the UpdateFieldElement function to each relevant sublist within chains *)
  updatedChains = Map[UpdateFieldElement, chains, Infinity];

  (* Combine epsilon objects with updated chains *)
  Join[epsilonObjects, updatedChains]
]



(* ::Subsection:: *)
(*Final*)


ClearAll[TranslateCheckComplete]

(*
  TranslateCheckComplete:
  Checks if the chains list does not contain any patterns matching {sb|ab, n_Integer, ___} or {___, n_Integer, sb|ab}.

  Parameters:
  - chains_List: The list of chains to be checked.

  Returns:
  - True if no such patterns are found, False otherwise.
*)
TranslateCheckComplete[chains_List] :=
  Count[chains, {sb | ab, n_Integer, ___}] +
  Count[chains, {___, n_Integer, sb | ab}] == 0


ClearAll[RearrangeIndex]

(*
  RearrangeIndex:
  Replaces old `label` indices with new generated ones as sorted.

  Parameters:
  - label_String: The label used to identify and generate new gauge indices.
  - chains_List: The list of chains to be processed.

  Returns:
  - Updated chains with rearranged gauge indices.
*)
RearrangeIndex[label_String][chains_List] := Module[
  {
    allIndices,
    newIndicesGenerator,
    indicesReplaceRules
  },
  (* Extract all unique indices that start with the specified label followed by "$" *)
  allIndices =
    Cases[
      Flatten@chains,
      a_ /; StringStartsQ[label <> "$"]@ToString@a
    ] // DeleteDuplicates;

  (* Initialize a new gauge index generator based on the label *)
  newIndicesGenerator = GetIndiceGen[label];

  (* Create replacement rules mapping old indices to new generated indices *)
  indicesReplaceRules = Dispatch[
    Table[
      oldId -> newIndicesGenerator[],
      {oldId, allIndices}
    ]
  ];

  (* Apply the replacement rules to rearrange indices in chains *)
  chains /. indicesReplaceRules
]


ClearAll[WeylObjsCanonical]

(*
  WeylObjsCanonical:
  Processes the chains to separate epsilon chains, trace chains, psi chains, and others.
  It then rearranges the indices for the "LI" label.

  Parameters:
  - chains_List: The list of chains to be canonicalized.

  Returns:
  - A rearranged list of chains with canonicalized Weyl objects.
*)
WeylObjsCanonical[chains_List] := Module[
  {
    epsilonChains,
    traceChains,
    psiChains, mts,mts2,
    otherChains
  },

  (* Extract chains that start with "\[CurlyEpsilon]" *)
  epsilonChains = Cases[chains, {"\[Epsilon]", ___}];
  (* Extract chains that start with "MT" *)
  mts=Cases[chains, {"MT", ___}];
  (* Extract chains that start with "Tr" *)
  traceChains = Cases[chains, {{"Tr"}, ___}];
  (* Extract chains that start with "\[CapitalPsi]" *)
  psiChains = Cases[chains, {{"\[Psi]", ___}, ___}];
  (* Identify other chains not classified as epsilon, trace, or psi chains *)
  otherChains = ComplementMultiSet[chains,epsilonChains,mts,traceChains,psiChains];

  (* Replace specific trace chains with "MT" if conditions are met *)
  mts2=Cases[traceChains,
    {{"Tr"}, {s1_, lor1_}, {s2_, lor2_}} /;
      Length@Complement[{"\[Sigma]", "\[Sigma]Bar"}, {s1, s2}] == 0];
  traceChains = ComplementMultiSet[traceChains, mts2];
  mts=Join[mts,mts2//.{{"Tr"}, {s1_, lor1_}, {s2_, lor2_}}:> {"MT", lor1, lor2}];

  (* Rearrange indices for "LI" label and combine all chains *)
  RearrangeIndex["LI"]@Join[epsilonChains, psiChains, otherChains, mts, traceChains]
]



ClearAll[Amp2WeylOp]
Amp2WeylOp::usage = "Amp2WeylOp[n, opts][amp] translates a spinor-helicity monomial, optionally with gauge tableaux, to the package Weyl-operator chain representation.";

(*
  Amp2WeylOp:
  Transforms an amplitude into its Weyl operator representation based on provided options.

  Parameters:
  - np_: An integer parameter representing a specific property or identifier.
  - OptionsPattern[]: Optional parameters including:
      - mass (default: All)
      - su2ShapeList (default: {})
      - su3ShapeList (default: {})

  Usage:
  Amp2WeylOp[np, mass -> masses, su2ShapeList -> su2s, su3ShapeList -> su3s][{IYTs__, amp}]
  Amp2WeylOp[np, mass -> masses][amp]
*)
Options[Amp2WeylOp] = {mass -> All, su2ShapeList -> {}, su3ShapeList -> {}};
Amp2WeylOp[np_Integer, OptionsPattern[]][{IYTs__, amp_?AmplitudeSingletQ}/;
 AllTrue[Head /@ {IYTs}, MatchQ[IYT]]] := Module[
  {
    iytsList = List[IYTs],
    su2Shapes = OptionValue[su2ShapeList],
    su3Shapes = OptionValue[su3ShapeList],
    su2IndDict,
    su3IndDict,
    result
  },

  (* Create SU2 Indices Dictionary *)
  su2IndDict = If[
    Length[su2Shapes] == 0 || Count[su2Shapes, ""] == Length[su2Shapes],
    <||>,
    GetGaugeIndDict[Lookup[su2ShapeDict, #, ""] & /@ su2Shapes]
  ];

  (* Create SU3 Indices Dictionary *)
  su3IndDict = If[
    Length[su3Shapes] == 0 || Count[su3Shapes, ""] == Length[su3Shapes],
    <||>,
    GetGaugeIndDict[Lookup[su3ShapeDict, #, ""] & /@ su3Shapes]
  ];

  (* Initialize Result by Applying Amp2WeylOp *)
  result = Amp2WeylOp[np, mass -> OptionValue[mass]][amp];

  (* Append Gauge Indices Based on Dictionaries and IYTsList Length *)
  Which[
    Length[su2IndDict] > 0 && Length[su3IndDict] > 0 && Length[iytsList] == 2,
      result = AppendChainsWithGaugeIndices["su3", su3IndDict][iytsList[[2]], result];
      result = AppendChainsWithGaugeIndices["su2", su2IndDict][iytsList[[1]], result];,

    Length[su2IndDict] > 0 && Length[iytsList] == 1,
      result = AppendChainsWithGaugeIndices["su2", su2IndDict][iytsList[[1]], result];,

    Length[su3IndDict] > 0 && Length[iytsList] == 1,
      result = AppendChainsWithGaugeIndices["su3", su3IndDict][iytsList[[1]], result];,

    True,
      Print["Warning: Mismatch in YT amount or gauge shape."]
  ];

  (* Return the Final Result *)
  Return[result]
]

Amp2WeylOp[np_Integer, OptionsPattern[]][amp_?AmplitudeSingletQ] := Module[
  {
    config,
    ruleMassless,
    psiChain,
    lorgen,
    posPhi,
    posPsi,
    posV,
    posG,
    re
  },

  (* Generate configuration *)
  config = Transpose@Amp2MetaInfo[amp, np, mass -> OptionValue[mass]];

  (* Check spin limit *)
  If[Max /@ Abs /@ First /@ config > 3/2,
    Print["spin > 3/2, not implemented"];
    Abort[]
  ];

  (* Create massless rules *)
  ruleMassless = Table[2 np + 1 - i -> i, {i, np}];

  (* Find and replace psi chains *)
  psiChain = FindPsiChain[amp, np, mass -> OptionValue[mass]][[2]] /. ruleMassless;

  (* Initialize index generator *)
  lorgen = GetIndiceGen["LI"];

  (* Initialize result association *)
  re = <||>;

  (* Translate D *)
  re["D"] = DtranslateAll[lorgen][psiChain];

  (* Find positions in config *)
  posPhi = Flatten@Position[config, {0, 0}];
  posPsi = Flatten@Position[config, {1/2 | -1/2, _}];
  posV = Flatten@Position[config, {1 | -1, _}];
  posG = Flatten@Position[config, {3/2 | -3/2, _}];

  (* Translate Phi, Psi, Vector, and Gravitino chains *)
  re["phi"] = Fold[TranslatePhi[#2][#1] &, Join[{re["D"]}, posPhi]];
  re["psi"] = Fold[TranslatePsi[#2][#1] &, Join[{re["phi"]}, posPsi]];
  re["V"] = Fold[TranslateVector[lorgen, #2][#1] &, Join[{re["psi"]}, posV]];
  re["Gravitino"] = Fold[TranslateGravitino[lorgen, #2][#1] &, Join[{re["V"]}, posG]];

  (* Verify translation completeness *)
  If[!TranslateCheckComplete[re["Gravitino"]],
    Print["Warning! Translation not complete!"];
    Abort[]
  ];

  (* Return canonical Weyl objects *)
  Return@WeylObjsCanonical[re["Gravitino"]]
]
