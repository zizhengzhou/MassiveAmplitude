(* ::Package:: *)

(* SU2 rep shapes  *)
su2ShapeDict = <|"" -> {}, "1" -> {1}, "2" -> {2}, "3" -> {3}|>;

(* SU2 Reduction to SYT *)
ClearAll[ReduceSU2ITY, ReduceSU2ITYSortPart, ReduceSU2ITYSchId];
ReduceSU2ITY[expr_] := 
  NestWhile[ReduceSU2ITYSortPart@ReduceSU2ITYSchId@ReduceSU2ITYSortPart@# &, 
   expr, (Expand@#1 =!= Expand@#2) &, 2];

ReduceSU2ITYSortPart[expr_Plus] := ReduceSU2ITYSortPart /@ expr;
ReduceSU2ITYSortPart[cc_. IYT[ll_List]] := Module[{coeff, ll2},
   coeff = cc*Times @@ (Signature /@ Transpose@ll);
   ll2 = Transpose@ll;
   ll2 = Sort /@ ll2;
   ll2 = SortBy[ll2, First];
   Return[coeff IYT[Transpose@ll2]];
];

(* SU2 Sch Identity *)
ReduceSU2ITYSchId[expr_Plus] := ReduceSU2ITYSchId /@ expr // Expand;
ReduceSU2ITYSchId[expr_Plus, ic_Integer, jc_Integer] := 
  ReduceSU2ITYSchId[#, ic, jc] & /@ expr // Expand;
ReduceSU2ITYSchId[cc_. IYT[ll_List]] /; 
   OrderedQ[ll[[1]]] && OrderedQ[ll[[2]]] := cc* IYT[ll];
ReduceSU2ITYSchId[cc_. IYT[ll_List]] := Fold[
   ReduceSU2ITYSchId[#1, Sequence @@ ##2] &, cc*IYT[ll],
   Flatten[Table[{ic, jc}, {ic, Range[Length@ll[[1]] - 1, 1, -1]}, 
     {jc, ic + 1, Length@ll[[1]]}], 1]
];
ReduceSU2ITYSchId[cc_. IYT[ll_List], ic_Integer, jc_Integer] := 
  If[ll[[2, ic]] < ll[[2, jc]], 
   Return[cc*IYT[ll]], 
   Module[{t = ll[[2, jc]], ll2 = ll, ll3},
    {ll2[[2, ic]], ll2[[2, jc]]} = Reverse@{ll2[[2, ic]], ll2[[2, jc]]};
    ll3 = ll2;
    {ll3[[2, ic]], ll3[[1, jc]]} = Reverse@{ll3[[2, ic]], ll3[[1, jc]]};
    Return[cc*IYT[ll2] - cc*IYT[ll3]]
]];

(* SUN Utility Functions *)
GetGaugeIndDict[shapes_List] := 
  Module[{indAmountList, indDict, lastInd = 0}, 
   indAmountList = Transpose@{Range[Length@shapes], Total /@ shapes} // SortBy[#, Last] &;
   indDict = Do[If[e[[2]] != 0, Sow[e[[1]] -> lastInd + Range[e[[2]]]];
          lastInd = lastInd + e[[2]];], {e, indAmountList}] // Reap // Last //
       First // Association;
   Return[indDict];
];

GenerateSUNSYT[n_Integer][maxInd_Integer] /; n >= 2 && Mod[maxInd, n] == 0 := 
  IYT /@ GenerateStandardTableaux[ConstantArray[maxInd/n, n]];

GetPermuteGaugeIdenticalRules[identicalParticleList_List, 
   colorIndDict_Association] := 
  Module[{particleReplaceRules = 
     GetMasslessIdenticalRules[identicalParticleList], ReplaceParticle2ColorRule}, 
   ReplaceParticle2ColorRule[n1_ -> n2_] := 
    MapThread[#1 -> #2 &, {colorIndDict[n1], colorIndDict[n2]}];
   Return[(ReplaceParticle2ColorRule /@ # // Flatten) & /@ particleReplaceRules]
];

GetPermuteGaugeInnerRules[colorIndDict_Association] := 
  Module[{permutationColorRuleDict, GenColorRule}, 
   GenColorRule[inds_] := 
    GetMasslessIdenticalRules@
     Switch[Length@inds, 1, {}, 2, inds~Append~{"A"}, 3, inds~Append~{"S"}];
   permutationColorRuleDict = GenColorRule /@ colorIndDict;
   Return[permutationColorRuleDict];
];

GetGaugeIdenticalPermutedOperatorDict[identicalParticleLists_List, 
   colorIndDict_Association, genCoorsByRule_] := 
  Module[{operatorDict, rules, coors, PFirst, PAll}, 
   operatorDict = Table[identicalParticleList -> Null, {identicalParticleList, identicalParticleLists}] // Association;
   Do[rules = GetPermuteGaugeIdenticalRules[identicalParticleList, colorIndDict];
    coors = genCoorsByRule /@ rules;
    PFirst = coors[[2]];
    PAll = coors[[-1]];
    operatorDict[identicalParticleList] = {1 -> IdentityMatrix[Length@coors[[-1]]], 
       symPermuteFirst -> PFirst, symPermuteAll[-1 + Length@identicalParticleList] -> PAll} // DeleteDuplicates;, 
    {identicalParticleList, identicalParticleLists}];
   Return[operatorDict];
];

GetGaugeInnerPermutedOperatorDict[colorIndDict_Association, genCoorsByRule_] := 
  Module[{operatorDict, allRules, rules, coors, PFirst, PAll}, 
   operatorDict = <||>;
   allRules = GetPermuteGaugeInnerRules[colorIndDict];
   Do[
    rules = allRules[coloredParticle];
    coors = genCoorsByRule /@ rules;
    If[Length@coors != 1, 
     PFirst = coors[[2]];
     PAll = coors[[-1]];
     AssociateTo[operatorDict, coloredParticle -> {1 -> IdentityMatrix[Length@coors[[1]]], 
        symPermuteFirst -> PFirst}~Join~If[Length@colorIndDict[coloredParticle] > 2, 
         {symPermuteAll[Length@colorIndDict[coloredParticle]] -> PAll}, {}]]
    ];
    , {coloredParticle, Keys@colorIndDict}
   ];
   Return[operatorDict];
];

ReplaceGaugeTableauxNumber[rule_] := # /. IYT[l___] :> IYT[l /. rule] &;

(* SU2 Basis Construction *)
ClearAll[GetProjectInnerSU2Op];
GetProjectInnerSU2Op[su2IndDict_Association, <||>] := {{1}};
GetProjectInnerSU2Op[su2IndDict_Association, operatorDict_Association] := 
  Module[{polyDict},
   polyDict = First@GetPermutedPolyFromYT@# & /@ Association@Table[particle -> {Length@su2IndDict[particle]}, 
       {particle, Keys@operatorDict}];
   Do[polyDict[p] = polyDict[p], {p, Keys@polyDict}];
   Dot @@ Table[polyDict[p] /. operatorDict[p], {p, Keys@polyDict}] // Return;
];

(* Main SU2 Basis Construction Functions *)
Clear[AuxConstructIdenticalSU2Basis]
Options[AuxConstructIdenticalSU2Basis] = {log -> False};

AuxConstructIdenticalSU2Basis[su2ShapeList_, identicalParm_, OptionsPattern[]] := 
 Module[{gaugeIndDict, identicalList = {}, maxInd, gaugeBasis, rulesIdentical,
    rulesInnerDict, rulesUsed, ParaFindRuleMatrix, ruleInnerCoorsDict, 
   gaugeInnerOpDict, projectionOp, independentPosList, proL, proR, metricInvG,
    ruleIdenticalCoorsDict, gaugeIdenticalOpDict}, 
  
  (* Check if su2ShapeList is valid *)
  If[Sort@Keys@su2ShapeDict =!= Sort@DeleteDuplicates[su2ShapeList~Join~Keys@su2ShapeDict], 
   Print["No such SU2 type"];
   Abort[];
  ];
  
  (* Generate gauge index dictionary *)
  gaugeIndDict = GetGaugeIndDict[su2ShapeDict[#] & /@ su2ShapeList];
  
  (* Initialize identicalList based on identicalParm *)
  Do[If[SubsetQ[Keys@gaugeIndDict, e[[;; -2]]], AppendTo[identicalList, e];], {e, identicalParm}];
  
  (* Calculate maxInd and check for SU2 singlet condition *)
  maxInd = Max[gaugeIndDict // Values];
  If[Mod[maxInd, 2] != 0, Throw["no SU2 singlet"]];
  
  (* Generate gauge basis *)
  gaugeBasis = GenerateSUNSYT[2][maxInd];
  
  (* Get rules for identical elements *)
  rulesIdentical = Flatten[GetPermuteGaugeIdenticalRules[#, gaugeIndDict] & /@ identicalList, 1];
  rulesIdentical = DeleteDuplicates[rulesIdentical];
  
  (* Get rules for inner elements *)
  rulesInnerDict = GetPermuteGaugeInnerRules[gaugeIndDict];
  rulesUsed = Flatten[rulesInnerDict // Values, 1];
  rulesUsed = DeleteDuplicates[rulesUsed];
  
  (* Define ParaFindRuleMatrix function *)
  ParaFindRuleMatrix[paraRule_] := 
   Map[Coefficient[ReduceSU2ITY@#, gaugeBasis] &, ReplaceGaugeTableauxNumber[paraRule] /@ gaugeBasis];
  
  ParaFindRuleMatrix[paraRule_, L_, R_, InvG_] := InvG . L . ParaFindRuleMatrix[paraRule] . R;
  ParaFindRuleMatrix[{}] := IdentityMatrix[Length@gaugeBasis];
  ParaFindRuleMatrix[{}, L_, R_, InvG_] := IdentityMatrix[Length@InvG];
  
  (* Create the ruleInnerCoorsDict *)
  ruleInnerCoorsDict = Table[rule -> ParaFindRuleMatrix[rule], {rule, rulesUsed}] // Association;
  
  (* Process the gauge basis and operators *)
  gaugeInnerOpDict = GetGaugeInnerPermutedOperatorDict[gaugeIndDict, ruleInnerCoorsDict[#] &];
  projectionOp = GetProjectInnerSU2Op[gaugeIndDict, gaugeInnerOpDict];
  If[projectionOp==={{1}},projectionOp=IdentityMatrix[Length@gaugeBasis]];
  independentPosList = FindIndependentBasisPos[projectionOp];
  If[Length@independentPosList == 0, Return[{gaugeIndDict, {}, <||>}]];
  
  proL = projectionOp[[independentPosList, ;;]];
  proR = Transpose@proL;
  metricInvG = Inverse[proL . proR];
  
  (* Create the ruleIdenticalCoorsDict *)
  ruleIdenticalCoorsDict = Table[rule -> ParaFindRuleMatrix[rule, proL, proR, metricInvG], {rule, rulesIdentical}] // Association;
  
  (* Generate the final result for gaugeIdenticalOpDict *)
  gaugeIdenticalOpDict = GetGaugeIdenticalPermutedOperatorDict[identicalList, gaugeIndDict, ruleIdenticalCoorsDict[#] &];
  
  (* Return the result *)
  Return[{gaugeIndDict, gaugeBasis[[independentPosList]], gaugeIdenticalOpDict}];
];



(*(*With Lorentz*)
ClearAll[ConstructIndependentSU2Basis];
Options[ConstructIndependentSU2Basis] = Join[Options@ConstructCFIByFakeDim, Options@ConstructIndependentSU2Basis] // DeleteDuplicates;
ConstructIndependentSU2Basis[spins_List, physicalDim_Integer, gaugeShapeList_ : {}, identicalParam_ : {}, opts : OptionsPattern[]] := Module[{identicalList, TimingTest, fakeDimList, fakeDimResult, gaugeIndDict, gaugeBasis, gaugeIdenticalOpDict, exprDict, fakeDimBasis},
   TimingTest[message_] := (# // AbsoluteTiming // (If[OptionValue@log, LogPri[message, #[[1]]];]; #[[2]]) &) &;
   
   (*Basis info*)
   If[identicalParam === {}, identicalList = {}, identicalList = (#~Append~If[OddQ[2*spins[[#[[1]]]]], "A", "S"]) & /@ identicalParam;];
   
   (*Calc SU2 Permutation*)
   {gaugeIndDict, gaugeBasis, gaugeIdenticalOpDict} = AuxConstructIdenticalSU2Basis[gaugeShapeList, identicalList, FilterRules[{opts}, Options@AuxConstructIdenticalSU2Basis]] // TimingTest["construct gauge basis cost "];
   If[OptionValue@log, LogPri["involved gauge basis ", Length@gaugeBasis];];
   If[Length@gaugeBasis==0, LogPri["SU2 cancel"];Return[{}];];
   
   (*Construct Lorentz*)
   fakeDimList = CalcNeededFakeDim[spins, physicalDim, OptionValue@mass];
   If[OptionValue@log, LogPri["physical dim ", physicalDim, " involves fake dim ", fakeDimList];];
   If[Length@fakeDimList === {}, Return[{}]];
   fakeDimResult = Association@Table[fd -> ConstructCFIByFakeDim[spins, fd, FilterRules[{opts}, Options@ConstructCFIByFakeDim]], {fd, fakeDimList}] // DeleteCases[Null] // TimingTest["construct fake basis cost "];
    
   (*Calc Mixing*)
   exprDict = GetTotalPermutedPolyDict[identicalList];
   fakeDimBasis = Table[AuxConstructIdenticalSU2BasisByFakeDim[fakeDimResult[fd], physicalDim, gaugeIndDict, gaugeBasis, gaugeIdenticalOpDict, exprDict, identicalList, FilterRules[{opts}, Options@AuxConstructIdenticalSU2BasisByFakeDim]], {fd, Keys@fakeDimResult}] // TimingTest["calc identical total cost: "];
   (*The keys of fakeDimResult may be subset of fakeDimList because of some Null result from construction*)If[OptionValue@log, LogPri["fake dim ", fakeDimList, " contribute ", Length /@ fakeDimBasis]];
   Return[fakeDimBasis // Flatten[#, 1] &];];

Options[AuxConstructIdenticalSU2BasisByFakeDim] = Options[CalcPermutationMatrixDictByFakeDim];
AuxConstructIdenticalSU2BasisByFakeDim[result : {icfs_, data_}, phyDim_, gaugeIndDict_, gaugeBasis_, gaugeIdenticalOpDict_, exprDict_, identicalList_, opts : OptionsPattern[]] := Module[{separatedOperatorDict, phyOperatorDict, GetGaugeCfBasis, CombineOpDict, gaugePhyOperatorDict, GetTotalOperator, GetIndependentBasisByTotalOp},
   (*Calc Lorentz Permutation*)
   separatedOperatorDict = CalcPermutationMatrixDictByFakeDim[result, identicalList, opts];
   If[! KeyExistsQ[separatedOperatorDict, phyDim], Return[{}]];
   phyOperatorDict = separatedOperatorDict[phyDim];
   (*Special:Self gauge cancel*)
   If[Length@gaugeBasis == 0, If[OptionValue@log, LogPri["Cancel gauge"];];
    Return[{}]];
   (*Expand basis*)
   GetGaugeCfBasis[cfs_] := Table[{gauge, amp}, {gauge, gaugeBasis}, {amp, cfs}] // Flatten[#, 1] &;
   (*Special:no identical*)
   If[identicalList === {}, Return[GetGaugeCfBasis[phyOperatorDict[[1]]]]];
   (*Combine gauge and amp*)CombineOpDict[cOpD_, lOpD_] := Block[{cOpDict = cOpD, ToIdentity, temp}, If[Length@cOpDict =!= Length@lOpD,
      ToIdentity[rule_] := rule[[1]] -> IdentityMatrix[Length@gaugeBasis];
      temp = (# -> ToIdentity /@ lOpD[#]) & /@ Complement[Keys@lOpD, Keys@cOpD];
      AssociateTo[cOpDict, temp];];
     MapThread[Normal@MapThread[KroneckerProduct, {Association@#1 // KeySort, Association@#2 // KeySort}] &, {cOpDict // KeySort, lOpD // KeySort}]];
   CombineOpDict[lOpD_] := CombineOpDict[gaugeIdenticalOpDict, lOpD];
   gaugePhyOperatorDict = {GetGaugeCfBasis[phyOperatorDict[[1]]], CombineOpDict[phyOperatorDict[[2]]]};
   (*Find independent parts*)
   GetTotalOperator[opDict_] := Dot @@ Table[exprDict[id] /. opDict[id], {id, identicalList}];
   GetIndependentBasisByTotalOp[{basis_, opDict_}] := basis[[#]] & /@ FindIndependentBasisPos[GetTotalOperator[opDict]];
   GetIndependentBasisByTotalOp@gaugePhyOperatorDict // Return;];
ClearAll[CheckIdenticalVaild];
CheckIdenticalVaild[gaugeList_List,identicalParam_List]:=And[
And@@Table[Length@e>1,{e,identicalParam}],
And@@Flatten@Table[Table[e[[1]]===e[[k]],{k,2,Length@e}],{e,identicalParam}]
]*)


(*Mixing *)
ClearAll[ConstructIndependentSU2SU3Basis];
Options[ConstructIndependentSU2SU3Basis] = Join[Options@ConstructCFIByFakeDim, Options@ConstructIndependentSU2Basis] // DeleteDuplicates;
ConstructIndependentSU2SU3Basis[spins_List, physicalDim_Integer, su2ShapeList_ : {},su3ShapeList_ : {}, identicalParam_ : {}, opts : OptionsPattern[]] := Module[{identicalList, TimingTest, fakeDimList, fakeDimResult,su2R,su3R, su2IndDict, su2Basis, su2IdenticalOpDict, su3IndDict, su3Basis, su3IdenticalOpDict, exprDict, fakeDimBasis},
   
TimingTest[message_] := (# // AbsoluteTiming // (If[OptionValue@log, LogPri[message, #[[1]]];]; #[[2]]) &) &;
(*Basis info*)
If[identicalParam === {}, identicalList = {}, identicalList = (#~Append~If[OddQ[2*spins[[#[[1]]]]], "A", "S"]) & /@ identicalParam;];
(*Calc SU2 Permutation*)
{su2IndDict, su2Basis, su2IdenticalOpDict} = su2R=AuxConstructIdenticalSU2Basis[su2ShapeList, identicalList, FilterRules[{opts}, Options@AuxConstructIdenticalSU2Basis]] // TimingTest["construct su2 basis cost "];If[OptionValue@log, LogPri["involved su2 basis ", Length@su2ShapeList];];
(*Calc SU3 Permutation*)
{su3IndDict, su3Basis, su3IdenticalOpDict} = su3R=AuxConstructIdenticalColorBasis[su3ShapeList, identicalList,IYT, FilterRules[{opts}, Options@AuxConstructIdenticalColorBasis]] // TimingTest["construct su3 basis cost "];If[OptionValue@log, LogPri["involved su3 basis ", Length@su3ShapeList];];
(*Special case*)
If[Length@su2Basis==0||Length@su3Basis==0,
	LogPri["su2|su3 cancel"];
	Return[{}];
];

(*Construct Lorentz*)
fakeDimList = CalcNeededFakeDim[spins, physicalDim, OptionValue@mass];
If[OptionValue@log, LogPri["physical dim ", physicalDim, " involves fake dim ", fakeDimList];];
If[Length@fakeDimList === {}, Return[{}]];
fakeDimResult = Association@Table[fd -> ConstructCFIByFakeDim[spins, fd, FilterRules[{opts}, Options@ConstructCFIByFakeDim]], {fd, fakeDimList}] // DeleteCases[Null] // TimingTest["construct fake basis cost "];

(*Calc Mixing*)
exprDict = GetTotalPermutedPolyDict[identicalList];
fakeDimBasis = Table[AuxConstructIdenticalSU2SU3BasisByFakeDim[fakeDimResult[fd], physicalDim,su2R,su3R,exprDict, identicalList, FilterRules[{opts}, Options@AuxConstructIdenticalSU2BasisByFakeDim]], {fd, Keys@fakeDimResult}] // TimingTest["calc identical total cost: "];
   (*The keys of fakeDimResult may be subset of fakeDimList because of some Null result from construction*)If[OptionValue@log, LogPri["fake dim ", fakeDimList, " contribute ", Length /@ fakeDimBasis]];
   Return[fakeDimBasis // Flatten[#, 1] &];];

ClearAll[AuxConstructIdenticalSU2SU3BasisByFakeDim];
Options[AuxConstructIdenticalSU2SU3BasisByFakeDim]=Options[CalcPermutationMatrixDictByFakeDim];

AuxConstructIdenticalSU2SU3BasisByFakeDim[result:{icfs_,data_},phyDim_,su2R:{su2IndDict_,su2Basis_,su2IdenticalOpDict_},su3R:{su3IndDict_,su3Basis_,su3IdenticalOpDict_},exprDict_,identicalList_,opts:OptionsPattern[]]:=Module[{separatedOperatorDict,phyOperatorDict,GetGaugeCfBasis,gaugePhyOperatorDict,GetTotalOperator,GetIndependentBasisByTotalOp,su2opDict2,su3opDict2,lorentzOpDict2,ToIdentitySU2,ToIdentitySU3,temp},
(*Calculate Lorentz Permutation*)
separatedOperatorDict=CalcPermutationMatrixDictByFakeDim[result,identicalList,opts];
If[!KeyExistsQ[separatedOperatorDict,phyDim],Return[{}]];
phyOperatorDict=separatedOperatorDict[phyDim];
(*Special:Self gauge cancel*)
If[Length@su2IndDict==0,If[OptionValue@log,LogPri["su2 Cancel"];];Return[{}]];
If[Length@su3IndDict==0,If[OptionValue@log,LogPri["su3 Cancel"];];Return[{}]];
(*Expand basis*)
GetGaugeCfBasis[cfs_]:=Table[{su2,su3,amp},{su2,su2Basis},{su3,su3Basis},{amp,cfs}]//Flatten[#,2]&;
(*Special:No identical*)
If[identicalList==={},Return[GetGaugeCfBasis[phyOperatorDict[[1]]]]];
(*Combine gauge and amp logic in-place*)
su2opDict2=su2IdenticalOpDict;
su3opDict2=su3IdenticalOpDict;
lorentzOpDict2=phyOperatorDict[[2]];
(*Adjust su2opDict2 to match length of lorentzOpDict2*)
If[
Length@su2opDict2=!=Length@lorentzOpDict2,
ToIdentitySU2[rule_]:=rule[[1]]->IdentityMatrix[Length@su2Basis];
temp=(#->ToIdentitySU2/@lorentzOpDict2[#])&/@Complement[Keys@lorentzOpDict2,Keys@su2opDict2];
AssociateTo[su2opDict2,temp];
];
(*Adjust su3opDict2 to match length of lorentzOpDict2*)
If[Length@su3opDict2=!=Length@lorentzOpDict2,
ToIdentitySU3[rule_]:=rule[[1]]->IdentityMatrix[Length@su3Basis];
temp=(#->ToIdentitySU3/@lorentzOpDict2[#])&/@Complement[Keys@lorentzOpDict2,Keys@su3opDict2];
AssociateTo[su3opDict2,temp];
];
(*Sort dictionaries*)
su2opDict2=KeySort@su2opDict2;
su3opDict2=KeySort@su3opDict2;
lorentzOpDict2=KeySort@lorentzOpDict2;
(*Combine operators using MapThread*)
gaugePhyOperatorDict={
GetGaugeCfBasis[phyOperatorDict[[1]]],MapThread[Normal@MapThread[KroneckerProduct,{Association@#1//KeySort,Association@#2//KeySort,Association@#3//KeySort}]&,{su2opDict2,su3opDict2,lorentzOpDict2}]};
(*Find independent parts*)
GetTotalOperator[opDict_]:=Dot@@Table[exprDict[id]/. opDict[id],{id,identicalList}];
GetIndependentBasisByTotalOp[{basis_,opDict_}]:=basis[[#]]&/@FindIndependentBasisPos[GetTotalOperator[opDict]];
GetIndependentBasisByTotalOp@gaugePhyOperatorDict//Return;
];

