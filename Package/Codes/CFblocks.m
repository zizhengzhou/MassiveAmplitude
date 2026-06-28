(* ::Package:: *)

(* ::Subsection:: *)
(*New reduce*)


(* ::Text:: *)
(*involved ConstructAmp Reduce funs*)


ClearAll[Poly2Singlet];
Poly2Singlet::usage =
  "Poly2Singlet[expr] extracts distinct monomial terms from a polynomial expression, dropping numeric coefficients.";
Poly2Singlet[amp_List] := Poly2Singlet /@ amp // Flatten // DeleteDuplicates;
Poly2Singlet[amp_Plus] := Poly2Singlet /@ (List @@ amp) // Flatten // DeleteDuplicates;
Poly2Singlet[c_?NumberQ * b_] := {b};
Poly2Singlet[-b_] := {b};
Poly2Singlet[c_?NumberQ] := {};
Poly2Singlet[b_] := {b};
ClearAll[ConstructIndepCFBlock];
Options@ConstructIndepCFBlock = {mass -> All, timeDebug -> False};
ConstructIndepCFBlock::usage =
  "ConstructIndepCFBlock[spins, codeDim, polarization, opts] constructs a fixed-polarization CF block, reduces it in the massless limit, removes local linear redundancy, and returns {independentAmplitudes, coefficientMatrix, monomialBasis}.";
ConstructIndepCFBlock[spins_List, codeDim_, polarization_List, OptionsPattern[]] := Module[{
    np = Length@spins,
    cf0, masslessLimitRule, rcfHE, basis, coeff, posIndep, TimingPrint},
   If[OptionValue@timeDebug,
    TimingPrint[label_String][{time_, result_}] := Block[{},
       Print[label <> " cost ", time, "s"];
       result];,
    TimingPrint[label_String][{time_, result_}] := result;];
   cf0 = ConstructAmp[spins, codeDim, antispinor -> polarization, mass -> OptionValue@mass] // AbsoluteTiming // TimingPrint["construct cf"];
   If[Length@cf0 == 0, Return[{}]];
   masslessLimitRule = Table[2*np + 1 - i -> i, {i, np}];
   (*Simply replacement of number for a general amplitude is dangerous.*)
   rcfHE = ReduceSt[Length@spins] /@ (ReplaceBraNumber[masslessLimitRule]/@cf0) // AbsoluteTiming // TimingPrint["reduce cfHE"];
   (*The reduce here could be improved future*)
   basis = Poly2Singlet@rcfHE // AbsoluteTiming // TimingPrint["find cfHE basis"];
   If[Length@basis == 0, Return[{}]];
   coeff = Table[Coefficient[a, b], {a, rcfHE}, {b, basis}];
   posIndep = FindIndependentBasisPos[coeff];
   {cf0[[posIndep]], coeff[[posIndep]], basis}
   ];


(* ::Subsection:: *)
(*CF blocks*)


ClearAll[GetDCodeListUpdate,ClassifyPolarsByIdentical,MergeIdenticalClassification];
GetDCodeListUpdate[spinList_, phyDim_, massList_] := Module[{positions, dimEva, nAmin, codeDimList, codeDimListRule, nAList, newLists, correspondences, np, polar, modifiedL1, polarChoiceList, finalCombo},(*Compute positions where spinList and massList are non-zero*)positions = Select[Range[Length[spinList]], spinList[[#]] != 0 && massList[[#]] != 0 &];
   (*Evaluate total dimension*)dimEva = Total[(Abs[spinList] /. {1 -> 2, 0 -> 1, 1/2 -> 3/2, 3/2 -> 5/2})];
   (*Check for invalid dimensions*)If[(dimEva - Length[positions]) > phyDim || ! IntegerQ[dimEva], {}];
   (*Compute minimum and maximum nA values*)nAmin = Max[dimEva - phyDim, 0];
   codeDimList = Table[{i1, phyDim + i1}, {i1, nAmin, Length[positions]}];
   codeDimListRule = Rule @@@ codeDimList;
   nAList = Table[i1, {i1, nAmin, Length[positions]}];
   newLists = Table[Range[0, 2*num], {num, Abs[spinList]}];
   correspondences = Table[Table[newLists[[a]][[Length[newLists[[a]]] - i + 1]] -> newLists[[a, i]], {i, 1, Floor[Length[newLists[[a]]]/2]}], {a, 1, Length[newLists]}];
   np = Length[massList];
   polar = Fold[(Flatten[#, 1] &@Table[l~Append~i, {l, #1}, {i, 0, If[massList[[#2]] === 0, 0, 2*spinList[[#2]]]}]) &, {{}}, Range[np]] // DeleteCases[ConstantArray[0, np]];
   modifiedL1 = Table[(polar[[a, i]] /. correspondences[[i]]), {a, 1, Length[polar]}, {i, 1, Length[correspondences]}];
   polar = Table[{Total[modifiedL1[[i]]], polar[[i]]}, {i, 1, Length[polar]}];
   polar = Append[polar, {0, ConstantArray[0, np]}];
   polarChoiceList = Select[polar, MemberQ[nAList, #[[1]]] &];
   (*Compute final combinations*)
   finalCombo = {#[[1]] /. codeDimListRule, #[[2]]} & /@ polarChoiceList;
   finalCombo // SortBy[First]];
ClearAll[GenerateNeedCFBlocks];
Options@GenerateNeedCFBlocks = {mass -> All};
GenerateNeedCFBlocks::usage =
  "GenerateNeedCFBlocks[spins, physicalDim, opts] returns the code dimensions and polarization sectors needed by the legacy CF-block pipeline at a physical dimension.";
GenerateNeedCFBlocks[spins_, physicalDim_, OptionsPattern[]] := GetDCodeListUpdate[spins, physicalDim, MassOption[OptionValue@mass, Length@spins]];


(* ::Subsection:: *)
(*help identical function*)


ClearAll[FilterCFBlocksByIdentical,ReAssignIdentical];
FilterCFBlocksByIdentical[cfBlocks_List, identicals_List] := Module[{identicalList,CheckValid,selected},
If[Length@cfBlocks == 0, Return[{}]];
If[Length@identicals == 0, Return[cfBlocks]];
identicalList=If[!IntegerQ[#[[-1]]],Most[#],#]&/@identicals;
CheckValid[{d_Integer, polar_List}, pos_List] :=   OrderedQ[polar[[pos]]];
CheckValid[pos_List]:=CheckValid[#,pos]&;
selected=Fold[Select,cfBlocks,CheckValid/@identicalList]
     ];
ReAssignIdentical[polar_List,identicals_List]:=Module[{result={},grouped,type,positions,values},
If[Length@identicals==0,Return[{}]];
Do[
positions=Most[id];
type=Last[id];
values=polar[[positions]];
grouped=GroupBy[Transpose[{positions,values}],Last->First];
Do[If[Length[g[[2]]]>1,AppendTo[result,Append[g[[2]],type]]],{g,Normal[grouped]}],{id,identicals}];
result];
ReAssignIdentical[{d_Integer, polar_List},identicals_List]:=ReAssignIdentical[polar,identicals];


ClearAll[GetCFBlockPermuteOperatorDict];
GetCFBlockPermuteOperatorDict[cfBlock:{cfs_List,coeffs_List,basis_List},identicals_List,np_Integer]:=Module[{operatorDict,masslessLimitRule,masslessLimitCF,CalcRuleMatrix,rules},
operatorDict=Association@Table[id->Null,{id,identicals}];
masslessLimitRule=Table[2*np+1-i->i,{i,np}];
masslessLimitCF=ReplaceBraNumber[masslessLimitRule]/@cfs;
CalcRuleMatrix[{}]:=IdentityMatrix[Length[cfs]];
CalcRuleMatrix[rule_]:=Module[{rcfs,ruleMatrix},
rcfs=Table[ReduceSt[np][ReplaceBraNumber[rule][amp]],{amp,masslessLimitCF}];
ruleMatrix=Table[Coefficient[a,b],{a,rcfs},{b,basis}];
(*OC0=C1 -->  O = (LinearSolve[C0T,C1T])T*)
Transpose@LinearSolve[Transpose[coeffs],Transpose[ruleMatrix]]];
Do[rules=GetMasslessIdenticalRules[id];
Which[
Length[rules]==1,operatorDict[id]={1->IdentityMatrix[Length[cfs]]},
Length[rules]==2,operatorDict[id]={1->IdentityMatrix[Length[cfs]],symPermuteFirst->CalcRuleMatrix[rules[[2]]]},
True,operatorDict[id]={1->IdentityMatrix[Length[cfs]],symPermuteFirst->CalcRuleMatrix[rules[[2]]],symPermuteAll[-1+Length[id]]->CalcRuleMatrix[rules[[3]]]}],{id,identicals}];
Return[operatorDict];];


ClearAll[AttachSUNBlocks];
(*Apply SUN blocks*)
(*Assume Keys@gaugeBasisOpDict as subset of originalBasisOpDict*)
AttachSUNBlocks[gaugeBasisHere_, gaugeBasisOpDict_, originalBasis_, originalBasisOpDict_] := Module[{CombineOpDict, gaugedBasis},
If[Length@gaugeBasisHere==0||Length@originalBasis==0,Return[{{},   <||>}]];
gaugedBasis = Table[Flatten[{gauge, b}], {gauge, gaugeBasisHere}, {b, originalBasis}] // Flatten[#, 1] &;
If[Length@originalBasisOpDict==0, Return[{gaugedBasis,originalBasisOpDict}];];CombineOpDict[cOpD_, lOpD_] := Module[{cOpD2 = cOpD, ToIdentity, temp2},
        If[Length@cOpD =!= Length@lOpD,
        ToIdentity[rule_] := rule[[1]] -> IdentityMatrix[Length@gaugeBasisHere];
        temp2 = (# -> ToIdentity /@ lOpD[#]) & /@ Complement[Keys@lOpD, Keys@cOpD];
         AssociateTo[cOpD2, temp2];];
       MapThread[Normal@MapThread[KroneckerProduct, {KeySort@Association@#1 , KeySort@Association@#2}] &, {KeySort@cOpD2 , KeySort@lOpD }]
       ];
     {gaugedBasis, CombineOpDict[gaugeBasisOpDict, originalBasisOpDict]}
     ];


(* ::Subsection:: *)
(*ConstructGeneralBasis*)


ClearAll[ConstructGeneralBasis];
su2ShapeList::usage="As an option identifies the su2 type of particles. Either {} or a list with length of spins. Each element should be in Keys@su2ShapeDict";
su3ShapeList::usage="As an option identifies the su3 type of particles. Either {} or a list with length of spins. Each element should be in Keys@su3ShapeDict";
Options[ConstructGeneralBasis]={mass->All,su2ShapeList->{},su3ShapeList->{},log->False};
ConstructGeneralBasis[spins_List,physicalDim_Integer,identicalParam_List,opts:OptionsPattern[]]:=Module[{masses,np,identicalList,cfBlocks,identicalCFBlocks,cfBlocksDict,identicalInfoDict,allSubIdenticals,cfIdenticalDict,identicalYExprDict,finalBasisDict,finalIdenticalOpDict,re,ConstructSU2Blocks,ConstructSU3Blocks,ConstructSUNBlocks,GetTotalYOp,GetIndependentBasisByY},masses=MassOption[OptionValue[mass],Length@spins];
np=Length@spins;
If[identicalParam==={},identicalList={},identicalList=(#~Append~If[OddQ[2*spins[[#[[1]]]]],"A","S"])&/@identicalParam];
(*Lorentz blocks*)
cfBlocks=GenerateNeedCFBlocks[spins,physicalDim,mass->masses];
If[Length@cfBlocks==0,If[OptionValue[log],Print["no cf block!"];];
Return[{}];];
(*identical filter on cf*)
identicalCFBlocks=FilterCFBlocksByIdentical[cfBlocks,identicalParam];
If[OptionValue[log],Print["identical remove:",Length@cfBlocks-Length@identicalCFBlocks," blocks remain ",Length@identicalInfoDict];];
cfBlocks=identicalCFBlocks;
Print[cfBlocks];
(*Lorentz cancel filter on cf*)AbsoluteTiming@Block[{},cfBlocksDict=Association@Table[block->ConstructIndepCFBlock[spins,block[[1]],block[[2]],mass->masses],{block,cfBlocks}];
cfBlocksDict=cfBlocksDict//DeleteCases[{}];]//If[OptionValue[log],Print["construct cf cost ",#[[1]],"s"]]&;
Print[cfBlocksDict];
If[OptionValue[log],Print["Lorentz cancel remove:",Length@cfBlocks-Length@cfBlocksDict," blocks remain ",Length@cfBlocksDict];];
cfBlocks=Keys@cfBlocksDict;
(*Calc sub identical types*)
identicalInfoDict=Association@Table[block->ReAssignIdentical[block,identicalList],{block,cfBlocks}];
allSubIdenticals=Values@identicalInfoDict//DeleteDuplicates;
(*Calc permutation ops*)AbsoluteTiming@Block[{},cfIdenticalDict=AssociationThread[cfBlocks,KeyValueMap[GetCFBlockPermuteOperatorDict[cfBlocksDict[#1],#2,np]&,identicalInfoDict]];]//If[OptionValue[log],Print["identical Op cost ",#[[1]],"s"]]&;
AbsoluteTiming@Block[{},identicalYExprDict=GetTotalPermutedPolyDict[DeleteDuplicates@Flatten[allSubIdenticals,1]];]//If[OptionValue[log],Print["identical expr cost ",#[[1]],"s"]]&;
(*Gauge blocks*)(*Construct SU2 blocks*)ConstructSU2Blocks[identicalList_List]:=Module[{su2IndDict,su2Basis,su2IdenticalOpDict},{su2IndDict,su2Basis,su2IdenticalOpDict}=AuxConstructIdenticalSU2Basis[OptionValue[su2ShapeList],identicalList,FilterRules[{opts},Options[AuxConstructIdenticalSU2Basis]]];
If[OptionValue[log],LogPri["involved su2 basis ",Length[su2Basis],"on identical as ",identicalList];];
If[Length[su2Basis]==0,If[OptionValue[log],Print["SU2 cancel at identical=",identicalList]];
Return[{{},{}}];];
Return[{su2Basis,su2IdenticalOpDict}];];
(*Construct SU3 blocks*)
ConstructSU3Blocks[identicalList_List]:=Module[{su3IndDict,su3Basis,su3IdenticalOpDict},{su3IndDict,su3Basis,su3IdenticalOpDict}=AuxConstructIdenticalColorBasis[OptionValue[su3ShapeList],identicalList,IYT];
If[OptionValue[log],LogPri["involved su3 basis ",Length[su3Basis],"on identical as ",identicalList];];
If[Length[su3Basis]==0,If[OptionValue[log],Print["SU3 cancel at identical=",identicalList]];
Return[{{},{}}];];
Return[{su3Basis,su3IdenticalOpDict}];];
ConstructSUNBlocks[suNshape_List,ConstructSUNBlocks_]:=Module[{suNSubIdenticals,reserveIdenticalsDict,suNIdenticalDict,suNBasis,suNIdenticalOpDict,temp},
suNSubIdenticals=Select[(Union[suNshape[[Most@#]]]=!={""})&]/@allSubIdenticals;
reserveIdenticalsDict=AssociationThread[allSubIdenticals,suNSubIdenticals];
Print[];
suNIdenticalDict=Association@Table[id->ConstructSUNBlocks[id],{id,suNSubIdenticals}];
suNBasis=suNIdenticalDict[reserveIdenticalsDict@identicalInfoDict@#][[1]]&;
suNIdenticalOpDict=suNIdenticalDict[reserveIdenticalsDict@identicalInfoDict@#][[2]]&;
temp=Association@Table[cfBlockInfo->AttachSUNBlocks[suNBasis[cfBlockInfo],suNIdenticalOpDict[cfBlockInfo],finalBasisDict[cfBlockInfo],finalIdenticalOpDict[cfBlockInfo]],{cfBlockInfo,cfBlocks}];
Do[finalBasisDict[cfBlockInfo]=temp[cfBlockInfo][[1]];
finalIdenticalOpDict[cfBlockInfo]=temp[cfBlockInfo][[2]];,{cfBlockInfo,cfBlocks}];];
finalBasisDict=First/@cfBlocksDict;
finalIdenticalOpDict=cfIdenticalDict;
If[Count[OptionValue@su3ShapeList,""]<Length@OptionValue@su3ShapeList,ConstructSUNBlocks[OptionValue@su3ShapeList,ConstructSU3Blocks];];
If[Count[OptionValue@su2ShapeList,""]<Length@OptionValue@su2ShapeList,ConstructSUNBlocks[OptionValue@su2ShapeList,ConstructSU2Blocks];];
(*Find independent parts*)
GetTotalYOp[yopDict_,identiacals_]:=Dot@@Table[identicalYExprDict[id]/. yopDict[id],{id,identiacals}];
GetIndependentBasisByY[basis_,opDict_,identiacals_]:=If[Length@identicalParam>0,basis[[#]]&/@FindIndependentBasisPos[GetTotalYOp[opDict,identiacals]],basis];
GetIndependentBasisByY[basis_,<||>,_]:=basis;
GetIndependentBasisByY[basis_,_,{}]:=basis;
re=Association@Table[cfBlockInfo->GetIndependentBasisByY[finalBasisDict[cfBlockInfo],finalIdenticalOpDict[cfBlockInfo],identicalInfoDict[cfBlockInfo]],{cfBlockInfo,cfBlocks}]//DeleteCases[{}];
Join@@Values@re];
