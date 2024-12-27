(* ::Package:: *)

LogPri["SSYT Loaded"];



(* ::Section:: *)
(*SSYT*)


ClearAll[TransposeYoung, RecoverYoung, SSYTfillingInner, SSYT, StrangeSSYT];
TransposeYoung[Young1_] := Module[{L1, Positions, Newlist,MaxLength},
  Positions = Flatten[MapIndexed[Function[{sublist, idx}, MapIndexed[{idx, #2[[1]]} &, sublist]], Young1], 1];
MaxLength=Max[Length[Young1[[1]]],Length[Young1]];
  Newlist = ConstantArray[0, {MaxLength, MaxLength}];
  Do[Newlist[[Positions[[i, 1, 1]], Positions[[i, 2]]]] = 1, {i, 1, Length[Positions]}];
  Newlist = Newlist // Transpose;
  Newlist = Select[#, # != 0 &] & /@ Newlist;
  Newlist =DeleteCases[ Newlist /. (1 -> 0),{}]
  ]
RecoverYoung[Young1_] := Module[{L1, Positions, Newlist,MaxLength},
  Positions = Table[{{i, j}, Young1[[i, j]]}, {i, 1, Length[Young1]}, {j, 1, Length[Young1[[i]]]}];
  MaxLength=Max[Length[Young1[[1]]],Length[Young1]];
  Newlist = ConstantArray[0, { MaxLength,  MaxLength}];
  Do[Newlist[[i, Positions[[i, j, 1, 2]]]] = Positions[[i, j, 2]], {i, 1, Length[Positions]}, {j, 1, Length[Positions[[i]]]}];
  Newlist = Newlist // Transpose;
  Newlist = Select[#, # != 0 &] & /@ Newlist;
  Newlist = DeleteCases[Newlist, {}]
  ] 
SSYTfillingInner[A_, filling_, n_ : 1] := Module[{f, num, pos, tal, partitions, poslist, list = {}},
  If[n > Length[filling], Return[{A}]]; {f, num} = filling[[n]]; pos = DeleteCases[Transpose[{Range[Length[A]], Flatten[(FirstPosition[#1, 0] &) /@ A]}], {_, _Missing}]; If[! OrderedQ[Reverse[pos[[All, 2]]]], Print[A, " is not a standard Young Diagram."]; Abort[]]; tal = Tally[pos[[All, 2]]]; partitions = Select[Join @@ Permutations /@ (PadRight[#1, Length[tal]] &) /@ IntegerPartitions[num, Length[tal]], And @@ Thread[#1 <= tal[[All, 2]]] &]; poslist = (Join @@ MapThread[Function[{row, part}, Take[Select[pos, #1[[2]] == row &], part]], {tal[[All, 1]], #1}] &) /@ partitions; Do[list = Join[list, SSYTfillingInner[ReplacePart[A, (#1 -> f &) /@ p], filling, n + 1]], {p, poslist}]; Return[list]]
SSYT[A_, filling_, n_ : 1] := Module[{A1, A2, A3},
  A1 = TransposeYoung[A];
  A2 = Tally[filling];
  A3 = SSYTfillingInner[A1, A2, n];
  RecoverYoung /@ A3]
StrangeSSYT[YoungD_, filling_, nt_, massivePart_] :=
    Module[ {ssyt, ntyt, posi, sel},
      posi[NumInNt_] := Position[NumInNt, #]& /@ massivePart;
      ssyt = SSYT[YoungD, filling];
      ntyt = Flatten /@ ssyt[[;;, ;;, ;; nt]];
      sel = Flatten /@ (posi /@ ntyt);
      Delete[ssyt, Complement[Array[{#}&, Length[ssyt]], Position[sel, {}]]]
    ];


(* ::Section::Closed::*)
(* SSYT To Amp*)

ab[i_, j_] /; i == j := 0 ;
ab[i_, j_] /; Signature[{i, j}] < 0 := -ab[j, i] ;
sb[i_, j_] /; i == j := 0 ;
sb[i_, j_] /; Signature[{i, j}] < 0 := -sb[j, i];

YTtoAmpmass[YT_, nt_, particleList_, OptionsPattern[]] :=
    Module[ {amp = 1},
      Do[
        amp *= ab @@ Complement[particleList, YT[[;;, ii]]];
        ,
        {ii, nt}];
      Do[
        amp *= sb @@ YT[[;; 2, ii]];
        ,
        {ii, nt + 1, Length[YT[[1]]]}];
      Return[amp];
    ];
