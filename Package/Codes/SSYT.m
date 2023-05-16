LogPri["SSYT Loaded"];

(* ::Section::Closed:: *)
(*SSYT*)
SSYT[A_, filling_, n_ : 1] :=
    Module[ {yt, pos, f, height = Length[A], list = {}},
      If[ n > Length[Flatten[A]], Return[{A}]];
      f = filling[[n]];
      pos = FirstPosition[#, 0]& /@ A // Flatten;
      Do[
        If[ MissingQ[pos[[i]]], Continue[]];
        If[ pos[[i]] > 1 && A[[i, pos[[i]] - 1]] > f, Continue[]];
        If[ i > 1 && (A[[i - 1, pos[[i]]]] == 0 || A[[i - 1, pos[[i]]]] >= f), Continue[]];
        yt = ReplacePart[A, {i, pos[[i]]} -> f];
        list = DeleteDuplicates@Join[list, SSYT[yt, filling, n + 1]];,
        {i, height}];
      Return[list];
    ];


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