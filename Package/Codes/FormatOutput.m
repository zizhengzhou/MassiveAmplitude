(* ::Package:: *)

LogPri["FormatOutput Loaded"];
ClearAll[DisplayYT];
DisplayYT::usage =
  "DisplayYT[yt] displays a Young-tableau-like list or IYT expression as a framed Grid.";
DisplayYT[warpedYt_, h_ : IYT] /; Head@warpedYt === h := DisplayYT[warpedYt[[1]]];
DisplayYT[yt_List] := Grid[yt, Frame -> {None, None,
  Flatten@Table[{i, j} -> True, {i, Length@yt}, {j,
    Length@yt[[i]]}]}];
DisplayYT[ytExpr_Plus, h_ : IYT] := DisplayYT[#, h]& /@ Sum2List[ytExpr] // Total;
DisplayYT[ytExpr_Times, h_ : IYT] := Times @@ (DisplayYT[#, h]& /@ Prod2List[ytExpr]);
DisplayYT[ytExpr_, h_ : IYT] /; NumberQ@ytExpr := ytExpr;

(*
\newcommand{\abk}[1] {\left\langle #1\right\rangle}
\newcommand{\sbk}[1] {\left[#1\right]}
*)
(*defaultAbkFun = "\\abk{" <> # <> "}"&;*)
(*defaultSbkFun = "\\sbk{" <> # <> "}"&;*)
(*TODO deal with minus*)
ClearAll[defaultAbkFun,defaultSbkFun,ExportAmp2Tex,ExportAmpMassive2Tex];
ExportAmp2Tex::usage =
  "ExportAmp2Tex[amp] exports a spinor-helicity amplitude to a compact TeX string. Custom angle and square bracket formatters may be supplied.";
ExportAmpMassive2Tex::usage =
  "ExportAmpMassive2Tex[n][amp] exports an n-point massive amplitude after relabeling conjugate massive spinors with primed labels.";
defaultAbkFun = "\\left\\langle " <> # <> "\\right\\rangle"&;
defaultSbkFun = "\\left[" <> # <> "\\right]"&;
ab /: ExportAmp2Tex[ab[i_, j_], abkFun_, sbkFun_] := abkFun[ToString@i <> ToString@j];
sb /: ExportAmp2Tex[sb[i_, j_], abkFun_, sbkFun_] := sbkFun[ToString@i <> ToString@j];
ExportAmp2Tex[n_?NumberQ, abkFun_, sbkFun_] := If[Denominator@n == 1, ToString@n,
  "\\frac{" <> ToString@Numerator@n <> "}{" <> ToString@Denominator@n <> "} "];
ExportAmp2Tex[l_List, abkFun_, sbkFun_] := ExportAmp2Tex[#, abkFun, sbkFun]& /@ l;
ExportAmp2Tex[expr_Times, abkFun_, sbkFun_] := StringJoin@ExportAmp2Tex[Prod2List[expr], abkFun, sbkFun];
ExportAmp2Tex[expr_Plus, abkFun_, sbkFun_] := ExportAmp2Tex[Sum2List@expr, abkFun, sbkFun] // StringRiffle[#, "+"]&;
ExportAmp2Tex[expr_] := ExportAmp2Tex[expr, defaultAbkFun, defaultSbkFun];
ExportAmpMassive2Tex[np_Integer] := ExportAmp2Tex[Last@FactorizeBracket@#& /@ ReplaceBraNumber[
  Table[(2 * np + 1 - i) -> ToString@i <> "^{\\prime}", {i, 1, np}]
][#]]&;


ClearAll[allowedLorentz,generalRules,defaultExternalRules,FieldTranslationRule,WrapBra,ExtractIndsWithLabel];
allowedLorentz = {"\[Mu]", "\[Nu]", "\[Rho]", "\[Xi]", "\[Tau]", "\[Zeta]", "\[Eta]", "\[Theta]", "\[Iota]", "\[Kappa]", "\[Lambda]"};

generalRules = {
  {"Tr"} -> "\\operatorname{Tr}",
  {"braL"} -> "\\left(",
  {"braR"} -> "\\right)",
  {"D", n_, i_} :> StringJoin["D_{", i, "}"],
  {"MT", i_, j_} :> StringJoin["g^{", i, j, "}"],
  {"\[Sigma]", ids__} :> StringJoin["\\sigma^{", ids, "}"],
  {"\[Sigma]Bar", ids__} :> StringJoin["\\bar{\\sigma}^{", ids, "}"],
  {"\[Epsilon]", ids__} :> StringJoin["\\epsilon_{", ids, "}"],
  {"\[Epsilon]i", ids__} :> StringJoin["\\epsilon^{", ids, "}"]
};

defaultExternalRules = {
  {"\[Phi]", n_, o___} :> StringJoin["\\phi_", "{", ToString@n ,"}^{", o, "}"],
  {"\[Psi]", n_Integer, r_, i_, o___} :>
    StringJoin["{\\psi}_{", ToString@n, i, ",", r, "}", "^{", o, "}"],
  {"\[Psi]bar", n_Integer, r_, i_, o___} :>
    StringJoin["{\\psi}_{", ToString@n, i, ",", r, "}", "^{\\dagger\\ ", o, "}"],
  {"\[Psi]", n_Integer, r_, o___} :>
    StringJoin["{\\psi}_{", ToString@n, ",", r, "}", "^{", o, "}"],
  {"\[Psi]bar", n_Integer, r_, o___} :>
    StringJoin["{\\psi}_{", ToString@n, ",", r, "}", "^{\\dagger\\ ", o, "}"],
  {"A", n_, i_, o___} :>
    StringJoin["{A}_{", ToString@n, ",", i, "}", "^{", o, "}"],
  {"F+", n_, i_, j_, o___} :>
    StringJoin["{F}_{", ToString@n, ",", i, " ", j, "}", "^{+\\ ", o, "}"],
  {"F-", n_, i_, j_, o___} :>
    StringJoin["{F}_{", ToString@n, ",", i, " ", j, "}", "^{-\\ ", o, "}"]
};

FieldTranslationRule[n_Integer, {field_String}]:=FieldTranslationRule[n, {field, ""}];
FieldTranslationRule[n_Integer, {field_String, fieldLongitude_String}] := {
  {"\[Phi]", n, o___} :> StringJoin["{", field, "}^{", o, "}"],
  {"\[Psi]", n, r_, i_, o___} :>
    StringJoin["{", field, "}_{", i, ",", r, "}", "^{", o, "}"],
  {"\[Psi]bar", n, r_, i_, o___} :>
    StringJoin["{", field, "}_{", i, ",", r, "}", "^{\\dagger\\ ", o, "}"],
  {"\[Psi]", n, r_, o___} :>
    StringJoin["{", field, "}_{", r, "}", "^{", o, "}"],
  {"\[Psi]bar", n, r_, o___} :>
    StringJoin["{", field, "}_{", r, "}", "^{\\dagger\\ ", o, "}"],
  {"A", n, i_, o___} :>
    StringJoin["{", If[fieldLongitude != "", fieldLongitude, field], "}_{", i, "}", "^{", o, "}"],
  {"F+", n, i_, j_, o___} :>
    StringJoin["{", field, "}_{", i, " ", j, "}", "^{+\\ ", o, "}"],
  {"F-", n, i_, j_, o___} :>
    StringJoin["{", field, "}_{", i, " ", j, "}", "^{-\\ ", o, "}"]
};

(* Add parentheses *)
WrapBra[expr___] := {{"braL"}, expr, {"braR"}};

ExtractIndsWithLabel[label_String][obj_List] :=
  Cases[obj, s_Symbol /; StringMatchQ[SymbolName[s], label <> "$" ~~ ___], Infinity] // DeleteDuplicates // Sort;



ClearAll[ExportWeylOp2Tex]
ExportWeylOp2Tex::usage =
  "ExportWeylOp2Tex[weylChain, opts] exports a Weyl-operator chain to TeX.";
antiFermionList::usage="position of anti-fermion. use this option to flip psi and add dagger.";
externalFieldNamesDict::usage="
Default value is  string Default.
Use non-default name to translate field. Key should be particle num, values should be list of name strings.
Example external-><|1->{W^+,W^+},2->{W^-,W^-},3->{g,G},4->{A,F},5->{\\nu_e},6->{e}|>";
Options[ExportWeylOp2Tex]={antiFermionList->{},externalFieldNamesDict->"Default"};
ExportWeylOp2Tex[weylOpChain_List,OptionsPattern[]]:=Module[{a,b,antiFermionPos,externalRules,chains,psis,psisDs,psisAttachDRule,lorentzIds,su2Indices,su3Indices,lorentzRules,su2Rules,su3Rules,result},
(*Initialize chains*)
chains=weylOpChain;
(*Extract options*)
antiFermionPos=OptionValue[antiFermionList];
externalRules=If[OptionValue[externalFieldNamesDict]==="Default",
defaultExternalRules,
Join@@KeyValueMap[FieldTranslationRule,Flatten/@List/@OptionValue[externalFieldNamesDict]]];
(*Handle Tr*)
chains=chains/. {{"Tr"},o___}:>Sequence@@{{"Tr"},Sequence@@WrapBra@o};
(*Handle Psi*)
psis=Cases[chains,{"\[Psi]",n_,___},Infinity];
psisDs=Association@Table[psi->SortBy[Last]@Cases[chains,{"D",psi[[2]],_}],{psi,psis}];
psisAttachDRule=Association@Table[psi->Sequence@@WrapBra[Sequence@@(psisDs[psi]),psi],{psi,psis}];
chains=Fold[DeleteCases,Join[{chains},Flatten[#,1]&@Values@psisDs]];
chains=chains/. {chain:{{"\[Psi]",n_,___},___}:>Sequence@@WrapBra[Sequence@@(chain/. psisAttachDRule)]};
(*Flip anti-fermion*)chains=chains/. {"\[Psi]",n_,r_,o___}/;MemberQ[antiFermionPos,n]:>{"\[Psi]bar",n,Sequence@@DeleteCases[{ab,sb},r],o};
chains=chains/. {{s:"\[Psi]"|"\[Psi]bar",n_,ab,o___}:>{s,n,"L",o},{s:"\[Psi]"|"\[Psi]bar",n_,sb,o___}:>{s,n,"R",o}};
(*Replace all indices*)
lorentzIds=ExtractIndsWithLabel["LI"][chains];
su2Indices=ExtractIndsWithLabel["su2"][chains];
su3Indices=ExtractIndsWithLabel["su3"][chains];
lorentzRules=Dispatch@Table[id->ToString@TeXForm@allowedLorentz[[ToExpression[StringSplit[ToString@id,"$"][[2]]]]],{id,lorentzIds}];
su2Rules=Dispatch@Table[id->StringJoin["a_{",StringSplit[ToString@id,"$"][[2]],"} "],{id,su2Indices}];
su3Rules=Dispatch@Table[id->StringJoin["b_{",StringSplit[ToString@id,"$"][[2]],"} "],{id,su3Indices}];
(*Translate all except field*)
chains=chains//.lorentzRules//.su2Rules//.su3Rules//.generalRules;
(*Translate field*)
chains=chains//.externalRules//.defaultExternalRules;
(*Check for incomplete translation*)If[Count[chains,_List]>1,Print["Warning toTex not complete! except",DeleteCases[chains,_String]]];
chains=DeleteCases[chains,_List];
(*Concatenate result*)
result=StringJoin[StringRiffle[chains," "]];
result]


Options[ExportTexList2Array] = {
  env -> "array",
  param -> "l",
  option -> "",
  prefix -> "\t",
  suffix -> "\\\\\n"
};
ExportTexList2Array::usage =
  "ExportTexList2Array[list, opts] formats a list of TeX strings as a TeX array-like environment.";
ExportTexList2Array[{}, OptionsPattern[]] := "\\text{None}\n";
ExportTexList2Array[l_List, OptionsPattern[]] /; StringQ[l[[1]]] :=
    With[{},
      If[Length@l == 1,
        l[[1]] <> "\n"
        ,
        "\\begin{" <> OptionValue@env <> "}"
            <> If[OptionValue@param =!= "" && OptionValue@param =!= Null,
          "{" <> OptionValue@param <> "}", ""]
            <> If[OptionValue@option =!= "" && OptionValue@option =!= Null,
          "[" <> OptionValue@option <> "]\n", "\n"]
            <> StringJoin[(OptionValue@prefix <> # <> OptionValue@suffix)& /@ l]
            <> "\\end{" <> OptionValue@env <> "}\n"
      ]
    ];
(*Example: "\\begin{array}{c}\n \t" <>
     StringRiffle[#, "\\\\ \n\t"] &@(# /. TraditionalForm[x_] -> x &@
      ExportWelyOp2Tex /@ (Amp2WeylOp[4]@# & /@
       ConstructIndependentBasis[{1, 1, 0, 0},
        6, {{1, 2}, {3, 4}}])) <> "\n\\end{array}" // TraditionalForm*)
(*Example: "\\begin{array}{c}\n \t" <>
     StringRiffle[#, "\\\\ \n\t"] &@(# /. TraditionalForm[x_] -> x &@
      ExportWelyOp2Tex /@ (Amp2WeylOp[4]@# & /@
       ConstructIndependentBasis[{1, 1, 0, 0},
        6, {{1, 2}, {3, 4}}])) <> "\n\\end{array}" // TraditionalForm*)
