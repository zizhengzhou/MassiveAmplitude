(* ::Package:: *)

(* ::Section:: *)
(*Model Def*)


(* ::Subsection:: *)
(*DP model*)


ClearAll@DPModelAboveEW;
DPModelAboveEW = <||>;
DPModelAboveEW["GL"] = <|"spin" -> -1, "mass" -> 0, "U1Y" -> 0, "SU2" -> "", "SU3" -> "g", "field name" -> "G"|>;
DPModelAboveEW["GR"] = <|"spin" -> +1, "mass" -> 0, "U1Y" -> 0, "SU2" -> "", "SU3" -> "g", "field name" -> "G"|>;
DPModelAboveEW["WL"] = <|"spin" -> -1, "mass" -> 0, "U1Y" -> 0, "SU2" -> "2", "SU3" -> "", "field name" -> "W"|>;
DPModelAboveEW["WR"] = <|"spin" -> +1, "mass" -> 0, "U1Y" -> 0, "SU2" -> "2", "SU3" -> "", "field name" -> "W"|>;
DPModelAboveEW["BL"] = <|"spin" -> -1, "mass" -> 0, "U1Y" -> 0, "SU2" -> "", "SU3" -> "", "field name" -> "B"|>;
DPModelAboveEW["BR"] = <|"spin" -> +1, "mass" -> 0, "U1Y" -> 0, "SU2" -> "", "SU3" -> "", "field name" -> "B"|>;
DPModelAboveEW["L"] = <|"spin" -> -1/2, "mass" -> 0, "U1Y" -> -1/2, "SU2" -> "1", "SU3" -> "", "field name" -> "L"|>;
DPModelAboveEW["Lbar"] = <|"spin" -> +1/2, "mass" -> 0, "U1Y" -> +1/2, "SU2" -> "1", "SU3" -> "", "field name" -> "L"|>;
DPModelAboveEW["e"] = <|"spin" -> +1/2, "mass" -> 0, "U1Y" -> -1, "SU2" -> "", "SU3" -> "", "field name" -> "e"|>;
DPModelAboveEW["ebar"] = <|"spin" -> -1/2, "mass" -> 0, "U1Y" -> +1, "SU2" -> "", "SU3" -> "", "field name" -> "e"|>;
DPModelAboveEW["q"] = <|"spin" -> -1/2, "mass" -> 0, "U1Y" -> 1/6, "SU2" -> "1", "SU3" -> "q", "field name" -> "q"|>;
DPModelAboveEW["qbar"] = <|"spin" -> +1/2, "mass" -> 0, "U1Y" -> -1/6, "SU2" -> "1", "SU3" -> "aq", "field name" -> "q"|>;
DPModelAboveEW["u"] = <|"spin" -> +1/2, "mass" -> 0, "U1Y" -> 2/3, "SU2" -> "", "SU3" -> "q", "field name" -> "u"|>;
DPModelAboveEW["ubar"] = <|"spin" -> -1/2, "mass" -> 0, "U1Y" -> -2/3, "SU2" -> "", "SU3" -> "aq", "field name" -> "u"|>;
DPModelAboveEW["d"] = <|"spin" -> +1/2, "mass" -> 0, "U1Y" -> -1/3, "SU2" -> "", "SU3" -> "q", "field name" -> "d"|>;
DPModelAboveEW["dbar"] = <|"spin" -> -1/2, "mass" -> 0, "U1Y" -> +1/3, "SU2" -> "", "SU3" -> "aq", "field name" -> "d"|>;
DPModelAboveEW["H"] = <|"spin" -> 0, "mass" -> 0, "U1Y" -> 1/2, "SU2" -> "1", "SU3" -> "", "field name" -> "H"|>;
DPModelAboveEW["Hdag"] = <|"spin" -> 0, "mass" -> 0, "U1Y" -> -1/2, "SU2" -> "1", "SU3" -> "", "field name" -> "H^\\dagger"|>;
DPModelAboveEW["DP"] = <|"spin" -> 1, "mass" -> 1, "U1Y" -> 0, "SU2" -> "", "SU3" -> "", "field name" -> "X"|>;
Do[Module[{entry = DPModelAboveEW[k]}, entry["antiparticle"] = StringEndsQ[k, "bar"];
      DPModelAboveEW[k] = entry;], {k, Keys[DPModelAboveEW]}];
Do[Module[{entry = DPModelAboveEW[k]},
      If[Abs@DPModelAboveEW[k]["spin"] == 1,
        entry["field strength name"] = entry["field name"],
        entry["field strength name"] = ""];
      DPModelAboveEW[k] = entry;], {k, Keys[DPModelAboveEW]}];


(* ::Subsection:: *)
(*Gravitino model*)


ClearAll@GravitinoModelAboveEW;
GravitinoModelAboveEW = <||>;
GravitinoModelAboveEW = KeyDrop[DPModelAboveEW,"DP"];
GravitinoModelAboveEW["Gn"] = <|"spin" -> 3/2, "mass" -> 1, "U1Y" -> 0, "SU2" -> "", "SU3" -> "", "field name" -> "\\psi"|>;
GravitinoModelAboveEW["Gnbar"] = <|"spin" -> 3/2, "mass" -> 1, "U1Y" -> 0, "SU2" -> "", "SU3" -> "", "field name" -> "\\psi"|>;
Do[Module[{entry = GravitinoModelAboveEW[k]}, entry["antiparticle"] = StringEndsQ[k, "bar"];
      GravitinoModelAboveEW[k] = entry;], {k, Keys[GravitinoModelAboveEW]}];
Do[Module[{entry = GravitinoModelAboveEW[k]},
      If[Abs@GravitinoModelAboveEW[k]["spin"] == 1,
        entry["field strength name"] = entry["field name"],
        entry["field strength name"] = ""];
      GravitinoModelAboveEW[k] = entry;], {k, Keys[GravitinoModelAboveEW]}];

(* ::Section:: *)
(*Model Tool fun*)


ClearAll[CheckModelVaild,CheckModelConfigVaild,GetConfigFromModel];
CheckModelVaild[model_Association][particles_List]:=CheckModelConfigVaild[GetConfigFromModel[model][particles,0],False];
CheckModelConfigVaild[config_List,print_:True]:=Module[{testspin,testmass,testSU2,testSU3,testU1,testAP},
  testU1=(Total[config[[3]]]==0);
  If[print&&!testU1,Print["Test Failed: U1",config[[3]]]]; 
  (*fermion == anti-fermion*)
  testAP=(Count[config[[1]][[1]],n_/;OddQ[2 n]]-2 Length[config[[4]]])==0;
  If[print&&!testAP,Print["Test Failed: fermion should be equal to anti-fermion",config[[4]]]];
  testspin=EvenQ[2 Total[config[[1]][[1]]]];
  If[print&&!testspin,Print["Test Failed: testspin",config[[1]][[1]]]];
  testmass=Count[MassOption[config[[2]],Length[config[[1]][[1]]]],a_/;a!=0]>0;
  If[print&&!testmass,Print["Test Failed: testmass"]];
  testSU2=EvenQ[Total[config[[1]][[3]]/. {"":>0,"1":>1,"2":>2}]];
  If[print&&!testSU2,Print["Test Failed: testSU2",config[[1]][[3]]]];
  testSU3=Total[config[[1]][[4]]/. {""->0,"q":>1,"aq":>2,"g":>3}];
  testSU3=Mod[testSU3,3]==0;
  If[print&&!Mod[testSU3,3]==0,Print["Test Failed: testSU3",config[[1]][[4]]]];
  And@@{testspin,testmass,testSU2,testSU3,testU1,testAP}]
GetConfigFromModel[model_Association][particles_List,opDim_Integer]:=Module[{spins,su2s,su3s,identical,masses,u1charge,antiparticles},
If[!And@@Table[KeyExistsQ[p][model],{p,particles}],Abort[]];
spins=Table[model[p]["spin"],{p,particles}];
su2s=Table[model[p]["SU2"],{p,particles}];
su3s=Table[model[p]["SU3"],{p,particles}];
u1charge=Table[model[p]["U1Y"],{p,particles}];
masses=MassOption[Flatten[Position[Table[model[p]["mass"],{p,particles}],1]],Length[particles]];
identical=Select[GatherBy[Range[Length[particles]],particles[[#1]]&],Length[#1]>1&];
antiparticles=DeleteMissing[Table[If[model[particles[[i]]]["antiparticle"],i,Missing[]],{i,Length[particles]}]];
{{spins,opDim,su2s,su3s,identical},masses,u1charge,antiparticles}]


(* ::Subsection:: *)
(*AutoModelFun*)


ClearAll@AutoModelFun;
AutoModelFun[model_Association][particles_List,opDim_Integer]:=Module[{config=GetConfigFromModel[model][particles,opDim],
    spins,su2s,su3s,dop,identical,masses,np,testSU2,testSU3,
    externalDict,antiparticles,Warpper,
    reAmps,reOps,reTex
    },
   spins=config[[1]][[1]];
   np=Length@spins;
   If[np<4,Abort[]];
   If[!CheckModelConfigVaild[config],Print["config illegal"];Abort[];];
   dop=config[[1]][[2]];
   su2s=config[[1]][[3]];
   su3s=config[[1]][[4]];
   identical=config[[1]][[5]];
   masses=config[[2]];
   testSU2=Length[config[[1]][[3]]//DeleteCases[""]]>0;
   testSU3=Length[config[[1]][[4]]//DeleteCases[""]]>0;
   externalDict=Association[Table[i->If[model[particles[[i]]]["field strength name"]==="",{model[particles[[i]]]["field name"]},
        {model[particles[[i]]]["field name"],
         model[particles[[i]]]["field strength name"]}],{i,Length[particles]}]];
   antiparticles=DeleteMissing[Table[If[model[particles[[i]]]["antiparticle"],i,Missing[]],{i,Length[particles]}]];
   reAmps=ConstructGeneralBasis[spins,dop,identical,mass->masses,su2ShapeList->su2s,su3ShapeList->su3s];
   If[Length@reAmps==0,Return[{}];];
   reOps=Amp2WeylOp[np,mass->masses,su2ShapeList->su2s,su3ShapeList->su3s]/@reAmps;
   reTex=ExportWeylOp2Tex[#,externalFieldNamesDict->externalDict,antiFermionList->antiparticles]&/@reOps;
   Return[{reAmps,reOps,reTex}] ;
   ];
