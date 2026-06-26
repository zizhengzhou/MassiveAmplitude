(* Wolfram Language Package *)

If[!Global`$DEBUG, BeginPackage["MassiveBasis`"];];
Print["Loading MassiveBasis..."];

{Amp2WeylOp, Amp2MetaInfo};
{DisplayYT, ExportAmp2Tex, ExportAmpMassive2Tex, ExportWeylOp2Tex, ExportTexList2Array};
{ConstructIndependentBasis, CalcPermutationMatrixDictByFakeDim};
{MassOption, ConstructAmp, CheckAmpConstruction, InnerConstructAmp, ReduceSt, ConstructCFIByFakeDim};
{ConstructIndepCFBlock, GenerateNeedCFBlocks, Poly2Singlet};
{ConstructLeft3PointOpenBasis};
{SewingRightResidualRecordsDirect, SewingRightResidualRecordsAuxiliary, CompareRightResidualBackends};
{SewingAuxiliaryAmpToFormalJ, SewingAuxiliaryAmpToFormalJCandidates};
{ConstructRightAuxiliaryOnShellRecords, CompareRightAuxiliaryOnShellToDirectJ};
{ConstructRightProjectedJResidualRecords};
{SewingContractionTerms, SymmetricSewContract};
{ConstructGeneralSewingAmplitudeRecords, ConstructIndepSewingBlock, CompareGeneralSewingToCFBlocks};
{SewingProjectAuxiliaryLabels, SewingNormalizeJTarget};
{SewingIndependentBlockFromRecords, SewingCoeffMatrixDataUnion};
{SewingSortData, SewingSortDataQ, SewingStaticXPower, SewingRelativeChiralOrder, SewingChiralSortKey, SewingSortRecordsByChiralOrder, SewingBasisSortKey, SewingSortRecordsForBasis};
{MassiveSpin};
{ab, sb};
{Sum2List, Prod2List, FindIndependentBasisPos, FindCoordinate};
{ReplaceBraNumber, YTtoAmpmass};
{ClearCache, CacheFunction};
{
  antispinor, mass, explicitmass, fund, tryMax, parallelized, minalParalledAmount,
  kernelAmount, log, withDict, externalReduceDict, synctask, synctime, maxntcount,
  timeDebug, su2ShapeList, su3ShapeList, antiFermionList, externalFieldNamesDict,
  env, param, option, prefix, suffix
};
{
  Labels, PhysicalLabels, SupplementLabels, JLabel, SplitColumns,
  AuxiliaryLabels, AuxiliarySpinRange, EqualAuxiliarySpin, RightAntispinor,
  Target, CodeDim, RejectMasslessSelfColumns, ReturnRejected, RejectZeroProjection,
  RightSpins, MassiveSpin, PointCount, QReplacement, MasslessRule, EOMRules,
  RightMass, LeftMass, JRange, JMax, SewingContractionMode, VerifyAmpDim, Check3Point, CheckRight,
  CheckSewing, CheckVerbose, FilterPhysicalSector, FilterByAmpDim,
  DeduplicateByReducedAmp, LeftPolarizationRange, CFPolarizations,
  FilterSewingByCFPolarization, CheckAgainstCF, SewingDebug
};
{$MassiveVerbose, $SewingDebug, SewingLog};

If[!BooleanQ[$MassiveVerbose], $MassiveVerbose = False;];
LogPri[mess___] := If[$MassiveVerbose, Print[mess]];
If[!BooleanQ[$SewingDebug], $SewingDebug = False;];
SewingLog::usage =
  "SewingLog[enabled, tag, data...] prints a tagged diagnostic line when enabled is True or when the global $SewingDebug flag is True. It is used by sewing constructors and is silent by default.";
SewingDebug::usage =
  "SewingDebug is an option for selected sewing constructors. SewingDebug -> True prints local diagnostic progress messages; the default is False.";
$SewingDebug::usage =
  "$SewingDebug is a global default-off switch for sewing diagnostics. Set it to True only for interactive debugging.";
SewingLog[enabled_, tag_, data___] := If[TrueQ[enabled] || TrueQ[$SewingDebug],
  Print["[Sewing:", tag, "] ", data]
];
ConstructIndependentBasis::usage =
  "ConstructIndependentBasis[spins, physicalDim, identical, opts] constructs the legacy independent CF basis after fake-dimension construction and identical-particle projection.";
CalcPermutationMatrixDictByFakeDim::usage =
  "CalcPermutationMatrixDictByFakeDim[result, identicalList, opts] computes permutation operators on fake-dimension CF data and separates them by physical dimension.";
Amp2MetaInfo::usage =
  "Amp2MetaInfo[amp, n, opts] extracts {spins, antispinorPolarization} metadata from an n-point spinor-helicity monomial. The mass option controls massive labels.";
Amp2WeylOp::usage =
  "Amp2WeylOp[n, opts][amp] translates a spinor-helicity monomial, optionally with gauge tableaux, to the package Weyl-operator chain representation.";
ReplaceBraNumber::usage =
  "ReplaceBraNumber[rules][expr] relabels spinor bracket labels in expr. ReplaceBraNumber[expr, rules] is the direct form.";
YTtoAmpmass::usage =
  "YTtoAmpmass[tableau, split, particleList, opts] converts an SSYT filling to a massive spinor-helicity monomial.";
DisplayYT::usage =
  "DisplayYT[yt] displays a Young-tableau-like list or IYT expression as a framed Grid.";
ExportAmp2Tex::usage =
  "ExportAmp2Tex[amp] exports a spinor-helicity amplitude to a compact TeX string. Custom angle and square bracket formatters may be supplied.";
ExportAmpMassive2Tex::usage =
  "ExportAmpMassive2Tex[n][amp] exports an n-point massive amplitude after relabeling conjugate massive spinors with primed labels.";
ExportWeylOp2Tex::usage =
  "ExportWeylOp2Tex[weylChain, opts] exports a Weyl-operator chain to TeX.";
ExportTexList2Array::usage =
  "ExportTexList2Array[list, opts] formats a list of TeX strings as a TeX array-like environment.";
ClearCache::usage =
  "ClearCache[] restores all cached package functions to their uncached definitions. ClearCache[f] restores one cached function.";
CacheFunction::usage =
  "CacheFunction[f] memoizes calls to f while preserving a shifted backup definition. CacheFunction[{f1, ...}] applies it to a list.";
$MassiveVerbose::usage =
  "$MassiveVerbose controls package-loading and legacy diagnostic prints. It is False by default.";
antispinor::usage = "antispinor is an option specifying square-spinor polarizations for amplitude construction.";
mass::usage = "mass is an option specifying massive external labels or an explicit mass vector.";
explicitmass::usage = "explicitmass is a legacy reduction option controlling explicit mass handling.";
fund::usage = "fund is a legacy reduction option specifying the fundamental spinor label family.";
tryMax::usage = "tryMax is a legacy reduction option specifying the maximum number of reduction attempts.";
parallelized::usage = "parallelized is a legacy reduction option enabling parallel reduction.";
withDict::usage = "withDict is a legacy ReduceToBH option selecting dictionary-backed reduction.";
externalReduceDict::usage = "externalReduceDict is a legacy option supplying an external reduction dictionary.";
maxntcount::usage = "maxntcount is a legacy reduction option limiting split-column trials.";
minalParalledAmount::usage = "minalParalledAmount is a legacy option setting the minimum batch size for parallel work.";
kernelAmount::usage = "kernelAmount is a legacy option specifying the number of kernels for synchronized parallel work.";
synctask::usage = "synctask is a legacy option controlling synchronized task batch size.";
synctime::usage = "synctime is a legacy option controlling synchronized task polling time.";
timeDebug::usage = "timeDebug is a legacy option enabling local timing prints in selected CF-block routines.";
log::usage = "log is a legacy option enabling progress output in selected legacy routines.";
su2ShapeList::usage = "su2ShapeList is an option specifying SU(2) gauge tableau shapes for each particle.";
su3ShapeList::usage = "su3ShapeList is an option specifying SU(3) gauge tableau shapes for each particle.";
antiFermionList::usage = "antiFermionList is an option specifying fermion positions to export as daggered antifermion fields.";
externalFieldNamesDict::usage = "externalFieldNamesDict is an option specifying custom TeX names for external fields.";
env::usage = "env is an option specifying the TeX environment name used by ExportTexList2Array.";
param::usage = "param is an option specifying the TeX environment argument used by ExportTexList2Array.";
option::usage = "option is an option specifying an optional TeX environment argument used by ExportTexList2Array.";
prefix::usage = "prefix is an option specifying the prefix inserted before each TeX array row.";
suffix::usage = "suffix is an option specifying the suffix inserted after each TeX array row.";
MassiveSpin::usage = "MassiveSpin is an option specifying the equal heavy-pair spin used by the left three-point current constructor.";
PointCount::usage = "PointCount is an option specifying the full physical point count used for massive-label relabeling and reduction.";
QReplacement::usage = "QReplacement is an option controlling how the left-current Q label is replaced before sewing.";
Labels::usage = "Labels is an option specifying the ordered label set used by residual SSYT enumeration.";
PhysicalLabels::usage = "PhysicalLabels is an option specifying physical right-side labels in residual enumeration.";
SupplementLabels::usage = "SupplementLabels is an option specifying supplemental labels used before projection to J.";
JLabel::usage = "JLabel is an option specifying the formal current label, usually J.";
SplitColumns::usage = "SplitColumns is an option specifying allowed angle-square column splits in residual tableaux.";
AuxiliaryLabels::usage = "AuxiliaryLabels is an option specifying the two massless auxiliary labels used on the right side.";
AuxiliarySpinRange::usage = "AuxiliarySpinRange is an option specifying allowed auxiliary-spin values or Automatic for the constructor default.";
EqualAuxiliarySpin::usage = "EqualAuxiliarySpin is an option requiring the two auxiliary particles to carry equal spin.";
RightAntispinor::usage = "RightAntispinor is an option specifying the physical right-side antispinor polarization list.";
Target::usage = "Target is an option specifying required angle and square label counts for residual filtering.";
CodeDim::usage = "CodeDim is an option overriding the package code dimension used in auxiliary amplitude construction.";
RejectMasslessSelfColumns::usage = "RejectMasslessSelfColumns is an option dropping auxiliary amplitudes with massless self-column factors.";
ReturnRejected::usage = "ReturnRejected is an option returning rejected projected-right records together with accepted records.";
RejectZeroProjection::usage = "RejectZeroProjection is an option dropping records whose auxiliary projection to J vanishes.";
RightSpins::usage = "RightSpins is an option specifying physical right-side spins for backend comparison helpers.";
RightMass::usage = "RightMass is an option specifying the physical or auxiliary-construction mass convention for the right side.";
LeftMass::usage = "LeftMass is an option specifying the two left heavy labels or mass vector.";
JRange::usage = "JRange is an option specifying explicit left-current J values to scan.";
JMax::usage = "JMax is an option specifying the maximum left-current J when JRange is Automatic.";
SewingContractionMode::usage = "SewingContractionMode is an option for sewn-record construction. Use \"Split\" to keep individual symmetric contraction terms as separate records, or \"Sum\" to combine them into one record per left/right pair.";
VerifyAmpDim::usage = "VerifyAmpDim is an option enabling sewn-amplitude bracket-dimension checks.";
Check3Point::usage = "Check3Point is an option enabling consistency checks for left three-point records.";
CheckRight::usage = "CheckRight is an option enabling consistency checks for projected right records.";
CheckSewing::usage = "CheckSewing is an option enabling final sewn-record consistency checks.";
CheckVerbose::usage = "CheckVerbose is an option enabling extra check-pass messages.";
FilterPhysicalSector::usage = "FilterPhysicalSector is an option dropping sewn records outside the requested spin and polarization sector.";
FilterByAmpDim::usage = "FilterByAmpDim is a reserved option for filtering records by amplitude dimension.";
DeduplicateByReducedAmp::usage = "DeduplicateByReducedAmp is an option deduplicating sewn records by reduced amplitude rather than construction provenance.";
MasslessRule::usage = "MasslessRule is an option specifying massive-to-massless relabeling rules used during reduction.";
EOMRules::usage = "EOMRules is an option specifying equations-of-motion replacement rules used during reduction.";
LeftPolarizationRange::usage = "LeftPolarizationRange is an option specifying left heavy-pair polarizations used for CF comparison.";
CFPolarizations::usage = "CFPolarizations is an option specifying full polarization sectors used in CF comparison.";
FilterSewingByCFPolarization::usage = "FilterSewingByCFPolarization is an option restricting sewn records to sectors visible in the CF comparison.";
CheckAgainstCF::usage = "CheckAgainstCF is an option causing ConstructIndepSewingBlock to validate sewn span rank against CF blocks.";

If[!Global`$DEBUG, Begin["`Private`"]];

Do[Get[file], {file, Global`$CodeFiles}];

If[!Global`$DEBUG, End[]];

$MassiveDefaultModelFile = FileNameJoin[{Global`$MassiveDir, "Model", "default.json"}];
If[ValueQ[ImportModel] && FileExistsQ[$MassiveDefaultModelFile],
  ImportModel[$MassiveDefaultModelFile]
];

(*Add cache*)
ClearCache[];
If[! ListQ@$MassiveCachedFunction,
  $MassiveCachedFunction = Select[
    {
    ConstructAmp,
    ConstructCFIByFakeDim,
    CalcPermutationMatrixDictByFakeDim,
    ConstructIndependentBasis,
    AuxConstructIdenticalColorBasis},
    MatchQ[OwnValues[#] ~ Join ~ DownValues[#] ~ Join ~ SubValues[#], Except[{}]] &
  ];
];
CacheFunction[$MassiveCachedFunction];

If[!Global`$DEBUG, EndPackage[]];

Print["Loaded MassiveBasis"];
