# Operator basis construction flow

Scope: this note describes the current executable construction path in
`Codes/MassiveAmplitude-Code/addingSinglet.m`. It focuses on how CF blocks are
used to build the heavy-soft amplitude basis, how chiral order is assigned and
propagated, and how the selected amplitudes are translated into operator/TeX
output.

## Entry points

There are two relevant interfaces.

| Layer | Function | Role |
| --- | --- | --- |
| amplitude basis | `ConstructHeavyBaryonPhysicalBasis` | Builds the heavy-soft amplitude basis at a requested internal amplitude dimension. |
| chiral/operator wrapper | `FromChiral2Amp` | Scans amplitude dimensions, assigns LO/NLO weight, and returns `{amp, preOp}` pairs. |
| user-facing wrapper | `GetOP` | Maps field names through `ChiralModel`, calls `FromChiral2Amp`, attaches gauge indices, and emits TeX. |

`GetOP[baryon, meson, "order" -> ...]` is the current collaborator-facing
entry point. It is not itself the basis constructor; it is a wrapper around the
heavy-soft amplitude constructor plus amp-to-operator conversion.

## Model parsing in `GetOP`

`GetOP` first reads each external field from `ChiralModel`.

For each input field it extracts:

1. spin,
2. mass status,
3. SU(3) representation,
4. printed field label,
5. optional post-amp filter heads.

It also constructs `idenlist` from repeated particle names via `PositionIndex`.
For example, two identical scalar octets in
`GetOP[{"Nbar","N"},{"s","s"},...]` produce `idenlist = {{3,4}}`.

After model parsing the data flow is:

`GetOP -> FromChiral2Amp -> FilterAmpOpPairsByModelHeads -> AssignGaugeIndices -> OpToTeX`.

## Heavy-soft amplitude basis

The bottom-level constructor is
`ConstructHeavyBaryonPhysicalBasis[spinsBaryon, spinsMeson, ampDimParm,
identicalParam, opts]`.

It first validates the input:

1. there must be exactly two heavy baryons;
2. baryon spins must be positive;
3. total particle number must be at least four;
4. identical groups cannot contain particles 1 or 2;
5. particles in each identical group must have the same spin and mass status.

Then it sets:

`codeDim = ampDimParm + totalParticles`.

This is important. The public `ampDimParm` is not passed directly to
`ConstructIndepCFBlock`; the CF-block calls use the shifted internal dimension
`codeDim`.

The constructor then runs four stages.

## Stage 1: CF block foundation

`AuxConstructKinematicFoundation` builds the CF-block data needed for the
heavy-soft construction.

It first calls `GenerateSimpleCFBlocks[spinsTotal, ampDim]`. This enumerates
allowed polarization assignments for the full external state at the requested
internal dimension.

For each allowed polarization block, the code considers extracting momentum
factors from the two heavy baryons:

| Symbol | Meaning in the code |
| --- | --- |
| `k` | number of soft extractions from the first heavy baryon side |
| `m` | number of hard extractions from the second heavy baryon side |
| `remainSpins` | effective spins left after the heavy extraction |
| `remainPolars` | effective polarizations left after the heavy extraction |
| `remainDim` | remaining dimension sent to the reduced CF block |

For every valid `{k,m}`, the remaining light/reduced problem is stored as a
`subSystemKey = {Join[remainSpins, spinsMeson], remainDim,
Join[remainPolars, mesonPolars]}`.

Two kinds of CF block are cached:

1. the original full block
   `ConstructIndepCFBlock[spinsTotal, ampDim, fullPolarization]`;
2. each reduced subsystem block
   `ConstructIndepCFBlock[remainSpinsWithMesons, remainDim,
   remainPolarizationWithMesons]`.

The third component of each full CF block is collected into
`globalFundamentalBasis`. This is the common massless amplitude space used later
for global linear reduction.

Physical meaning: Stage 1 enumerates all possible ways to peel off hard/soft
heavy factors and records which reduced CF blocks can supply the remaining
spinor structure.

## Stage 2: Global heavy-soft reduction

`AuxGlobalKinematicReduction` converts the Stage 1 reduced CF data into
symbolic heavy-soft amplitudes.

For a reduced CF basis element `currentBasisA` and extraction pair `{k,m}`, it
sets:

`totalExtract = k + m`.

The symbolic heavy-soft candidate is:

`Xsoft^i Xhard^(totalExtract-i) currentBasisA`.

Here:

| Dummy | Meaning |
| --- | --- |
| `Xhard` | hard heavy-pair factor, later mapped to `M0` |
| `Xsoft` | soft/recoil factor, later mapped to `p0` |

To test linear independence, the code embeds every candidate into the same
massless global CF basis. It substitutes the dummy heavy factors by

`GetMixedMonomialX[totalParticles]` and `GetMixedMonomialY[totalParticles]`,

expands `(x+y)^i (x-y)^mPowerOrder`, reduces the resulting spinor monomials by
`ReduceSt[totalParticles]`, and expresses the result on
`globalFundamentalBasis`.

The candidates are sorted before pivot selection:

`SortBy[globalStatePool, {-priority_j, -priority_i}]`.

In the current code:

1. `priority_j` is the hard-power order;
2. `priority_i` is the soft-power order;
3. larger hard power is preferred first;
4. larger soft power is then preferred.

`FindIndependentBasisPos` is then applied to a single projection matrix for the
whole candidate pool. This is the key global-reduction step. It is not a
sector-wise local minimization.

The output of this stage is:

1. `reducedAmps`, a list of independent symbolic amplitudes containing
   `Xhard` and `Xsoft`;
2. `dummyToReducedCache`, used later to reconstruct permutation operators.

## Stage 3: Dispatch back to local CF blocks

`AuxDispatchDummyBlocks` replaces the symbolic dummies by concrete spinor
monomials:

`Xsoft -> GetMixedMonomialX[totalParticles]`,

`Xhard -> GetMixedMonomialY[totalParticles]`.

It then reads the local polarization data using `Amp2MetaInfo` and groups the
dummy amplitudes by polarization block. It also stores a reverse map:

`dummyToSymbolicAssoc[dummyAmp] = symbolicAmp`.

This lets Stage 4 apply identical-particle and SU(3) projectors in the concrete
local CF-block space, and then restore the selected result back to the symbolic
`Xhard/Xsoft` amplitude.

## Stage 4: Identical particles and SU(3)

`ConstructHeavyBaryonPhysicalBasis` converts the user input
`identicalParam = {{...}}` into an internal list with symmetry type:

`{..., "S"}` for integer-spin identical particles,

`{..., "A"}` for half-integer-spin identical particles.

If `su3ShapeList` is supplied, `ConstructSU3TrCached` builds the SU(3) trace
basis and the SU(3) permutation matrices. The current `ConstructSU3Tr` also
handles singlets by multiplying trace basis elements by `TrS[position]`.

`AuxKroneckerFilteringAndRestore` then combines the kinematic and SU(3) spaces:

1. it gets the local CF fundamental basis for the polarization block;
2. it expresses the reduced dummy amplitudes on that local basis using
   `CoeffsOnBasis`;
3. it gets the kinematic permutation matrices from
   `GetCFBlockPermuteOperatorDict`;
4. if SU(3) is present, it tensors SU(3) and kinematic bases using
   `AttachHeavySUNBlocks`;
5. it constructs the identical-particle Young/projector operator;
6. it finds independent rows of that projector;
7. it restores the selected dummy amplitudes back to symbolic `Xhard/Xsoft`
   amplitudes.

Known caveat: in `addingSinglet.m`, the identical-particle projector is formed
by directly replacing group-algebra generators with matrices. This is fragile
for three or more identical particles because scalar `1` must represent an
identity matrix and products of generators must represent matrix products. A
newer collaborator file appears to move in the right direction by introducing a
group-polynomial-to-matrix converter, but the full three-identical SU(3) route
still needs separate verification.

## Chiral order propagation

The chiral/order logic is not inside
`ConstructHeavyBaryonPhysicalBasis`. That constructor only returns a basis at a
requested internal amplitude dimension.

The order logic is in `FromChiral2Amp`.

First it sets a scan start:

`codeAmp = Total[spinsMeson] + Total[spinsBaryon]`.

Then it calls `ChPTexprFindDIM1`, which scans from `codeAmp` upward until the
first nonempty heavy-soft basis is found. This first nonempty dimension is
called `dim1`.

After `dim1` is found, the code scans:

`dims = Range[dim1, dim1 + MaxAmpDimensionShift]`.

For each dimension it calls `ChPTexprConstructBasis`, which calls
`ConstructHeavyBaryonPhysicalBasis`.

Each returned basis item is passed to `ChPTexprAmpOpRow`.

## Row data and current chiral weight

`ChPTexprAmpOpRow` records one row as:

| Field | Meaning |
| --- | --- |
| `Color` | SU(3)/singlet trace factor, or `1` if absent |
| `RawAmp` | symbolic heavy-soft amp with `Xhard/Xsoft` |
| `AmpForOp` | amp after `Xhard -> M0`, `Xsoft -> p0` |
| `PreOp` | operator expression from `AmpXYT2Op` |
| `Weight` | current chiral-order selector |
| `Pair` | `{{color, AmpForOp}, {color, PreOp}}` |

The current weight is:

`Weight = Exponent[RawAmp, Xsoft] + Count[PreOp, Df[i] /; i > nb]`.

So the implemented LO/NLO selector is:

| Method | Target weight |
| --- | ---: |
| `"LO"` | 0 |
| `"NLO"` | 1 |

This means the current code treats chiral order as a soft/recoil/source
derivative weight. It is not a direct count of the full operator mass
dimension. In particular:

1. `Xhard` power does not increase this `Weight`;
2. derivatives on baryon fields are not counted by the meson/source derivative
   counter;
3. higher internal amplitude dimensions can still contribute to NLO if their
   translated `PreOp` has `Weight == 1`.

This is why examples can contain NLO rows coming from dimensions above
`dim1 + 1`.

## Amp to operator

After weight selection, `FromChiral2Amp` returns only

`#["Pair"] & /@ selectedRows`.

Then `GetOP` filters, gauges, and formats the result:

1. `FilterAmpOpPairsByModelHeads` drops pairs whose post-amp operator contains
   a head forbidden by the external field model. For example, some field
   entries can say `DropHeadsAfterAmp -> {Ff}`.
2. `ampFiltered = pairFiltered[[All,1]]`.
3. `preOpFiltered = pairFiltered[[All,2]]`.
4. `AssignGaugeIndices` attaches SU(3) indices using `RepIndices =
   GetRepIndices[su3List]`.
5. `OpToTeX` converts `{color, operator}` terms into printed TeX strings.

For spin-1/2 heavy baryons, `AmpXYT2Op` dispatches to `Transfer[1]`. This
translates `M0` and `p0` factors into baryon bilinears and translates the
remaining spinor monomial through the old `Amp2MonoOp` machinery.

For spin-3/2 sectors, `AmpXYT2Op` dispatches to `Transfer[2]` or `Transfer[3]`,
which add projector-specific handling. These branches are not validated by the
simple `Nbar N` examples.

## What is currently aligned with the paper

The amplitude-basis construction follows the main advertised structure:

1. separate possible heavy hard/soft factors;
2. build reduced CF blocks for the remaining soft part;
3. embed all candidates into one common global basis;
4. perform a global ordered reduction;
5. restore the surviving representatives;
6. apply SU(3) and identical-particle constraints;
7. translate selected amplitudes to operators.

The important aligned point is the global row reduction in Stage 2. The code
does not select independently within each local extraction sector; it forms one
candidate pool and selects pivots after embedding into the same global CF basis.

## Boundary relative to the paper

The main mismatch risk is the meaning of "chiral order".

The paper language says chiral order is equivalent to mass dimension. The
current `addingSinglet.m` wrapper uses a narrower practical selector:

`Xsoft power + number of light/source derivatives appearing in PreOp`.

This may be the intended heavy-baryon counting after hard-factor separation,
but it should be stated that way. If the manuscript claims full mass-dimension
counting without qualification, the current implementation is not a literal
implementation of that statement.

Recommended wording for internal use:

The amplitude basis is constructed globally after heavy hard/soft factor
separation. The current LO/NLO operator wrapper then filters this basis by the
implemented soft/recoil chiral weight, where `Xsoft` powers and derivatives on
non-baryon fields count, while `Xhard` is treated as part of the heavy factor.
