# API Surface

## Public Entry Point

`ConstructProjectedSewingRelativeChiralBasis` is the only function intended for
ordinary package users.

```wl
ConstructProjectedSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  ampDim,
  identicalParam,
  opts
]
```

```wl
ConstructProjectedSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  rightMass,
  ampDim,
  identicalParam,
  opts
]
```

Inputs:

* `leftSpin`: spin of both heavy particles 1 and 2.
* `rightSpins`: spins of particles 3 through n.
* `rightMass`: optional list of massive right-side particle labels, such as
  `{3}` or `{3, 4}`.  If omitted, the current default is the first right-side
  particle.
* `ampDim`: amplitude dimension used in the paper convention.
* `identicalParam`: right-side identical groups such as `{{3, 4}}`.

Important options:

* `su3ShapeList`: SU(3) shape labels for all particles, for example
  `{"", "", "q", "aq"}`.
* `QReplacement`: default `{1, -2}`, meaning \(Q=p_1-p_2\).
* `ReplaceQInFinalSymbolForm`: default `True`.
* `ReturnProjectionData`: default `False`.
* `SewingDebug`: default `False`.

Default output:

```wl
<|
  relativeChiralOrder1 -> {basis1, basis2, ...},
  relativeChiralOrder2 -> {...}
|>
```

Detailed output with `ReturnProjectionData -> True`:

```wl
<|
  "BasisByRelativeChiralOrder" -> ...,
  "SectorResults" -> ...,
  "Spins" -> ...,
  "Mass" -> ...,
  "IdenticalTypeList" -> ...,
  "CandidateBlocks" -> ...,
  "PhysicalBlocks" -> ...,
  "SU3ShapeList" -> ...,
  "SU3IndexDictionaries" -> ...
|>
```

## Expert Inspection Functions

These are useful when checking intermediate physics or debugging a paper
example.  They are not promised to stay stable across major rewrites.

* `ConstructLeft3PointOpenBasis`: left heavy-heavy-current three-point blocks.
* `ConstructRightProjectedJResidualRecords`: right auxiliary residual blocks
  projected back to formal \(J\)-slots.
* `ConstructGeneralSewingAmplitudeRecords`: sewn records before final
  independent-basis selection.
* `CompareGeneralSewingToCFBlocks`: fixed-sector CF/sewing rank comparison.
* `ConstructSewingRelativeChiralBasis`: fixed-right-polarization relative
  chiral basis.

## Internal Functions

Functions that directly manipulate tableaux, reductions, permutation matrices,
or coefficient matrices are implementation details.  They may be exported by
the current package loader for historical reasons, but they should not be used
as stable public APIs.
