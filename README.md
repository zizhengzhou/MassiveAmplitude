# Sewing Method Code

This repository packages the current left-right sewing construction for
heavy-pair local amplitudes.  It is intended to be usable without the full
Overleaf manuscript tree.

## Main Entry Point

The public interface for ordinary users is:

```wl
ConstructProjectedSewingRelativeChiralBasis[
  leftSpin,
  rightSpins,
  ampDim,
  identicalParam,
  opts
]
```

or, with explicit right-side massive labels:

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

The function returns an association keyed by relative chiral order.  Without
color structures, each value is a list of symbolic Lorentz basis elements.  With
`su3ShapeList`, each value is a list of associations containing
`LorentzSymbolForm`, `SU3Basis`, `SU3IndexDictionary`, and `DirectProduct`.

Use `ReturnProjectionData -> True` when debugging or validating a sector.  It
returns the grouped basis plus sector records, CF/sewing ranks, Young operators,
SU3 index dictionaries, and J-block diagnostics.

## User Levels

Most users should only call `ConstructProjectedSewingRelativeChiralBasis`.

Expert users may inspect these supporting constructors:

* `ConstructLeft3PointOpenBasis`
* `ConstructRightProjectedJResidualRecords`
* `ConstructGeneralSewingAmplitudeRecords`
* `CompareGeneralSewingToCFBlocks`
* `ConstructSewingRelativeChiralBasis`

Lower-level permutation, reduction, and auxiliary construction functions are
implementation details.  They are not a stable public API.

## Quick Examples

Load the package from the repository root:

```wl
Get[FileNameJoin[{"src", "Package", "Kernel", "init.m"}]];
```

Four-point example without identical particles:

```wl
ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {}
]
```

Same Lorentz problem with right-side identical projection:

```wl
ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {{3, 4}}
]
```

Attach an SU(3) singlet structure:

```wl
ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1},
  {3},
  4,
  {},
  su3ShapeList -> {"", "", "q", "aq"}
]
```

Restrict right-side polarization sectors after identical-sector representative
selection and before Young projection:

```wl
ConstructProjectedSewingRelativeChiralBasis[
  1/2,
  {1, 1, 0},
  {3, 4},
  4,
  {{3, 4}},
  RightPolarizationFilter -> <|3 -> 2|>
]
```

## Current Method

For an \(n\)-point amplitude, the constructor uses this workflow:

1. Construct the left \(\ell+\ell+J\) three-point open-current block directly.
2. Construct the right block with two auxiliary massless particles plus the
   \(n-2\) physical right-side particles.
3. Choose the auxiliary spin sector from the angular and square \(J\)-slot
   counts required by the left block.
4. Translate auxiliary labels back to formal \(J\)-slots and keep nonzero
   records matching the required angular and square counts.
5. Sew all \(J\)-slots symmetrically.  The default
   `SewingContractionMode -> "Split"` keeps each symmetric contraction term as
   a separate record.
6. Reduce internal amp forms and compare the sewn span against the matching CF
   block.
7. Apply identical-particle Young projection on right-side identical groups.
8. Optionally attach SU(3) structures by Lorentz/color direct product.
9. Select independent representatives with `FindIndependentBasisPos`.
10. Group final symbolic results by relative chiral order.

## Documentation

* `docs/api.md`: public and expert API surface.
* `docs/physics-conventions.md`: spinor, mass, Q, X, identical, SU(3), and
  relative chiral-order conventions.
* `docs/testing.md`: maintained tests, note-generation scripts, and removed
  probes.
* `docs/release-checklist.md`: tasks before a public release.
* `docs/benchmark-and-cache-plan.md`: performance benchmark and caching plan.

## Verification

From the repository root, run:

```powershell
wolframscript -file tests\run_all.wls
```

This runs the maintained regression suite.  Development probes should not be
added to `tests/run_all.wls` unless they become stable regression tests.
