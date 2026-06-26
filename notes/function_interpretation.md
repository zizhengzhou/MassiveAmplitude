# Function Interpretation: Heavy-Soft Factorization Audit

This note documents the first executable audit pass for
`ConstructHeavyBaryonPhysicalBasis`.  The original notebook-export file is
archived as `note/SoftHeavyFactorization.notebook-export.original.m`.  Because
`SoftHeavyFactorization.m` is currently locked by another Wolfram process, the
audited executable source is `SoftHeavyFactorization.executable.m`.

## Entry Point

`ConstructHeavyBaryonPhysicalBasis[spinsBaryon, spinsMeson, ampDim,
identicalParam, opts]` constructs a physical heavy-baryon basis from a fixed
heavy pair and light external content.

Inputs:

- `spinsBaryon`: exactly two positive integer or half-integer spins for legs 1
  and 2.
- `spinsMeson`: spins for the remaining light legs.
- `ampDim`: amplitude dimension parameter used by the manuscript examples.
- `identicalParam`: identical light-particle groups such as `{{3, 4}}`.
- `mass`: old-package mass specification; legs 1 and 2 must be massive.
- `su3ShapeList`: triggers the first-round mock SU(3) backend when nonempty.
- `AuditLogDirectory`, `AuditRunID`, `AuditVerbose`: non-destructive audit
  options.  Logging is disabled by default.

Output:

- `finalBasis` when no SU(3) occupancy is present.
- `{su3IndexOccupancy, finalBasis}` when the mock SU(3) backend returns a
  nonempty occupancy.
- `{}` for validation failure or an empty constructed space.

## Pipeline

1. Boundary validation.
   The function checks heavy-pair length, positive heavy spins, total particle
   count, spin integrality, nonnegative dimension, identical-particle format,
   identical spin/mass status, and massive heavy legs.

2. `AuxConstructKinematicFoundation`.
   This scans simple CF blocks, enumerates soft/hard extraction pairs `{k, m}`,
   constructs subsystem keys, calls the old `ConstructIndepCFBlock`, and builds
   one common `globalFundamentalBasis`.  The audit log records every extraction
   candidate and the final subsystem/global-basis sizes.

3. `AuxGlobalKinematicReduction`.
   This is the main global-filtration step.  It expands each extracted
   structure into the common basis, sorts by descending `Xhard` power and then
   descending `Xsoft` power, builds one projection matrix, and keeps the pivot
   rows selected by `FindIndependentBasisPos`.  This is the code-level
   implementation of global ordered reduction rather than sector-wise
   minimization.

4. `AuxDispatchDummyBlocks`.
   This substitutes `Xsoft` and `Xhard` by spinor monomials, asks
   `Amp2MetaInfo` for the local polarization block, and groups the surviving
   dummy amplitudes by polarization.

5. `AuxKroneckerFilteringAndRestore`.
   This computes kinematic permutation operators, optionally tensor-products
   them with the first-round mock SU(3) operators, applies the identical-particle
   Young operator, selects independent rows, and restores symbolic
   `Xsoft`/`Xhard` amplitudes.

## Old-Package Dependencies

- `MassOption`: parses the old package mass option into a per-particle mass
  list.
- `ConstructIndepCFBlock`: generates a local CF block, reduces it in the
  massless limit, and returns `{independentBasis, coefficientRows, basis}`.
- `ReduceSt`: applies Schouten and momentum-conservation reduction rules.
- `ReplaceBraNumber`: remaps spinor labels inside `ab`/`sb`.
- `FindIndependentBasisPos`: selects pivot row positions by row reduction.
- `Amp2MetaInfo`: extracts spin and anti-spinor metadata from a monomial.
- `GetCFBlockPermuteOperatorDict`: builds identical-particle permutation
  matrices for a CF block.
- `GetTotalPermutedPolyDict`: builds Young symmetrizer polynomials.
- `ReAssignIdentical`: refines identical-particle groups after polarization
  splitting.

## Audit Logs

When `AuditLogDirectory -> "logs"` is supplied, a run directory is created under
`logs/<run-id>/` and the following files are written:

- `run_summary.json`
- `stage1_kinematic_foundation.jsonl`
- `stage2_global_reduction.jsonl`
- `stage3_dispatch.jsonl`
- `stage4_identical_filter_mock_su3.jsonl`
- `final_basis.jsonl`

The stage-2 log is the highest-priority audit artifact because it records the
candidate ids, priority powers, projection matrix dimensions, pivot positions,
and the statement that all candidates are reduced in the same global basis.

## Current Risks

- `SoftHeavyFactorization.m` itself is still the locked notebook export; use
  `SoftHeavyFactorization.executable.m` until the lock is released.
- The SU(3) backend is deliberately a mock.  It validates plumbing and
  identical-particle filtering, not real flavor-trace physics.
- `SupplementMaterial.tex` still describes a `GetOP[...]` interface that is not
  implemented by this audit entry point.
- The first-round tests cover small examples and LO anchors.  They do not prove
  the full NLO/NNLO catalogue.
