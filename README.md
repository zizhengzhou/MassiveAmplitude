# Sewing Method Code

This repository isolates the current left-right sewing construction for
heavy-pair local amplitudes from the surrounding Overleaf manuscript project.

## Current Method

The working construction for an \(n\)-point amplitude is:

1. Construct the left \(\ell+\ell+J\) three-point open-current block directly.
2. Construct the right block with two auxiliary massless particles plus the
   \(n-2\) physical right-side particles.
3. Choose the auxiliary spin sector from the angular and square \(J\)-slot
   counts required by the left block.
4. Build the right auxiliary amplitudes with the CF-block-style SSYT machinery.
5. Translate the two auxiliary labels back to formal \(J\)-slots and keep only
   nonzero records matching the required angular and square counts.
6. Sew all \(J\)-slots symmetrically and expand the result into records.
7. Reduce the sewn records with the fixed priority order: lower \(J\), then
   higher `Xsoft`, then higher `Xhard`.
8. Validate spans against `ConstructIndepCFBlock` through rank equality.

## Layout

* `src/Package/Codes/Sewing.m`: current sewing implementation and public entry
  points.
* `src/Package/Codes/*.m`: minimal package dependencies copied from the old
  amplitude package.
* `tests/`: regression and data-generation scripts relevant to the sewing
  method.
* `notes/`: curated technical notes and proof-status notes.
* `logs/`: retained witness logs for the most important scans.
* `docs/`: local repository indexes and maintenance notes.

## Primary Entry Points

* `ConstructLeft3PointOpenBasis`
* `ConstructRightProjectedJResidualRecords`
* `SymmetricSewContract`
* `ConstructGeneralSewingAmplitudeRecords`
* `ConstructIndepSewingBlock`
* `CompareGeneralSewingToCFBlocks`

## Verification

From the repository root, run:

```powershell
wolframscript -file tests\package_smoke.wls
wolframscript -file tests\usage_audit.wls
```

The first script checks that the package loads from `src/Package` and that the
primary entry points are defined. The second script checks the public usage
strings and the message strings used by the current error paths.
