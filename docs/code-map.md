# Code Map

## Core Sewing Layer

* `src/Package/Codes/Sewing.m`

This file owns the new method.  The main public entry point is
`ConstructProjectedSewingRelativeChiralBasis`.  Supporting functions construct
left open-current records, right auxiliary records, projected formal-\(J\)
residual records, symmetric sewing records, priority sorting metadata,
independence extraction, CF comparison, identical projection, and SU(3) direct
products.

## Minimal Dependencies

* `src/Package/Codes/Amplitude.m`

Provides `ConstructAmp`, `CheckAmpConstruction`, `InnerConstructAmp`,
`MassOption`, and `ReduceSt`.

* `src/Package/Codes/CFblocks.m`

Provides `ConstructIndepCFBlock`, the independent CF reference used for rank
comparison.

* `src/Package/Codes/Operator.m`

Provides `Amp2MetaInfo`, used to check the spin and polarization sector of
sewn amplitudes.

* `src/Package/Codes/Permutation.m`

Provides `ReplaceBraNumber` and permutation utilities needed by reduction and
legacy CF logic.

* `src/Package/Codes/SU3.m`

Provides the legacy SU(3) color-basis and identical-permutation constructor
used by `ConstructProjectedSewingRelativeChiralBasis`.

* `src/Package/Codes/SSYT.m`

Provides `StrangeSSYT` and `YTtoAmpmass`, the SSYT-to-amplitude layer used by
the auxiliary right construction.

* `src/Package/Codes/Tools.m`

Provides `Sum2List`, `Prod2List`, and `FindIndependentBasisPos`.

* `src/Package/Codes/Cache.m`

Provides cache infrastructure used by the package loader.

## Package Loader

* `src/Package/Kernel/init.m`
* `src/Package/MassiveBasis.m`

These preserve the package-style loading path from the old codebase.  They may
need path cleanup as the new repository becomes independent.
