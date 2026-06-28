# Subagent Summary: Old Package Dependencies

## Prompt

Read `Codes/MassiveAmplitude-Code/Package` only.  Summarize the initialization
chain, locate the old functions used by `SoftHeavyFactorization`, and identify
runtime risks.

## Summary

- `Package/Kernel/init.m` sets `$DEBUG = True`, computes `$MassiveDir`, gathers
  `Package/Codes/*.m`, and loads `MassiveBasis.m`.
- In debug mode the old package definitions land in the current/global context
  instead of a clean package-private context.
- `MassiveBasis.m` imports `Model/default.json`, clears cache, and wraps several
  old functions with the cache layer.
- Direct dependencies include `MassOption`, `ConstructIndepCFBlock`, `ReduceSt`,
  `ReplaceBraNumber`, `FindIndependentBasisPos`, `Amp2MetaInfo`,
  `GetCFBlockPermuteOperatorDict`, `GetTotalPermutedPolyDict`, and
  `ReAssignIdentical`.
- The old package does not provide an active `ConstructSU3Tr`; the real color
  constructor is closer to `AuxConstructIdenticalColorBasis` and uses different
  shape labels.

## Main-Agent Use

The first audit round therefore keeps SU(3) as a structural mock and focuses on
the heavy-soft kinematic pipeline.  The test runner loads `Package/Kernel/init.m`
before loading `SoftHeavyFactorization.executable.m` and calls `ClearCache[]`
between repeated pipeline runs.
