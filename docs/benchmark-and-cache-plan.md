# Benchmark And Cache Plan

## Benchmark Goals

The benchmark should answer three questions:

1. Which stages dominate runtime for realistic examples?
2. Which repeated calls benefit from in-memory caching?
3. Which rare but very expensive results deserve file-backed cache support?

## Proposed Benchmark Cases

Start with a small fixed table:

* `LeftSpin -> 1/2`, `RightSpins -> {1, 1}`, `RightMass -> {3}`,
  `AmpDim -> 5`.
* `LeftSpin -> 1/2`, `RightSpins -> {1, 1}`, `RightMass -> {3, 4}`,
  `AmpDim -> 6`.
* `LeftSpin -> 1`, `RightSpins -> {1, 1}`, `RightMass -> {3}`,
  `AmpDim -> 6`.
* `LeftSpin -> 3/2`, `RightSpins -> {1, 1}`, `RightMass -> {3}`,
  `AmpDim -> 5`.
* `LeftSpin -> 1/2`, `RightSpins -> {0, 0, 0}`, `RightMass -> {3}`,
  `AmpDim -> 5`.
* One SU(3) case with `su3ShapeList -> {"", "", "q", "aq"}`.
* One identical case with `identicalParam -> {{3, 4}}`.

For each case, record:

* total wall time;
* memory delta if available;
* number of full polarization sectors;
* number of nonzero CF sectors;
* number of right-polarization record builds;
* final basis count;
* relative chiral-order keys.

## Stage Timers

Add optional timers around:

* `GenerateNeedCFBlocks`;
* `ConstructIndepCFBlock`;
* `ConstructGeneralSewingAmplitudeRecords`;
* `ConstructRightProjectedJResidualRecords`;
* `SewingReducedMasslessGeneral`;
* `GetCFBlockPermuteOperatorDict`;
* `AuxConstructIdenticalColorBasis`;
* final `FindIndependentBasisPos`.

The timers should be off by default and integrated with `SewingDebug`.

## Cache Policy

Do not cache everything.  Cache only functions proven slow by benchmark data.

Recommended cache levels:

* local per-call association caches for repeated sectors inside
  `ConstructProjectedSewingRelativeChiralBasis`;
* optional package-level in-memory cache for slow pure computations;
* optional file-backed cache only for very expensive, stable, serializable
  results.

Candidate in-memory caches:

* `ConstructIndepCFBlock[spins, codeDim, fullPolarization, mass]`;
* `ConstructGeneralSewingAmplitudeRecords[...]`;
* `ConstructRightProjectedJResidualRecords[...]`;
* `SewingReducedMasslessGeneral[amp, PointCount -> np]`;
* `GetCFBlockPermuteOperatorDict[...]`;
* `AuxConstructIdenticalColorBasis[su3ShapeList, identicalInfo, IYT]`.

Candidate file-backed caches:

* large right auxiliary record tables;
* large CF blocks;
* expensive SU(3) color bases for fixed shape and identical data.

## Adaptive Cache Design

A useful general wrapper would be:

```wl
SewingCachedCall[key, expr, opts]
```

Behavior:

* evaluate `expr` normally the first time;
* measure elapsed time;
* store the result only if elapsed time exceeds a threshold;
* use an in-memory association by default;
* optionally write to a file-backed cache for keys marked stable.

Possible options:

* `CacheEnabled -> True`;
* `CacheThresholdSeconds -> 0.25`;
* `CacheBackend -> "Memory" | "File"`;
* `CacheDirectory -> Automatic`;
* `CacheKeyVersion -> "v1"`;
* `CacheDebug -> False`.

File-backed cache keys must include:

* package version;
* function name;
* normalized input;
* important options;
* Wolfram version if serialization is version-sensitive.

## Multi-Kernel Note

Do not try to synchronize all caches across kernels by default.  That adds
complexity and can hurt correctness.  Prefer:

* per-kernel memory caches for ordinary repeated calls;
* file-backed caches only for very slow stable objects;
* explicit cache invalidation through versioned keys.
