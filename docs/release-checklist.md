# Release Checklist

## API

* Keep `ConstructProjectedSewingRelativeChiralBasis` as the primary public
  function.
* Treat expert functions as inspection helpers, not stable user-facing APIs.
* Avoid exposing low-level reduction, permutation, and tableaux internals unless
  a real external use case appears.

## Documentation

* README has a load example and three minimal calls.
* `docs/api.md` describes input and output schemas.
* `docs/physics-conventions.md` records the conventions needed to interpret
  output.
* Usage strings mention required options and output keys.

## Verification

Before release, run:

```powershell
wolframscript -file tests\run_all.wls
```

Recommended additional checks:

* batch comparison against legacy `ConstructGeneralBasis` for nonzero examples;
* one identical-particle example;
* one SU(3) direct-product example;
* one 5-point example with a massive right-side particle;
* one higher-spin example, especially `LeftSpin -> 3/2`.

## Packaging

* Add a version number.
* Add a license.
* Add a changelog.
* Document supported Wolfram Language versions.
* Decide whether old `.wlt` tests should be converted to `.wls` or moved to a
  legacy test folder.
* Keep development probes out of the release package.

## Known Scope

The package supports the current paper method.  It is not intended to support
large alternative rewrites of the construction or arbitrary low-level internal
experiments as stable APIs.
