# Testing Layout

## Maintained Regression Suite

Run all maintained tests from the repository root:

```powershell
wolframscript -file tests\run_all.wls
```

The suite currently includes:

* package smoke and usage audits;
* symbolic/amp-form separation checks;
* left open-structure coverage checks;
* relative chiral-basis interface checks;
* projected sewing identical and SU(3) checks;
* Section 5.2 reproduction checks;
* split-vs-sum contraction count checks.

Only stable regression tests should be listed in `tests/run_all.wls`.

## Note Data Scripts

Some scripts generate data or logs for notes and are not part of the maintained
suite:

* `tests/sewing_bbuf_chiral_order_note_data.wls`
* `tests/sewing_bbuf_dims_3_5_note_data.wls`
* `tests/sewing_qsum_current_probe.wls`

These are retained because they support curated notes and logs.

## Legacy WLT Tests

The `.wlt` tests are retained from earlier package work.  They are useful smoke
tests but are not the release gate.  The release gate is `tests/run_all.wls`.

## Removed Development Probes

Temporary 5-point, broad-scan, and failure-diagnostic probes were removed from
the working tree because they were exploratory scripts rather than maintained
tests.  If a probe discovers a real bug, promote the minimal reproducer into a
small `.wls` regression script and add it to `run_all.wls`.
