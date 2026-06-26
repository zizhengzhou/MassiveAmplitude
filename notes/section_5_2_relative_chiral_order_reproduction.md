<!-- markdownlint-disable MD013 MD052 -->

# Section 5.2 Relative Chiral-Order Reproduction

This note records the successful executable reproduction of the relative
chiral-order ordering for the \((\bar B,B,u,f_+)=(1,2,3,4)\) sewing example.
It supersedes the older `d_amp - n_x` bookkeeping for this code path.

## Sector

The reproduced point is

```wl
CompareGeneralSewingToCFBlocks[
  1/2, {1, 1}, {3}, d, {1, 0},
  JMax -> 4,
  QReplacement -> 2
]
```

with \(d=d_{\rm amp}=3,4,5,6\).  The sector has one spin-\(1/2\) heavy pair,
a massive spin-one \(u_\mu\) leg at position 3, and a positive-helicity
massless vector leg at position 4.

## Rule

The relative chiral-order label used by the current test is

```wl
RelativeOrder = AmpDim - XPower - J
```

where `XPower` is `SewingStaticXPower[rec]`.  In the present implementation
this directly reads the `Xhard` power stored in `SortData`.

The global table is not obtained by independently reducing each fixed
`ampDim` space first.  The tested procedure is:

1. collect all complete sewn records for `ampDim=3,4,5,6`;
2. sort them by `SewingChiralSortKey`;
3. add rows greedily only when the reduced coefficient rank increases.

This is the same filtration logic as the table-level chiral-order comparison:
earlier relative order has priority, and higher-dimensional check rows only
enter when they add a genuinely new reduced direction.

## Left Three-Point Correction

The successful run depends on a correction to the left three-point open-current
constructor.  For sectors without extra \(Q\)-raising factors, the open
left block must be balanced between angle and square open slots.  The helper
`SewingBalancedOpenPairQ` enforces

```wl
Angle1 + Angle2 == Square1 + Square2
```

before forming the left records when `qExponent == 0`.

This removes the over-broad pure square-square and pure angle-angle
\(J=1\) left structures.  In particular, `ampDim=4,J=1` records are absent
after this correction.  The valid leading `ampDim=4` open-current row is the
`J=2` row with one \(Q\)-raising component.

## Reproduced Ordering

The witness test gives the following relative-order blocks.

| relative order | count | sources |
| --- | ---: | --- |
| 2 | 3 | two `ampDim=3,J=1` rows and one `ampDim=4,J=2` row |
| 3 | 4 | one static `ampDim=4,J=0` row, two `ampDim=5,J=2` rows, and one `ampDim=6,J=3` row |
| 4 | 5 | one recoil `ampDim=4,J=0` row, two `ampDim=5,J=1` rows, and two `ampDim=6,J=2` rows |

The key leading-order check is therefore exact:

```text
relative order 2: 3 rows
  ampDim=3, J=1
  ampDim=3, J=1
  ampDim=4, J=2
```

No `ampDim=4,J=1` row appears in the constructed record list.

## Verification Commands

Run these commands from the `sewing-method-code` repository root:

```powershell
wolframscript -file tests\section_5_2_bbuf_reproduce.wls
wolframscript -file tests\section_5_2_chiral_order_reproduce.wls
wolframscript -file tests\package_smoke.wls
wolframscript -file tests\usage_audit.wls
git diff --check
```

The chiral-order witness script writes
`logs/section_5_2_relative_chiral_orders.log`.
