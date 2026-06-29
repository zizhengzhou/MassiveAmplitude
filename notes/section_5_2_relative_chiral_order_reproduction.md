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

The default contraction mode is now

```wl
SewingContractionMode -> "Split"
```

so one left/right sewing pair may produce several records, one for each
individual fully symmetric contraction term.  The old one-left-one-right
summed behavior is still available with

```wl
SewingContractionMode -> "Sum"
```

This is the same filtration logic as the table-level chiral-order comparison:
earlier relative order has priority, and higher-dimensional check rows only
enter when they add a genuinely new reduced direction.

## Left Three-Point Correction

The left three-point open-current constructor follows the paper formula

```wl
ab[1, J]^a sb[L1, J]^(m - a)
ab[2, J]^b sb[L2, J]^(m - b)
Xhard^(r - k) Xsoft^k
(ab[Q, J] sb[Q, J])^Max[J - N, 0]
```

with the full Cartesian enumeration

```wl
a = 0, ..., m
b = 0, ..., m
k = 0, ..., r
```

where \(N=2s\), \(m=\min(J,N)\), and \(r=N-m\).  There is no additional
balanced-angle filter.  For \(s=1/2,J=1\), this keeps all four open
structures.  The formal \(Q\)-raising factor appears only for \(J>N\), so
closed \(J=0\) `Xhard`/`Xsoft` rows do not acquire an extra
`ab[Q,J] sb[Q,J]` factor.

## Reproduced Ordering

The witness test gives the following relative-order blocks.

| relative order | split-term count | sources |
| --- | ---: | --- |
| 2 | 4 | two `ampDim=3,J=1` rows and two split `ampDim=4,J=2` terms |
| 3 | 6 | one open `ampDim=4,J=1` row, three split `ampDim=5,J=2` terms, and two split `ampDim=6,J=3` terms |
| 4 | 3 | one `ampDim=5,J=1` row and two split `ampDim=6,J=2` terms |

The key leading-order check is therefore exact:

```text
relative order 2: 4 split-term rows
  ampDim=3, J=1
  ampDim=3, J=1
  ampDim=4, J=2
  ampDim=4, J=2
```

The first relative-order-3 representative is the `ampDim=4,J=1` open row
made possible by the full Cartesian left three-point enumeration.

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
